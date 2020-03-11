/*!
Generate lexicographically-evenly-spaced strings between two strings
from pre-defined alphabets.

This is a rewrite of [mudderjs](https://github.com/fasiha/mudderjs); thanks
for the original work of the author and their contributors!

## Usage
Add a dependency in your Cargo.toml:

```toml
mudders = "0.0.1"
```

Now you can generate lexicographically-spaced strings in a few different ways:

```
use mudders::SymbolTable;

// You can use the included alphabet table
let table = SymbolTable::alphabet();
// SymbolTable::mudder() returns a Vec containing `amount` Strings.
let result = table.mudder("a", "z", 1);
// These strings are always lexicographically placed between `start` and `end`.
let one_string = result[0].as_str();
assert!(one_string > "a");
assert!(one_string < "z");

// You can also define your own symbol tables
let table = SymbolTable::from_chars(&['a', 'b']).unwrap();
let result = table.mudder("a", "b", 2);
assert_eq!(result.len(), 2);
assert!(result[0].as_str() > "a", result[1].as_str() > "a");
assert!(result[0].as_str() < "b", result[1].as_str() < "b");

// The strings *should* be evenly-spaced and as short as they can be.
let table = SymbolTable::alphabet();
let result = table.mudder("anhui", "azazel", 3);
assert_eq!(result.len(), 3);
assert_eq!(vec!["aq", "at", "aw"], result);
```

## Notes
The most notable difference to Mudder.js is that currently, mudders only
supports ASCII characters (because 127 characters ought to be enough for
everyone™). Our default `::alphabet()` also only has lowercase letters.

*/

use std::{convert::TryFrom, str::FromStr};

pub mod error;
use error::*;

/// The functionality of the crate lives here.
///
/// A symbol table is, internally, a vector of valid ASCII bytes that are used
/// to generate lexicographically evenly-spaced strings.
#[derive(Clone, Debug)]
pub struct SymbolTable(Vec<u8>);

impl SymbolTable {
    /// Creates a new symbol table from the given byte slice.
    /// The slice is internally sorted using `.sort()`.
    ///
    /// An error is returned if one of the given bytes is out of ASCII range.
    pub fn new(source: &[u8]) -> Result<Self, NonAsciiError> {
        if source.iter().any(|i| !i.is_ascii()) {
            return Err(NonAsciiError::NonAscii);
        }
        // Copy the values, we need to own them anyways...
        let mut vec: Vec<_> = source.iter().copied().collect();
        // Sort them so they're actually in order.
        // (You can pass in ['b', 'a'], but that's not usable internally I think.)
        vec.sort();
        Ok(Self(vec))
    }

    /// Creates a new symbol table from the given characters.
    /// The slice is internally sorted using `.sort()`.
    ///
    /// An error is returned if one of the given characters is not ASCII.
    pub fn from_chars(source: &[char]) -> Result<Self, NonAsciiError> {
        let inner: Box<[u8]> = source
            .iter()
            .map(|i| u8::try_from(*i as u32).map_err(NonAsciiError::from))
            .collect::<Result<_, _>>()?;
        Ok(Self::new(&inner)?)
    }

    /// Returns a SymbolTable which contains the lowercase latin alphabet (`[a-z]`).
    #[allow(clippy::char_lit_as_u8)]
    pub fn alphabet() -> Self {
        Self::new(&('a' as u8..='z' as u8).collect::<Box<[_]>>()).unwrap()
    }

    /// Generate `amount` strings that lexicographically sort between `start` and `end`.
    /// The algorithm will try to make them as evenly-spaced as possible.
    pub fn mudder(&self, start: &str, end: &str, amount: usize) -> Vec<String> {
        // Iterator version which doesn't handle different string lengths correctly.
        //let matching_count: Option<usize> =
        //    // Through all characters in start and end,
        //    start
        //        .chars()
        //        .zip(end.chars())
        //        // attach an index...
        //        .enumerate()
        //        // ...give me the first one where chars differ...
        //        .find(|(_, (c1, c2))| c1 != c2)
        //        // ...and return the index at which this happens.
        //        // The index logically comes *after* the last matching char,
        //        // so it's matching_index + 1, or the amount of matches.
        //        // If the index is 0, there are no common characters, so None.
        //        .and_then(|(index, _)| if index == 0 { None } else { Some(index) });

        // loop version
        let matching_count: usize = {
            // Iterate through the chars of both given inputs...
            let (mut start_chars, mut end_chars) = (start.chars(), end.chars());
            // Counting to get the index.
            let mut i: usize = 0;
            loop {
                // Advance the iterators...
                match (start_chars.next(), end_chars.next()) {
                    // As long as there's two characters that match, increment i.
                    (Some(sc), Some(ec)) if sc == ec => {
                        i += 1;
                        continue;
                    }
                    // break with i as soon as any mismatch happens or both iterators run out.
                    // matching_count will either be 0, indicating that there's
                    // no leading common pattern, or something other than 0, in
                    // that case it's the count of common characters.
                    (None, None) | (Some(_), None) | (None, Some(_)) | (Some(_), Some(_)) => {
                        break i
                    }
                }
            }
        };

        // Calculate the distance between the first non-matching characters.
        // If matching_count is greater than 0, we have leading common chars,
        // so we skip those, but add the amount to the depth base.
        let depth_base =
            self.distance_between_first_chars(&start[matching_count..], &end[matching_count..]);
        // We also add matching_count to the depth because if we're starting
        // with a common prefix, we have at least x leading characters that
        // will be the same for all substrings.
        let depth = dbg!(log(dbg!(depth_base), amount + 2)) + matching_count;

        // TODO: Maybe keeping this as an iterator would be more efficient,
        // but it would have to be cloned at least once to get the pool length.
        let pool: Vec<String> = dbg!(self.traverse("".into(), start, end, depth).collect());
        if amount == 1 {
            // return the middle element
            vec![pool[(pool.len() as f64 / 2.0f64).floor() as usize].clone()]
        } else {
            let step = (pool.len() / amount) - (depth);
            let mut pool = pool.into_iter();
            if dbg!(step) == 0 {
                // Skip the first one.
                // If we have a step of 0, this most likely means that we had an
                // extremely small pool (since depth was equal to pool.len() / 2).
                // In this case, it's hopefully safe to assume that we have `start`
                // as the first item in pool.
                pool.next();
            }
            // `amount` times...
            (1..=amount)
                // Take the value at `step`, advancing the iterator by `step`
                .map(|_| pool.nth(step).unwrap())
                // Return the results
                .collect()
        }
    }

    /// Traverses a virtual tree of strings to the given depth.
    fn traverse<'a>(
        &'a self,
        curr_key: String,
        start: &'a str,
        end: &'a str,
        depth: usize,
    ) -> Box<dyn Iterator<Item = String> + 'a> {
        if depth == 0 {
            Box::new(std::iter::empty())
        } else {
            // Generate all possible mutations on level
            Box::new(
                self.0
                    .iter()
                    .filter_map(move |c| -> Option<Box<dyn Iterator<Item = String>>> {
                        // TODO: Performance - this probably still isn't the best option.
                        let key = {
                            let the_char = *c as char;
                            let mut string =
                                String::with_capacity(curr_key.len() + the_char.len_utf8());
                            string.push_str(&curr_key);
                            string.push(the_char);
                            string
                        };

                        // After the end key, we definitely do not continue.
                        if key.as_str() > end && !end.is_empty() {
                            None
                        } else if key.as_str() < start {
                            // If we're prior to the start key...
                            // ...and the start key is a subkey of the current key...
                            if start.starts_with(&key) {
                                // ...only traverse the subtree, ignoring the key itself.
                                Some(Box::new(self.traverse(key, start, end, depth - 1)))
                            } else {
                                None
                            }
                        } else {
                            // Traverse normally, returning both the parent and sub key,
                            // in all other cases.
                            if key.len() < 2 {
                                let iter = std::iter::once(key.clone());
                                Some(if key == end {
                                    Box::new(iter)
                                } else {
                                    Box::new(iter.chain(self.traverse(key, start, end, depth - 1)))
                                })
                            } else {
                                let first = key.chars().next().unwrap();
                                Some(if key.chars().all(|c| c == first) {
                                    // If our characters are all the same,
                                    // don't add key to the list, only the subtree.
                                    Box::new(self.traverse(key, start, end, depth - 1))
                                } else {
                                    Box::new(std::iter::once(key.clone()).chain(self.traverse(
                                        key,
                                        start,
                                        end,
                                        depth - 1,
                                    )))
                                })
                            }
                        }
                    })
                    .flatten(),
            )
        }
    }

    fn distance_between_first_chars(&self, start: &str, end: &str) -> usize {
        // check the first character of both strings...
        match (start.chars().next(), end.chars().next()) {
            // if both have a first char, compare them.
            (Some(start_char), Some(end_char)) => {
                assert!(dbg!(start_char) < dbg!(end_char));
                let distance = end_char as u8 - start_char as u8;
                distance as usize + 1
            }
            // if only the start has a first char, compare it to our last possible symbol.
            (Some(start_char), None) => {
                let end_u8 = self.0.last().unwrap();
                assert!(start_char < *end_u8 as char);
                let distance = end_u8 - start_char as u8;
                distance as usize + 1
            }
            // if only the end has a first char, compare it to our first possible symbol.
            (None, Some(end_char)) => {
                let start_u8 = self.0.first().unwrap();
                // assert!(dbg!(*start_u8) < dbg!(end_char as u8));
                let distance = end_char as u8 - start_u8;
                if distance == 0 {
                    2
                } else {
                    distance as usize + 1
                }
            }
            // if there's no characters given, the whole symboltable is our range.
            _ => self.0.len(),
        }
    }
}

/// Just for internal convenience/readability, since `f64::log` kinda has
/// flipped the usual logarithm arguments.
///
/// Also converts the result to usize directly.
fn log(base: usize, anti: usize) -> usize {
    f64::log(anti as f64, base as f64).ceil() as usize
}

impl FromStr for SymbolTable {
    type Err = NonAsciiError;
    fn from_str(s: &str) -> Result<Self, NonAsciiError> {
        Self::from_chars(&s.chars().collect::<Box<[_]>>())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    #[allow(clippy::char_lit_as_u8)]
    fn valid_tables_work() {
        let _table = SymbolTable::new(&[1, 2, 3, 4, 5]);
        // Possible, but to be discouraged
        let _table = SymbolTable::new(&['a' as u8, 'b' as u8]);
        let _table = SymbolTable::from_chars(&['a', 'b', 'c']).unwrap();
        let _table = SymbolTable::from_str("0123").unwrap();
    }

    #[test]
    fn invalid_tables_error() {
        assert!(SymbolTable::from_str("🍅😂👶🏻").is_err());
        assert!(SymbolTable::from_chars(&['🍌', '🍣', '⛈']).is_err());
    }

    #[test]
    fn reasonable_values() {
        let table = SymbolTable::from_str("ab").unwrap();
        let result = table.mudder("a", "b", 1);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], "ab");
        let table = SymbolTable::from_str("0123456789").unwrap();
        let result = table.mudder("1", "2", 1);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], "15");
    }

    #[test]
    fn outputs_match_mudderjs() {
        let table = SymbolTable::from_str("abc").unwrap();
        let result = table.mudder("a", "b", 1);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], "ac");
        let table = SymbolTable::alphabet();
        let result = table.mudder("anhui", "azazel", 3);
        assert_eq!(result.len(), 3);
        assert_eq!(vec!["aq", "at", "aw"], result);
    }

    #[test]
    fn empty_start() {
        let table = SymbolTable::from_str("abc").unwrap();
        let result = table.mudder("", "c", 2);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn empty_end() {
        let table = SymbolTable::from_str("abc").unwrap();
        let result = table.mudder("b", "", 2);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn only_amount() {
        let table = SymbolTable::alphabet();
        // TODO: Should we add an alias for this?
        let result = table.mudder("", "", 10);
        assert_eq!(result.len(), 10);
    }

    #[test]
    fn values_sorting_correct() {
        let values = SymbolTable::alphabet().mudder("", "", 12);
        let mut iter = values.into_iter();
        while let (Some(one), Some(two)) = (iter.next(), iter.next()) {
            assert!(one < two);
        }
    }

    #[test]
    fn differing_input_lengths() {
        let table = SymbolTable::alphabet();
        let result = table.mudder("a", "ab", 1);
        assert_eq!(result.len(), 1);
        assert!(result[0].starts_with('a'));
    }

    // TODO: Make this test pass.
    // Currently, this works fine until it gets to `table.mudder("a", "ab", 1)`.
    // At this point, it incorrectly returns `aa`, which makes it impossible to
    // put any more strings inbetween.
    // It should actually add one level to the depth and return `aan`.
    // We should also return an error on inputs like (`a`, `aa`).
    // #[test]
    // fn values_consistently_between_start_and_end() {
    //     let table = SymbolTable::alphabet();
    //     let mut right = String::from("n");
    //     for _ in 0..50 {
    //         let new_val = dbg!(table.mudder("f", &right, 1))[0].clone();
    //         assert_ne!(new_val, right);
    //         assert_ne!(new_val, "a");
    //         right = new_val;
    //     }
    // }
}
