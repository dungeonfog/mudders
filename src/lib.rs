/*!
Generate lexicographically-evenly-spaced strings between two strings
from pre-defined alphabets.

This is a rewrite of [mudderjs](https://github.com/fasiha/mudderjs); thanks
for the original work of the author and their contributors!

## Usage
Add a dependency in your Cargo.toml:

```toml
mudders = "0.0.2"
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
assert!(result[0].as_str() > "a" && result[1].as_str() > "a");
assert!(result[0].as_str() < "b" && result[1].as_str() < "b");

// The strings *should* be evenly-spaced and as short as they can be.
let table = SymbolTable::alphabet();
let result = table.mudder("anhui", "azazel", 3);
assert_eq!(result.len(), 3);
assert_eq!(vec!["aq", "as", "av"], result);
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
    ///
    /// When both parameters are empty strings, `amount` new strings that are
    /// in lexicographical order are returned.
    ///
    /// If parameter `b` is lexicographically before `a`, they are swapped internally.
    ///
    /// ```
    /// # use mudders::SymbolTable;
    /// // Using the included alphabet table
    /// let table = SymbolTable::alphabet();
    /// // Generate 10 strings from scratch
    /// let results = table.mudder("", "", 10);
    /// assert!(results.len() == 10);
    /// // results should look something like ["b", "d", "f", ..., "r", "t"]
    /// ```
    pub fn mudder(&self, a: &str, b: &str, amount: usize) -> Vec<String> {
        let (a, b) = if a.is_empty() || b.is_empty() {
            // If an argument is empty, keep the order
            (a, b)
        } else if b < a {
            // If they're not empty and b is lexicographically prior to a, swap them
            (b, a)
        } else {
            // In any other case, keep the order
            // TODO: Handle a == b
            (a, b)
        };
        // Count the characters start and end have in common.
        let matching_count: usize = {
            // Iterate through the chars of both given inputs...
            let (mut start_chars, mut end_chars) = (a.chars(), b.chars());
            // We need to keep track of this, because:
            // In the case of `a` == `"a"` and `b` == `"aab"`,
            // we actually need to compare `""` to `"b"` later on, not `""` to `"a"`.
            let mut last_start_char = '\0';
            // Counting to get the index.
            let mut i: usize = 0;
            loop {
                // Advance the iterators...
                match (start_chars.next(), end_chars.next()) {
                    // As long as there's two characters that match, increment i.
                    (Some(sc), Some(ec)) if sc == ec => {
                        last_start_char = sc;
                        i += 1;
                        continue;
                    }
                    // If start_chars have run out, but end_chars haven't, check
                    // if the current end char matches the last start char.
                    // If it does, we still need to increment our counter.
                    (None, Some(ec)) if ec == last_start_char => {
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
        let non_empty_input_count = [a, b].iter().filter(|s| !s.is_empty()).count();
        let computed_amount = || amount + non_empty_input_count;

        // Calculate the distance between the first non-matching characters.
        // If matching_count is greater than 0, we have leading common chars,
        // so we skip those, but add the amount to the depth base.
        let branching_factor = self.distance_between_first_chars(
            //            v--- matching_count might be higher than a.len()
            //           vvv   because we might count past a's end
            &a[std::cmp::min(matching_count, a.len())..],
            &b[matching_count..],
        );
        // We also add matching_count to the depth because if we're starting
        // with a common prefix, we have at least x leading characters that
        // will be the same for all substrings.
        let depth =
            depth_for(dbg!(branching_factor), dbg!(computed_amount())) + dbg!(matching_count);

        // TODO: Maybe keeping this as an iterator would be more efficient,
        // but it would have to be cloned at least once to get the pool length.
        let pool: Vec<String> = self.traverse("".into(), a, b, dbg!(depth)).collect();
        let pool = if (pool.len() as isize) - (non_empty_input_count as isize) < amount as isize {
            let depth = depth + depth_for(branching_factor, computed_amount() + pool.len());
            dbg!(self.traverse("".into(), a, b, dbg!(depth)).collect())
        } else {
            pool
        };
        if amount == 1 {
            vec![pool[(pool.len() as f64 / 2.0f64).floor() as usize].clone()]
        } else {
            let step = computed_amount() as f64 / pool.len() as f64;
            let mut counter = 0f64;
            let mut last_value = 0;
            pool.into_iter()
                .filter(|_| {
                    counter += step;
                    let new_value = counter.floor() as usize;
                    if new_value > last_value {
                        last_value = new_value;
                        true
                    } else {
                        false
                    }
                })
                .take(amount)
                .collect()
        }
    }

    // fn

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

/// Calculate the required depth for the given values.
///
/// `branching_factor` is used as the logarithm base, `n_elements` as the
/// value, and the result is rounded up and cast to usize.
fn depth_for(branching_factor: usize, n_elements: usize) -> usize {
    f64::log(n_elements as f64, branching_factor as f64).ceil() as usize
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

    // Public API tests:

    #[test]
    #[allow(clippy::char_lit_as_u8)]
    fn valid_tables_work() {
        assert!(SymbolTable::new(&[1, 2, 3, 4, 5]).is_ok());
        assert!(SymbolTable::new(&[125, 126, 127]).is_ok());
        // Possible, but to be discouraged
        assert!(SymbolTable::new(&['a' as u8, 'f' as u8]).is_ok());
        assert!(SymbolTable::from_chars(&['a', 'b', 'c']).is_ok());
        assert!(SymbolTable::from_str("0123").is_ok());
    }

    #[test]
    fn invalid_tables_error() {
        assert!(SymbolTable::from_str("🍅😂👶🏻").is_err());
        assert!(SymbolTable::from_chars(&['🍌', '🍣', '⛈']).is_err());
        assert!(SymbolTable::new(&[128, 129, 130]).is_err());
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
    fn outputs_more_or_less_match_mudderjs() {
        let table = SymbolTable::from_str("abc").unwrap();
        let result = table.mudder("a", "b", 1);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], "ac");
        let table = SymbolTable::alphabet();
        let result = table.mudder("anhui", "azazel", 3);
        assert_eq!(result.len(), 3);
        assert_eq!(vec!["aq", "as", "av"], result);
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

    #[test]
    fn values_consistently_between_start_and_end() {
        let table = SymbolTable::alphabet();
        {
            // From z to a
            let mut right = String::from("z");
            for _ in 0..500 {
                let new_val = dbg!(table.mudder("a", &right, 1))[0].clone();
                assert!(new_val < right);
                assert!(new_val.as_str() > "a");
                right = new_val;
            }
        }
        {
            // And from a to z
            let mut left = String::from("a");
            // TODO:    vv this test fails for higher numbers. FIXME!
            for _ in 0..17 {
                let new_val = dbg!(table.mudder(&left, "z", 1))[0].clone();
                assert!(new_val > left);
                assert!(new_val.as_str() < "z");
                left = new_val;
            }
        }
    }

    // Internal/private method tests:

    #[test]
    fn traverse_alphabet() {
        fn traverse_alphabet(a: &str, b: &str, depth: usize) -> Vec<String> {
            SymbolTable::alphabet()
                .traverse("".into(), a, b, depth)
                .collect()
        }
        assert_eq!(traverse_alphabet("a", "d", 1), vec!["a", "b", "c", "d"]);
        assert_eq!(
            traverse_alphabet("a", "z", 1),
            ('a' as u32 as u8..='z' as u32 as u8)
                .map(|c| (c as char).to_string())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            traverse_alphabet("a", "b", 2),
            vec![
                "a", "ab", "ac", "ad", "ae", "af", "ag", "ah", "ai", "aj", "ak", "al", "am", "an",
                "ao", "ap", "aq", "ar", "as", "at", "au", "av", "aw", "ax", "ay", "az", "b"
            ]
        )
    }

    #[test]
    fn traverse_custom() {
        fn traverse(table: &str, a: &str, b: &str, depth: usize) -> Vec<String> {
            let table = SymbolTable::from_str(table).unwrap();
            table.traverse("".into(), a, b, depth).collect()
        }
        assert_eq!(traverse("abc", "a", "c", 1), vec!["a", "b", "c"]);
        assert_eq!(
            traverse("abc", "a", "c", 2),
            vec!["a", "ab", "ac", "b", "ba", "bc", "c"]
        );
        assert_eq!(
            traverse("0123456789", "1", "2", 2),
            vec!["1", "10", "12", "13", "14", "15", "16", "17", "18", "19", "2"]
        );
    }

    #[test]
    fn distance_between_first_chars_correct() {
        let table = SymbolTable::alphabet();
        assert_eq!(table.distance_between_first_chars("a", "b"), 2);
        assert_eq!(table.distance_between_first_chars("a", "z"), 26);
        assert_eq!(table.distance_between_first_chars("", ""), 26);
        assert_eq!(table.distance_between_first_chars("n", ""), 13);
        assert_eq!(table.distance_between_first_chars("", "n"), 14);
        assert_eq!(table.distance_between_first_chars("y", "z"), 2);
        assert_eq!(table.distance_between_first_chars("a", "y"), 25);
        assert_eq!(
            table.distance_between_first_chars("aaaa", "zzzz"),
            table.distance_between_first_chars("aa", "zz")
        );

        let table = SymbolTable::from_str("12345").unwrap();
        assert_eq!(table.distance_between_first_chars("1", "2"), 2);
        assert_eq!(table.distance_between_first_chars("1", "3"), 3);
        assert_eq!(table.distance_between_first_chars("2", "3"), 2);
    }
}
