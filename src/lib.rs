/*!
Generate lexicographically-evenly-spaced strings between two strings
from pre-defined alphabets.

This is a rewrite of [mudderjs](https://github.com/fasiha/mudderjs); thanks
for the original work of the author and their contributors!
*/

use std::ops::{Add, Div};
use std::{convert::TryFrom, num::TryFromIntError, str::FromStr};

pub struct SymbolTable(Vec<u8>);

pub struct NonAsciiError;

impl SymbolTable {
    pub fn new(source: &[u8]) -> Self {
        // Copy the values, we need to own them anyways...
        let mut vec: Vec<_> = source.iter().copied().collect();
        // Sort them so they're actually in order.
        // (You can pass in ['b', 'a'], but that's not usable internally I think.)
        vec.sort();
        Self(vec)
    }
    pub fn from_chars(source: &[char]) -> Result<Self, TryFromIntError> {
        let inner: Box<[u8]> = source
            .iter()
            .map(|i| u8::try_from(*i as u32))
            .collect::<Result<_, _>>()?;
        Ok(Self::new(&inner))
    }
    /// Generate `amount` strings that lexicographically sort between `start` and `end`.
    /// The algorithm will try to make them as evenly-spaced as possible.
    pub fn mudder(&self, start: &str, end: &str, amount: usize) -> Vec<String> {
        let depth = dbg!(self
            .0
            .len()
            // I 100% don't understand what I'm doing at this point.
            // Which is probably why it doesn't work at all.
            .pow(amount as u32)
            .add(2)
            .div(5));
        // TODO: Maybe keeping this as an iterator would be more efficient,
        // but it would have to be cloned at least once to get the pool length.
        let pool: Vec<String> = self.traverse("".to_string(), start, end, depth).collect();
        if amount == 1 {
            // return the middle element
            vec![pool[pool.len() / 2].clone()]
        } else {
            let step = (pool.len() / amount) - 2;
            let mut pool = pool.into_iter();
            (1..=amount).map(|_| pool.nth(step).unwrap()).collect()
        }
        // unimplemented!()
    }

    /// Traverses a virtual tree of strings to the given depth.
    fn traverse<'a>(
        &'a self,
        curr_key: String,
        start: &'a str,
        end: &'a str,
        depth: usize,
    ) -> Box<dyn Iterator<Item = String> + 'a> {
        use std::iter;
        if depth == 0 {
            Box::new(iter::empty())
        } else {
            // Generate all possible mutations on level
            // let mut list = Vec::new();
            Box::new(
                self.0
                    .iter()
                    .filter_map(move |c| -> Option<Box<dyn Iterator<Item = String>>> {
                        // TODO: Performance - this probably still isn't the best option.
                        // Desparately trying to avoid unnecessary allocations here...
                        let key = {
                            let the_char = *c as char;
                            let mut string =
                                String::with_capacity(curr_key.len() + the_char.len_utf8());
                            string.push_str(&curr_key);
                            string.push(the_char);
                            string
                        };
                        if key.as_str() < start || key.as_str() > end {
                            None
                        } else {
                            let iter = iter::once(key.clone());
                            if key == end {
                                Some(Box::new(iter))
                            } else {
                                Some(Box::new(iter.chain(self.traverse(
                                    key,
                                    start,
                                    end,
                                    depth - 1,
                                ))))
                            }
                        }
                    })
                    .flatten(),
            )
        }
    }
}

impl FromStr for SymbolTable {
    type Err = TryFromIntError;
    fn from_str(s: &str) -> Result<Self, TryFromIntError> {
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
        let table = SymbolTable::from_str("abc").unwrap();
        let result = dbg!(table.mudder("a", "c", 4));
        assert_eq!(result.len(), 4);
        // assert_eq!(result[0], "b");
        // let table = SymbolTable::from_str("0123456789").unwrap();
        // let result = table.mudder("1", "2", 1);
        // assert_eq!(result[0], "15");
    }

    #[test]
    fn outputs_match_mudderjs() {
        let table = SymbolTable::from_str("abc").unwrap();
        let result = table.mudder("a", "b", 1);
        assert_eq!(result[0], "ab");
    }
}
