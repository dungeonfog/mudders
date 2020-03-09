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
    pub fn mudder(&self, start: &str, end: &str, amount: usize) -> Vec<String> {
        let depth = dbg!(self
            .0
            .len()
            // I 100% don't understand what I'm doing at this point.
            // Which is probably why it doesn't work at all.
            .pow(amount as u32)
            .add(2)
            .div(5));
        let mut pool: Vec<String> = dbg!(self
            .traverse("".to_string(), start.to_string(), end.to_string(), depth)
            .collect());
        if amount == 1 {
            // return the middle element
            vec![pool.remove(dbg!(pool.len()) / 2)]
        } else {
            let step = (pool.len() / amount) - 2;
            let mut pool = pool.into_iter();
            (1..=amount).map(|_| pool.nth(step).unwrap()).collect()
        }
        // unimplemented!()
    }

    fn traverse<'a>(
        &'a self,
        curr_key: String,
        start: String,
        end: String,
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
                    // TODO: Performance - format! isn't the best option here.
                    // itoa and string concatenation maybe?
                    .filter_map(move |c| -> Option<Box<dyn Iterator<Item = String>>> {
                        let key = format!("{}{}", curr_key, *c as char);
                        if key < start || key > end {
                            None
                        } else {
                            let iter = iter::once(key.clone());
                            if key == end {
                                Some(Box::new(iter))
                            } else {
                                Some(Box::new(iter.chain(self.traverse(
                                    key,
                                    start.clone(),
                                    end.clone(),
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
        // TODO: Somehow improve this test.
        // We can only ever check if one of the conditions panics this way.
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
