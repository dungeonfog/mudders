[![Build Status](https://travis-ci.org/Follpvosten/mudders.svg?branch=master)](https://travis-ci.org/Follpvosten/mudders)

# mudders

Generate lexicographically-evenly-spaced strings between two strings
from pre-defined alphabets.

This is a rewrite of [mudderjs](https://github.com/fasiha/mudderjs); thanks
for the original work of the author and their contributors!

### Usage
Add a dependency in your Cargo.toml:

```toml
mudders = "0.0.1"
```

Now you can generate lexicographically-spaced strings in a few different ways:

```rust
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

### Notes
The most notable difference to Mudder.js is that currently, mudders only
supports ASCII characters (because 127 characters ought to be enough for
everyone™). Our default `::alphabet()` also only has lowercase letters.

