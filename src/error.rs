use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::num::TryFromIntError;

/// Checks for a condition, and if it false, returns the given error.
///
/// Intended usage:
///
/// ```
/// fn fallibe_function(i: i32) -> Result<(), String> {
///     ensure! { i > 5, "i may not be less than 5" }
///     Ok(())
/// }
/// ```
///
/// Note: Uses From::from on $error.
macro_rules! ensure {
    ($predicate:expr, $error:expr) => {
        if !$predicate {
            return Err(From::from($error));
        }
    };
}

/// Error that might occur when generating new strings.
#[derive(Debug, Clone, PartialEq)]
pub enum GenerationError {
    NonAsciiInput(NonAsciiError),
    UnknownCharacters(String),
    MatchingStrings(String),
    Internal(InternalError),
}

impl From<NonAsciiError> for GenerationError {
    fn from(s: NonAsciiError) -> GenerationError {
        GenerationError::NonAsciiInput(s)
    }
}
impl From<InternalError> for GenerationError {
    fn from(s: InternalError) -> GenerationError {
        GenerationError::Internal(s)
    }
}

impl Display for GenerationError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            GenerationError::NonAsciiInput(err) => err.fmt(f),
            GenerationError::UnknownCharacters(string) => write!(
                f,
                "the given string contained characters not in the SymbolTable: {}",
                string
            ),
            GenerationError::MatchingStrings(s) => write!(f, "the given strings are equal: {}", s),
            GenerationError::Internal(err) => write!(
                f,
                "Internal error: {}; this is a bug in mudders, please report it!",
                err
            ),
        }
    }
}

impl Error for GenerationError {}

/// Errors that are likely not user errors, but bugs in the library.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum InternalError {
    FailedToGetMiddle,
    NotEnoughItemsInPool,
    WrongCharOrder(char, char),
}

impl Display for InternalError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            InternalError::FailedToGetMiddle => write!(f, "failed to get middle element from pool"),
            InternalError::NotEnoughItemsInPool => {
                write!(f, "failed to get the requested amount of items")
            }
            InternalError::WrongCharOrder(start, end) => write!(
                f,
                "expected first char ({first:?}) to precede second ({second:?}), but it didn't",
                first = start,
                second = end
            ),
        }
    }
}

impl Error for InternalError {}

/// An error indicating that a character passed to mudders is not in ASCII range.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NonAsciiError {
    InvalidU8(TryFromIntError),
    NonAsciiU8,
}

impl From<TryFromIntError> for NonAsciiError {
    fn from(s: TryFromIntError) -> NonAsciiError {
        NonAsciiError::InvalidU8(s)
    }
}

impl Display for NonAsciiError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            NonAsciiError::InvalidU8(error) => error.fmt(f),
            NonAsciiError::NonAsciiU8 => write!(f, "a given byte was not within ASCII range"),
        }
    }
}

impl Error for NonAsciiError {}

/// Errors that might occur on SymbolTable construction.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CreationError {
    NonAscii(NonAsciiError),
    EmptySlice,
}

impl From<NonAsciiError> for CreationError {
    fn from(s: NonAsciiError) -> CreationError {
        CreationError::NonAscii(s)
    }
}

impl Display for CreationError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            CreationError::NonAscii(err) => err.fmt(f),
            CreationError::EmptySlice => write!(f, "tried to create an empty SymbolTable"),
        }
    }
}
