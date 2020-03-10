use std::num::TryFromIntError;

#[derive(Debug, Clone, Copy)]
pub enum NonAsciiError {
    InvalidU8(TryFromIntError),
    NonAscii,
}

impl NonAsciiError {
    const fn _description_nonascii() -> &'static str {
        "the given byte was not within ASCII range"
    }
}

impl From<TryFromIntError> for NonAsciiError {
    fn from(s: TryFromIntError) -> NonAsciiError {
        NonAsciiError::InvalidU8(s)
    }
}

use std::fmt;
impl fmt::Display for NonAsciiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidU8(error) => error.fmt(f),
            Self::NonAscii => write!(f, "{}", Self::_description_nonascii()),
        }
    }
}

impl std::error::Error for NonAsciiError {
    fn description(&self) -> &str {
        Self::_description_nonascii()
    }
}
