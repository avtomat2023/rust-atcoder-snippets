//! Numeric types and traits.

// pub type BigDigit = u64;

mod types;
pub use self::types::{WithZero, WithOne, Integer, ToSigned, ToUnsigned};

mod primitives;
pub use self::primitives::{PrimitiveInteger, PrimitiveUnsigned};
