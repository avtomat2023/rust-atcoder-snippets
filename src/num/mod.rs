//! Numeric types and traits.

// pub type BigDigit = u64;

mod types;
pub use self::types::{WithZero, WithOne, Numeric, Integer, Float};

mod primitives;
pub use self::primitives::{PrimitiveInteger, PrimitiveUnsigned, gcd, bezout};
