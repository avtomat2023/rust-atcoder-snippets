//! Numeric types and traits.

// pub type BigDigit = u64;

mod primitives;
pub use self::primitives::{PrimitiveInteger, PrimitiveUnsigned, gcd, bezout};
