//! Numeric types and traits.

// pub type BigDigit = u64;

mod types;
#[macro_use] mod macros;

pub use self::types::{WithZero, WithOne, Numeric, Integer, Float};

mod primitives;
mod modp;

pub use self::primitives::{PrimitiveInteger, PrimitiveUnsigned, gcd, bezout};
pub use self::modp::{modp, ModP, ModPBase, FactCache, InvCache, PowCache, CombinatoricsCache};
