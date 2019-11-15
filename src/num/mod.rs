//! Numeric types and traits.

// pub type BigDigit = u64;

mod primitives;
mod modp;

pub use self::primitives::{PrimitiveInteger, PrimitiveUnsigned, gcd, bezout};
pub use self::modp::{modp, ModP, ModPBase, FactCache, InvCache, PowCache, CombinatoricsCache};
