//! Numeric types and traits.

// #[snippet = "num"]
// pub type BigDigit = u64;

mod primitives;
mod modp;

pub use self::primitives::{PrimitiveInteger, PrimitiveUnsigned};
pub use self::modp::{modp, ModP, ModPBase};
