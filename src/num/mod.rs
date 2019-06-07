//! Numeric types and traits.

// #[snippet = "num"]
// pub type BigDigit = u64;

mod types;
#[macro_use] mod macros;

pub use self::types::{WithZero, WithOne, Numeric, Integer, Float};

mod primitives;
mod modp;

pub use self::primitives::{PrimitiveInteger, PrimitiveUnsigned};
pub use self::modp::{modp, ModP, ModPBase};
