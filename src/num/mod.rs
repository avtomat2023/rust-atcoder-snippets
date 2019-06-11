//! Numeric types and traits.

// #[snippet = "num"]
// pub type BigDigit = u64;

mod primitives;
mod mod_p;

pub use self::primitives::{PrimitiveInteger, PrimitiveUnsigned};
pub use self::mod_p::{ModP, ModPBase};
