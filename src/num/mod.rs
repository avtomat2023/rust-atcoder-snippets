//! Numeric types and traits.

// #[snippet = "num"]
// pub type BigDigit = u64;

mod integer;
#[macro_use] mod macros;

pub use self::integer::Integer;

pub mod primitives;
pub mod mod_p;
