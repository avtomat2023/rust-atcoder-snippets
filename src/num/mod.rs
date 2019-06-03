//! Numeric types and traits.

// #[snippet = "num"]
// pub type BigDigit = u64;

pub mod primitives;

/// Integer supporting basic operations and constants.
#[snippet = "num"]
pub trait Integer: Sized + Eq + Ord +
    // Higher Ranked Trait Bound
    // https://stackoverflow.com/questions/34630695
    for<'a> std::ops::Add<&'a Self, Output=Self> +
    for<'a> std::ops::Sub<&'a Self, Output=Self> +
    for<'a> std::ops::Div<&'a Self, Output=Self>
{
    fn one() -> Self;
}
