//! Unsinged integer division by ceiling and rounding.

/// Enriches unsigned integer types by adding extra division methods.
#[snippet = "div"]
pub trait RoundingDiv {
    fn ceildiv(self, rhs: Self) -> Self;
    fn rounddiv(self, rhs: Self) -> Self;
}

#[snippet = "div"]
macro_rules! impl_rounding_div {
    ( $($t: ty)* ) => { $(
        impl RoundingDiv for $t {
            fn ceildiv(self, rhs: $t) -> $t {
                (self + rhs - 1) / rhs
            }

            fn rounddiv(self, rhs: $t) -> $t {
                (self + rhs/2 - 1) / rhs
            }
        }
    )* }
}

#[snippet = "div"]
impl_rounding_div!(u8 u16 u32 u64);
