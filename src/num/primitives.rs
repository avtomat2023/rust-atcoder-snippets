//! Extension traits for primitive integer types.

use crate::num::BigDigit;

#[snippet = "num"]
trait PrimitiveInteger {
    fn abs_diff(self, rhs: Self) -> Self;
    fn mod_euc(self, rhs: Self) -> Self;
}

#[snippet = "num"]
macro_rules! impl_primitive_integer {
    ( $($t: ty)* ) => { $(
        impl PrimitiveInteger for $t {
            fn abs_diff(self, rhs: $t) -> $t {
                if self < rhs { rhs - self } else { self - rhs }
            }

            // https://doc.rust-lang.org/src/core/num/mod.rs.html
            #[allow(unused_comparisons)]
            fn mod_euc(self, rhs: $t) -> $t {
                let r = self % rhs;
                if r < 0 {
                    if rhs < 0 { r - rhs } else { r + rhs }
                } else {
                    r
                }
            }
        }
    )* }
}

#[snippet = "num"]
impl_primitive_integer!(u8 u16 u32 u64 usize i8 i16 i32 i64 isize);

/// Enriches unsigned integer types by adding extra division methods.
#[snippet = "num"]
pub trait PrimitiveUnsigned {
    fn ceil_div(self, rhs: Self) -> Self;
    fn round_div(self, rhs: Self) -> Self;
    fn to_le_big_digits(self) -> Vec<BigDigit>;
}

#[snippet = "num"]
macro_rules! impl_primitive_unsigned {
    ( $($t: ty)* ) => { $(
        impl PrimitiveUnsigned for $t {
            fn ceil_div(self, rhs: $t) -> $t {
                (self + rhs - 1) / rhs
            }

            fn round_div(self, rhs: $t) -> $t {
                (self + rhs/2) / rhs
            }

            fn to_le_big_digits(self) -> Vec<BigDigit> {
                vec![self as BigDigit]
            }
        }
    )* }
}

#[snippet = "num"]
impl_primitive_unsigned!(u8 u16 u32 u64 usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mod_euc() {
        let a = 7i32;
        let b = 4i32;
        assert_eq!(a.mod_euc(b), 3);
        assert_eq!((-a).mod_euc(b), 1);
        assert_eq!(a.mod_euc(-b), 3);
        assert_eq!((-a).mod_euc(-b), 1);
    }

    #[test]
    fn test_round_div() {
        for i in 0u8..50 {
            if i.round_div(100) != 0 {
                panic!("{}", i);
            }
        }
        for i in 50u8..100 {
            if i.round_div(100) != 1 {
                panic!("{}", i);
            }
        }

        for i in 0u8..51 {
            if i.round_div(101) != 0 {
                panic!("{}", i);
            }
        }
        for i in 51u8..101 {
            if i.round_div(101) != 1 {
                panic!("{}", i);
            }
        }
    }
}
