#[snippet = "num"]
trait RichInt {
    fn abs_diff(self, rhs: Self) -> Self;
    fn mod_euc(self, rhs: Self) -> Self;
}

#[snippet = "num"]
macro_rules! impl_rich_int {
    ( $($t: ty)* ) => { $(
        impl RichInt for $t {
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
impl_rich_int!(u8 u16 u32 u64 usize i8 i16 i32 i64 isize);

/// Enriches unsigned integer types by adding extra division methods.
#[snippet = "num"]
pub trait RichUInt {
    fn ceil_div(self, rhs: Self) -> Self;
    fn round_div(self, rhs: Self) -> Self;
}

#[snippet = "num"]
macro_rules! impl_rich_uint {
    ( $($t: ty)* ) => { $(
        impl RichUInt for $t {
            fn ceil_div(self, rhs: $t) -> $t {
                (self + rhs - 1) / rhs
            }

            fn round_div(self, rhs: $t) -> $t {
                (self + rhs/2 - 1) / rhs
            }
        }
    )* }
}

#[snippet = "num"]
impl_rich_uint!(u8 u16 u32 u64);

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
}
