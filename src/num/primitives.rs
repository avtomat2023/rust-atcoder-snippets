//! Extension traits for primitive integer types.

/// Enriches signed and unsigned integer types.
#[snippet = "num"]
pub trait PrimitiveInteger:
    Sized + Ord +
    std::ops::Add<Output=Self> +
    std::ops::Sub<Output=Self> +
    std::ops::Div<Output=Self>
{
    fn one() -> Self;

    /// Calculate absolute value of *a* - *b*.
    ///
    /// This is useful for unsigned integers because overflow never happens
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::num::*;
    /// assert_eq!(5u8.abs_diff(3u8), 2u8);
    /// assert_eq!(3u8.abs_diff(5u8), 2u8);
    /// ```
    fn abs_diff(self, rhs: Self) -> Self;

    /// The least nonnegative remainder of *a* mod *b*.
    ///
    /// You can use this method in [the latest nightly Rust](https://doc.rust-lang.org/std/primitive.i32.html#method.rem_euclid).
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::num::*;
    /// let a = 7i32;
    /// let b = 4i32;
    ///
    /// assert_eq!(a.rem_euclid(b), 3);
    /// assert_eq!((-a).rem_euclid(b), 1);
    /// assert_eq!(a.rem_euclid(-b), 3);
    /// assert_eq!((-a).rem_euclid(-b), 1);
    /// ```
    fn rem_euclid(self, rhs: Self) -> Self;
}

#[snippet = "num"]
macro_rules! impl_primitive_integer {
    ( $($t: ty)* ) => { $(
        impl PrimitiveInteger for $t {
            fn one() -> $t {
                1
            }

            fn abs_diff(self, rhs: $t) -> $t {
                if self < rhs { rhs - self } else { self - rhs }
            }

            // Implementation: https://doc.rust-lang.org/src/core/num/mod.rs.html
            #[allow(unused_comparisons)]
            fn rem_euclid(self, rhs: $t) -> $t {
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

/// Enriches unsigned integer types.
#[snippet = "num"]
pub trait PrimitiveUnsigned: PrimitiveInteger {
    /// Division with ceiling.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::num::*;
    /// assert_eq!(13u8.ceil_div(10u8), 2)
    /// ```
    fn ceil_div(self, rhs: Self) -> Self;

    /// Division with rounding off.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::num::*;
    /// assert_eq!(4u8.round_div(10u8), 0);
    /// assert_eq!(5u8.round_div(10u8), 1);
    /// ```
    fn round_div(self, rhs: Self) -> Self;

    /// Returns maximum `x` such that `2.pow(x) <= self`.
    ///
    /// If `self` is zero, returns `None`.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::num::*;
    /// assert_eq!(0b10000_u32.log2(), Some(4));
    /// assert_eq!(0b10001_u32.log2(), Some(4));
    /// ```
    fn log2(self) -> Option<Self>;

    /// Returns minimum `x` such that `2.pow(x) >= self`.
    ///
    /// If `self` is zero, returns `None`.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::num::*;
    /// assert_eq!(0b10000_u32.ceil_log2(), Some(4));
    /// assert_eq!(0b10001_u32.ceil_log2(), Some(5));
    /// ```
    fn ceil_log2(self) -> Option<Self>;

    /// Returns maximum `x` such that `x*x <= self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::num::*;
    /// assert_eq!(15u32.sqrt(), 3);
    /// assert_eq!(16u32.sqrt(), 4);
    /// ```
    fn sqrt(self) -> Self;

    // fn to_le_big_digits(self) -> Vec<BigDigit>;
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

            fn log2(mut self) -> Option<$t> {
                if self == 0 {
                    None
                } else {
                    let mut ans = 0;
                    while self > 1 {
                        ans += 1;
                        self /= 2;
                    }
                    Some(ans)
                }
            }

            fn ceil_log2(self) -> Option<$t> {
                self.log2().map(|x| {
                    (self + ((1<<x) - 1)).log2().unwrap()
                })
            }

            fn sqrt(self) -> $t {
                (self as f64).sqrt() as $t
            }

            // fn to_le_big_digits(self) -> Vec<BigDigit> {
            //     vec![self as BigDigit]
            // }
        }
    )* }
}

#[snippet = "num"]
impl_primitive_unsigned!(u8 u16 u32 u64 usize);

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn test_log2() {
        assert_eq!(0u32.log2(), None);
        assert_eq!(1u32.log2(), Some(0));
        assert_eq!(2u32.log2(), Some(1));
        assert_eq!(3u32.log2(), Some(1));
        assert_eq!(0b1001011u32.log2(), Some(6));
    }

    #[test]
    fn test_ceil_log2() {
        assert_eq!(0u32.ceil_log2(), None);
        assert_eq!(1u32.ceil_log2(), Some(0));
        assert_eq!(2u32.ceil_log2(), Some(1));
        assert_eq!(3u32.ceil_log2(), Some(2));
        assert_eq!(0b1001011u32.ceil_log2(), Some(7));
    }

    #[test]
    fn test_sqrt() {
        assert_eq!(0u32.sqrt(), 0);
        assert_eq!(1u32.sqrt(), 1);
        assert_eq!(2u32.sqrt(), 1);
        assert_eq!(3u32.sqrt(), 1);
        assert_eq!(4u32.sqrt(), 2);
        assert_eq!(9999u32.sqrt(), 99);
        assert_eq!(10000u32.sqrt(), 100);
    }
}
