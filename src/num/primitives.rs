//! Extension traits for primitive integer types.

use crate::num::{WithZero, WithOne, Integer, ToSigned, ToUnsigned};

// BEGIN SNIPPET int DEPENDS ON num_types

/// Enriches signed and unsigned integer types.
pub trait PrimitiveInteger: Integer + Copy + ToSigned + ToUnsigned {
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
}

macro_rules! impl_primitive_integer_unsigned {
    ( $($t: ty, $t_signed: ty);* ) => { $(
        impl WithZero for $t {
            fn zero() -> $t { 0 }
        }

        impl WithOne for $t {
            fn one() -> $t { 1 }
        }

        impl Integer for $t {}

        impl ToSigned for $t {
            type Signed = $t_signed;

            fn to_signed(&self) -> Option<$t_signed> {
                use std::convert::TryInto;
                (*self).try_into().ok()
            }

            unsafe fn to_signed_unchecked(&self) -> $t_signed {
                *self as $t_signed
            }
        }

        impl ToUnsigned for $t {
            type Unsigned = $t;

            fn to_unsigned(&self) -> Option<$t> {
                Some(*self)
            }
        }

        impl PrimitiveInteger for $t {
            fn abs_diff(self, rhs: $t) -> $t {
                if self < rhs { rhs - self } else { self - rhs }
            }
        }
    )* }
}

impl_primitive_integer_unsigned!(
    u8, i8;
    u16, i16;
    u32, i32;
    u64, i64;
    u128, i128;
    usize, isize
);

macro_rules! impl_primitive_integer_signed {
    ( $($t: ty, $t_unsigned: ty);* ) => { $(
        impl WithZero for $t {
            fn zero() -> $t { 0 }
        }

        impl WithOne for $t {
            fn one() -> $t { 1 }
        }

        impl Integer for $t {}

        impl ToSigned for $t {
            type Signed = $t;

            fn to_signed(&self) -> Option<$t> {
                Some(*self)
            }
        }

        impl ToUnsigned for $t {
            type Unsigned = $t_unsigned;

            fn to_unsigned(&self) -> Option<$t_unsigned> {
                use std::convert::TryInto;
                (*self).try_into().ok()
            }

            unsafe fn to_unsigned_unchecked(&self) -> $t_unsigned {
                *self as $t_unsigned
            }
        }

        impl PrimitiveInteger for $t {
            fn abs_diff(self, rhs: $t) -> $t {
                if self < rhs { rhs - self } else { self - rhs }
            }
        }
    )* }
}

impl_primitive_integer_signed!(
    i8, u8;
    i16, u16;
    i32, u32;
    i64, u64;
    i128, u128;
    isize, usize
);

/// Enriches unsigned integer types.
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

    /// Greatest common divisor.
    ///
    /// If both numbers are 0, returns 0.
    /// That's because 0 is the identity element as we see (ℕ, gcd) as a monoid.
    fn gcd(self, other: Self) -> Self {
        if other == Self::zero() { self } else { other.gcd(self % &other) }
    }

    // fn to_le_big_digits(self) -> Vec<BigDigit>;
}

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

impl_primitive_unsigned!(u8 u16 u32 u64 u128 usize);

/// Enriches signed integer types.
pub trait PrimitiveSigned: PrimitiveInteger {
    /// Calculates Bézout coefficients, that's (*x*, *y*) satisfying *ax* + *by* = gcd(*a*, *b*).
    ///
    /// Returned value is a 3-tuple `(x, y, g)`.
    ///
    /// `g` is `gcd(a.abs(), b.abs())`. The right hand side of the equation is `g`.
    ///
    /// `x` and `y` are Bézout coefficients. When both `a.abs()` and `b.abs()` are positive,
    /// the coefficients satisfy `x.abs() <= b.abs()` and `y.abs() <= a.abs()`.
    /// When one of `a` and `b` is 0, either `x.abs()` or `y.abs()` is 1 and the other is 0.
    /// Otherwise, both `x` and `y` are 0.
    fn bezout(self, other: Self) -> (Self, Self, Self::Unsigned);
}

unsafe fn bezout_sub<T: PrimitiveUnsigned>(a: T, b: T) -> (T::Signed, T::Signed, T) {
    if b == T::zero() { (T::Signed::one(), T::Signed::zero(), a) } else {
        let m = (a / &b).to_signed_unchecked();
        let (x, y, g) = bezout_sub(b, a % &b);
        let solution_b = x - &(m * &y);
        (y, solution_b, g)
    }
}

macro_rules! impl_primitive_signed {
    ( $($t: ty)* ) => { $(
        impl PrimitiveSigned for $t {
            fn bezout(self, other: $t) -> ($t, $t, <$t as ToUnsigned>::Unsigned) {
                let (x, y, g) = unsafe { bezout_sub(
                    (self * self.signum()).to_unsigned_unchecked(),
                    (other * other.signum()).to_unsigned_unchecked()
                ) };
                (x * self.signum(), y * other.signum(), g)
            }
        }
    )* }
}

impl_primitive_signed!(i8 i16 i32 i64 i128 isize);

// END SNIPPET

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

    #[test]
    fn test_gcd() {
        assert_eq!(u32::gcd(0, 0), 0);
        assert_eq!(u32::gcd(1, 0), 1);
        assert_eq!(u32::gcd(123, 0), 123);
        assert_eq!(u32::gcd(0, 1), 1);
        assert_eq!(u32::gcd(0, 123), 123);
        assert_eq!(u32::gcd(1, 1), 1);
        assert_eq!(u32::gcd(31, 31), 31);
        assert_eq!(u32::gcd(56, 56), 56);
        assert_eq!(u32::gcd(31, 47), 1);
        assert_eq!(u32::gcd(47, 31), 1);
        assert_eq!(u32::gcd(56, 42), 14);
        assert_eq!(u32::gcd(42, 56), 14);
    }

    #[test]
    fn test_bezout() {
        assert_eq!(i32::bezout(0, 0), (0, 0, 0));
        assert_eq!(i32::bezout(1, 0), (1, 0, 1));
        assert_eq!(i32::bezout(0, 1), (0, 1, 1));
        assert_eq!(i32::bezout(-1, 0), (-1, 0, 1));
        assert_eq!(i32::bezout(0, -1), (0, -1, 1));

        let (x1, y1, g1) = i32::bezout(31, 47);
        assert_eq!(g1, 1);
        assert_eq!(31*x1 + 47*y1, g1 as i32);
        assert!(x1.abs() <= 47 && y1.abs() <= 31);

        let (x2, y2, g2) = i32::bezout(56, 42);
        assert_eq!(g2, 14);
        assert_eq!(56*x2 + 42*y2, g2 as i32);
        assert!(x2.abs() <= 42 && y2.abs() <= 56);

        let (x3, y3, g3) = i32::bezout(-31, 47);
        assert_eq!(g3, 1);
        assert_eq!(-31*x3 + 47*y3, g3 as i32);
        assert!(x3.abs() <= 47 && y3.abs() <= 31);

        let (x4, y4, g4) = i32::bezout(-56, -42);
        assert_eq!(g4, 14);
        assert_eq!(-56*x4 - 42*y4, g4 as i32);
        assert!(x4.abs() <= 42 && y4.abs() <= 56);
    }
}
