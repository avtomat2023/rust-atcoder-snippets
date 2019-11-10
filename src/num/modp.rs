//! Arithmetics modulo a prime number.
//!
//! Never use this module in multi-threaded programs.
// 動的なmod設定が必要な問題: ABC137 F
// 複数のmodを使い分けなければならない問題には対応できない

// BEGIN SNIPPET modp

pub type ModPBase = u64;
pub type ModPModulus = u32;

/// The modulus which is a prime number.
///
/// In the contest, change the value by `ModP::set_mod` method
/// before any use of `ModP`.
/// Typically, the value is `1_000_000_007`.
static mut MODULUS: ModPBase = 0;

/// A number whose arithmetics is carried modulo a prime number.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ModP {
    base: ModPBase
}

impl ModP {
    /// Sets the modulus.
    ///
    /// If `modulus` is not a prime number, returns `Err`.
    ///
    /// # Undefined behaviors
    ///
    /// If you make another call of `set_mod` after creating `ModP` numbers,
    /// you must not use the numbers.
    /// The correctness of calculations using the numbers is not guaranteed.
    ///
    /// If you call `set_mod` when two or more threads use `ModP` numbers,
    /// the correctness of calculations using the numbers is not guaranteed.
    pub unsafe fn set_mod(modulus: ModPModulus) -> Result<(), String> {
        if modulus <= 1 {
            return Err(format!("{} is not a prime number.", modulus));
        }

        if modulus >= 4 {
            if modulus % 2 == 0 || modulus % 3 == 0 {
                return Err(format!("{} is not a prime number.", modulus));
            }
            let mut divisor = 5;
            loop {
                if divisor * divisor > modulus {
                    break;
                }
                if modulus % divisor == 0 {
                    return Err(format!("{} is not a prime number.", modulus));
                }
                divisor += 2;

                if divisor * divisor > modulus {
                    break;
                }
                if modulus % divisor == 0 {
                    return Err(format!("{} is not a prime number.", modulus));
                }
                divisor += 4;
            }
        }

        MODULUS = modulus as ModPBase;
        Ok(())
    }

    /// Create a number.
    pub fn new(n: ModPBase) -> ModP {
        if !cfg!(test) {
            assert!(unsafe { MODULUS } != 0,
                    "Call ModP::set_mod before using ModP.");
        }
        ModP { base: n % unsafe { MODULUS } }
    }

    /// Create a number without taking remainder by the modulus.
    ///
    /// If n is greater than or equal to the modulus,
    /// the correctness of calculations is not guaranteed.
    pub unsafe fn new_unchecked(n: ModPBase) -> ModP {
        ModP { base: n }
    }

    /// Returns a `ModPBase` satisfying `0 <= x < modulus`.
    pub fn base(&self) -> ModPBase {
        self.base
    }

    /// Calculate power using exponentiation by squaring.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # extern crate atcoder_snippets;
    /// # use atcoder_snippets::num::*;
    /// // MODULUS is set to 7.
    /// // 2^5 = 32 = 4 mod 7.
    /// assert_eq!(ModP::new(2).pow(5), ModP::new(4));
    /// ```
    pub fn pow(self, exp: ModPBase) -> ModP {
        if exp == 0 { ModP::new(1) } else {
            let sub = self.pow(exp / 2);
            if exp % 2 == 0 {
                sub * sub
            } else {
                self * sub * sub
            }
        }
    }

    /// Inverse element.
    ///
    /// # Panic
    ///
    /// Panics if `self` is zero.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # extern crate atcoder_snippets;
    /// # use atcoder_snippets::num::*;
    /// // MODULUS is set to 7.
    /// // 3^5 = 15 = 1 mod 7.
    /// assert_eq!(ModP::new(3).inv(), ModP::new(5));
    /// ```
    pub fn inv(self) -> ModP {
        assert!(self.base() != 0);
        self.pow(unsafe { MODULUS } - 2)
    }
}

/// Shorthand of `ModP::new(x)`.
pub fn modp(x: ModPBase) -> ModP {
    ModP::new(x)
}

impl std::fmt::Display for ModP {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.base())
    }
}

impl std::fmt::Debug for ModP {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} mod P", self.base())
    }
}

impl PartialEq<ModPBase> for ModP {
    fn eq(&self, other: &ModPBase) -> bool {
        self.base() == other % unsafe { MODULUS }
    }
}

impl PartialEq<ModP> for ModPBase {
    fn eq(&self, other: &ModP) -> bool {
        self % unsafe { MODULUS } == other.base() % unsafe { MODULUS }
    }
}

impl std::ops::Add for ModP {
    type Output = ModP;

    fn add(self, rhs: ModP) -> ModP {
        let m = unsafe { MODULUS };
        ModP { base: (self.base() + rhs.base() % m) % m }
    }
}

impl std::ops::Add<ModPBase> for ModP {
    type Output = ModP;

    fn add(self, rhs: ModPBase) -> ModP {
        self + ModP::new(rhs)
    }
}

impl std::ops::Add<ModP> for ModPBase {
    type Output = ModP;

    fn add(self, rhs: ModP) -> ModP {
        ModP::new(self) + rhs.base()
    }
}

impl std::ops::AddAssign for ModP {
    fn add_assign(&mut self, rhs: ModP) {
        *self = *self + rhs
    }
}

impl std::ops::AddAssign<ModPBase> for ModP {
    fn add_assign(&mut self, rhs: ModPBase) {
        *self = *self + ModP::new(rhs)
    }
}

impl std::ops::Neg for ModP {
    type Output = ModP;

    fn neg(self) -> ModP {
        ModP::new(unsafe { MODULUS } - self.base())
    }
}

impl std::ops::Sub for ModP {
    type Output = ModP;

    fn sub(self, rhs: ModP) -> ModP {
        self + (-rhs)
    }
}

impl std::ops::Sub<ModPBase> for ModP {
    type Output = ModP;

    fn sub(self, rhs: ModPBase) -> ModP {
        self - ModP::new(rhs)
    }
}

impl std::ops::Sub<ModP> for ModPBase {
    type Output = ModP;

    fn sub(self, rhs: ModP) -> ModP {
        ModP::new(self) - rhs
    }
}

impl std::ops::SubAssign for ModP {
    fn sub_assign(&mut self, rhs: ModP) {
        *self = *self - rhs;
    }
}

impl std::ops::SubAssign<ModPBase> for ModP {
    fn sub_assign(&mut self, rhs: ModPBase) {
        *self = *self - ModP::new(rhs)
    }
}

impl std::ops::Mul for ModP {
    type Output = ModP;

    fn mul(self, rhs: ModP) -> ModP {
        let m = unsafe { MODULUS };
        ModP { base: self.base() * (rhs.base() % m) % m }
    }
}

impl std::ops::Mul<ModPBase> for ModP {
    type Output = ModP;

    fn mul(self, rhs: ModPBase) -> ModP {
        self * ModP::new(rhs)
    }
}

impl std::ops::Mul<ModP> for ModPBase {
    type Output = ModP;

    fn mul(self, rhs: ModP) -> ModP {
        ModP::new(self) * rhs.base()
    }
}

impl std::ops::MulAssign for ModP {
    fn mul_assign(&mut self, rhs: ModP) {
        *self = *self * rhs
    }
}

impl std::ops::MulAssign<ModPBase> for ModP {
    fn mul_assign(&mut self, rhs: ModPBase) {
        *self = *self * ModP::new(rhs)
    }
}

impl std::ops::Div for ModP {
    type Output = ModP;

    fn div(self, rhs: ModP) -> ModP {
        self * rhs.inv()
    }
}

impl std::ops::Div<ModPBase> for ModP {
    type Output = ModP;

    fn div(self, rhs: ModPBase) -> ModP {
        self * ModP::new(rhs).inv()
    }
}

impl std::ops::Div<ModP> for ModPBase {
    type Output = ModP;

    fn div(self, rhs: ModP) -> ModP {
        ModP::new(self) * rhs.inv()
    }
}

impl std::ops::DivAssign for ModP {
    fn div_assign(&mut self, rhs: ModP) {
        *self = *self / rhs;
    }
}

impl std::ops::DivAssign<ModPBase> for ModP {
    fn div_assign(&mut self, rhs: ModPBase) {
        *self = *self / ModP::new(rhs)
    }
}

impl std::iter::Sum for ModP {
    fn sum<I: Iterator<Item=ModP>>(iter: I) -> ModP {
        let mut ans = 0;
        for n in iter {
            ans += n.base();
        }
        ModP::new(ans)
    }
}

impl<'a> std::iter::Sum<&'a ModP> for ModP {
    fn sum<I: Iterator<Item=&'a ModP>>(iter: I) -> ModP {
        let mut ans = 0;
        for n in iter {
            ans += n.base();
        }
        ModP::new(ans)
    }
}

impl std::iter::Product for ModP {
    fn product<I: Iterator<Item=ModP>>(iter: I) -> ModP {
        let mut ans = unsafe { ModP::new_unchecked(1) };
        for n in iter {
            ans *= n;
        }
        ans
    }
}

impl<'a> std::iter::Product<&'a ModP> for ModP {
    fn product<I: Iterator<Item=&'a ModP>>(iter: I) -> ModP {
        let mut ans = unsafe { ModP::new_unchecked(1) };
        for &n in iter {
            ans *= n;
        }
        ans
    }
}

use read::{Readable, Words};

readable!(ModP, 1, |ws| ModP::new(ws[0].read::<ModPBase>()));

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_mod() {
        unsafe {
            // small numbers
            assert!(ModP::set_mod(0).is_err());
            assert!(ModP::set_mod(1).is_err());
            assert!(ModP::set_mod(2).is_ok());
            assert!(ModP::set_mod(3).is_ok());
            assert!(ModP::set_mod(4).is_err());
            assert!(ModP::set_mod(5).is_ok());
            assert!(ModP::set_mod(6).is_err());
            assert!(ModP::set_mod(7).is_ok());
            assert!(ModP::set_mod(8).is_err());
            assert!(ModP::set_mod(9).is_err());
            assert!(ModP::set_mod(10).is_err());

            // large numbers
            assert!(ModP::set_mod(10000).is_err());
            assert!(ModP::set_mod(10001).is_err());
            assert!(ModP::set_mod(10002).is_err());
            assert!(ModP::set_mod(10003).is_err());
            assert!(ModP::set_mod(10004).is_err());
            assert!(ModP::set_mod(10005).is_err());
            assert!(ModP::set_mod(10006).is_err());
            assert!(ModP::set_mod(10007).is_ok());
            assert!(ModP::set_mod(10008).is_err());
            assert!(ModP::set_mod(10009).is_ok());

            // square numbers
            assert!(ModP::set_mod(16).is_err());
            assert!(ModP::set_mod(7056).is_err());

            // typical prime numbers
            assert!(ModP::set_mod(998_244_353).is_ok());
            assert!(ModP::set_mod(1_000_000_007).is_ok());
        }
    }

    #[test]
    fn test_new() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::new(3), ModP::new(10));
        assert_eq!(modp(3), modp(10));
    }

    #[test]
    fn test_pow() {
        unsafe { ModP::set_mod(7).unwrap(); }

        let zero = ModP::new(0);
        assert_eq!(zero.pow(0), ModP::new(1));
        assert_eq!(zero.pow(1), ModP::new(0));
        assert_eq!(zero.pow(ModPBase::max_value()), ModP::new(0));

        let n = ModP::new(3);
        assert_eq!(n.pow(0), ModP::new(1));
        assert_eq!(n.pow(1), ModP::new(3));
        assert_eq!(n.pow(2), ModP::new(2));
        assert_eq!(n.pow(3), ModP::new(6));
        assert_eq!(n.pow(ModPBase::max_value()), ModP::new(6));
    }

    #[test]
    fn test_inv() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::new(1).inv(), ModP::new(1));
        assert_eq!(ModP::new(2).inv(), ModP::new(4));
        assert_eq!(ModP::new(3).inv(), ModP::new(5));
        assert_eq!(ModP::new(4).inv(), ModP::new(2));
        assert_eq!(ModP::new(5).inv(), ModP::new(3));
        assert_eq!(ModP::new(6).inv(), ModP::new(6));
    }

    #[test]
    fn test_partial_eq() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::new(3), 10);
        assert_eq!(ModP::new(10), 3);
        assert_eq!(3, ModP::new(10));
        assert_eq!(10, ModP::new(3));
    }

    #[test]
    fn test_add() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::new(5) + ModP::new(5), ModP::new(3));
        assert_eq!(ModP::new(5) + 5, ModP::new(3));
        assert_eq!(5 + ModP::new(5), ModP::new(3));
    }

    #[test]
    fn test_add_avoiding_overflow() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::new(5) + ModPBase::max_value(), ModP::new(6));
        assert_eq!(ModPBase::max_value() + ModP::new(5), ModP::new(6))
    }

    #[test]
    fn test_add_assign() {
        unsafe { ModP::set_mod(7).unwrap(); }

        let mut n1 = ModP::new(5);
        n1 += ModP::new(5);
        assert_eq!(n1, ModP::new(3));

        let mut n2 = ModP::new(5);
        n2 += 5;
        assert_eq!(n2, ModP::new(3));
    }

    #[test]
    fn test_add_assign_avoiding_overflow() {
        unsafe { ModP::set_mod(7).unwrap(); }
        let mut n = ModP::new(5);
        n += u64::max_value();
        assert_eq!(n, ModP::new(6));
    }

    #[test]
    fn test_neg() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(-ModP::new(3), ModP::new(4));
        assert_eq!(-ModP::new(0), ModP::new(0));
    }

    #[test]
    fn test_sub() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::new(3) - ModP::new(4), ModP::new(6));
        assert_eq!(ModP::new(3) - 4, ModP::new(6));
        assert_eq!(3 - ModP::new(4), ModP::new(6));
    }

    #[test]
    fn test_sub_avoiding_overflow() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::new(5) - u64::max_value(), ModP::new(4));
    }

    #[test]
    fn test_sub_assign() {
        unsafe { ModP::set_mod(7).unwrap(); }

        let mut n1 = ModP::new(3);
        n1 -= ModP::new(4);
        assert_eq!(n1, ModP::new(6));

        let mut n2 = ModP::new(3);
        n2 -= 4;
        assert_eq!(n2, ModP::new(6));
    }

    #[test]
    fn test_sub_assign_avoiding_overflow() {
        unsafe { ModP::set_mod(7).unwrap(); }
        let mut n = ModP::new(5);
        n -= u64::max_value();
        assert_eq!(n, ModP::new(4));
    }

    #[test]
    fn test_mul() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::new(5) * ModP::new(5), ModP::new(4));
        assert_eq!(ModP::new(5) * 5, ModP::new(4));
        assert_eq!(5 * ModP::new(5), ModP::new(4));
    }

    #[test]
    fn test_mul_avoiding_overflow() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::new(5) * u64::max_value(), ModP::new(5));
        assert_eq!(u64::max_value() * ModP::new(5), ModP::new(5))
    }

    #[test]
    fn test_mul_assign() {
        unsafe { ModP::set_mod(7).unwrap(); }

        let mut n1 = ModP::new(5);
        n1 *= ModP::new(5);
        assert_eq!(n1, ModP::new(4));

        let mut n2 = ModP::new(5);
        n2 *= 5;
        assert_eq!(n2, ModP::new(4));
    }

    #[test]
    fn test_mul_assign_avoiding_overflow() {
        unsafe { ModP::set_mod(7).unwrap(); }
        let mut n = ModP::new(5);
        n *= u64::max_value();
        assert_eq!(n, ModP::new(5));
    }

    #[test]
    fn test_div() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::new(3) / ModP::new(4), ModP::new(6));
        assert_eq!(ModP::new(3) / 4, ModP::new(6));
        assert_eq!(3 / ModP::new(4), ModP::new(6));
    }

    #[test]
    fn test_div_assign() {
        unsafe { ModP::set_mod(7).unwrap(); }

        let mut n1 = ModP::new(3);
        n1 /= ModP::new(4);
        assert_eq!(n1, ModP::new(6));

        let mut n2 = ModP::new(3);
        n2 /= 4;
        assert_eq!(n2, ModP::new(6));
    }

    #[test]
    fn test_sum() {
        unsafe { ModP::set_mod(7).unwrap(); }
        let seq: Vec<ModP> = (1..=6).map(|n| ModP::new(n)).collect();
        assert_eq!(seq.iter().sum::<ModP>(), ModP::new(0));
        assert_eq!(seq.into_iter().sum::<ModP>(), ModP::new(0));
    }

    #[test]
    fn test_product() {
        unsafe { ModP::set_mod(7).unwrap(); }
        let seq: Vec<ModP> = (1..=6).map(|n| ModP::new(n)).collect();
        assert_eq!(seq.iter().product::<ModP>(), ModP::new(6));
        assert_eq!(seq.into_iter().product::<ModP>(), ModP::new(6));
    }

    #[test]
    fn test_read() {
        unsafe { ModP::set_mod(7).unwrap(); }
        assert_eq!(ModP::read_words(&["10"]), Ok(ModP::new(3)));
    }
}
