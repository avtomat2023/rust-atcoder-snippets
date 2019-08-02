//! Arithmetics modulo a prime number.

use num::{WithZero, WithOne, Numeric};

#[snippet = "modp"]
pub type ModPBase = u64;

/// The modulus which is a prime number.
///
/// In the contest, change the value of this constant.
/// Typically, the value is `1_000_000_007`.
#[snippet = "modp"]
pub const MODULUS: ModPBase = 7;

/// A number whose arithmetics is carried modulo `MODULUS`.
#[snippet = "modp"]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ModP {
    base: ModPBase
}

#[snippet = "modp"]
impl ModP {
    /// Create a number.
    pub fn new(n: ModPBase) -> ModP {
        if !cfg!(test) {
            assert!(MODULUS != 7, "Set const MODULUS to the value provided by the problem.");
        }
        ModP { base: n % MODULUS }
    }

    /// Create a number without taking remainder by `MODULUS`.
    ///
    /// If `n >= MODULUS`, the correctness of arithmetics is not guaranteed.
    pub unsafe fn new_unchecked(n: ModPBase) -> ModP {
        ModP { base: n }
    }

    /// Returns a `ModPBase` satisfying `0 <= x < MODULUS`.
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
        self.pow(MODULUS - 2)
    }
}

/// Shorthand of `ModP::new(x)`.
#[snippet = "modp"]
pub fn modp(x: u64) -> ModP {
    ModP::new(x)
}

#[snippet = "modp"]
impl std::fmt::Display for ModP {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.base())
    }
}

#[snippet = "modp"]
impl std::fmt::Debug for ModP {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} mod P", self.base())
    }
}

#[snippet = "modp"]
impl PartialEq<ModPBase> for ModP {
    fn eq(&self, other: &ModPBase) -> bool {
        self.base() == other % MODULUS
    }
}

#[snippet = "modp"]
impl PartialEq<ModP> for ModPBase {
    fn eq(&self, other: &ModP) -> bool {
        self % MODULUS == other.base() % MODULUS
    }
}

#[snippet = "modp"]
impl std::ops::Add for ModP {
    type Output = ModP;

    fn add(self, rhs: ModP) -> ModP {
        ModP { base: (self.base() + rhs.base() % MODULUS) % MODULUS }
    }
}

#[snippet = "modp"]
impl std::ops::Add<ModPBase> for ModP {
    type Output = ModP;

    fn add(self, rhs: ModPBase) -> ModP {
        self + ModP::new(rhs)
    }
}

#[snippet = "modp"]
impl std::ops::Add<ModP> for ModPBase {
    type Output = ModP;

    fn add(self, rhs: ModP) -> ModP {
        ModP::new(self) + rhs.base()
    }
}

#[snippet = "modp"]
impl std::ops::AddAssign for ModP {
    fn add_assign(&mut self, rhs: ModP) {
        *self = *self + rhs
    }
}

#[snippet = "modp"]
impl std::ops::AddAssign<ModPBase> for ModP {
    fn add_assign(&mut self, rhs: ModPBase) {
        *self = *self + ModP::new(rhs)
    }
}

#[snippet = "modp"]
impl std::ops::Neg for ModP {
    type Output = ModP;

    fn neg(self) -> ModP {
        ModP::new(MODULUS - self.base())
    }
}

#[snippet = "modp"]
impl std::ops::Sub for ModP {
    type Output = ModP;

    fn sub(self, rhs: ModP) -> ModP {
        self + (-rhs)
    }
}

#[snippet = "modp"]
impl std::ops::Sub<ModPBase> for ModP {
    type Output = ModP;

    fn sub(self, rhs: ModPBase) -> ModP {
        self - ModP::new(rhs)
    }
}

#[snippet = "modp"]
impl std::ops::Sub<ModP> for ModPBase {
    type Output = ModP;

    fn sub(self, rhs: ModP) -> ModP {
        ModP::new(self) - rhs
    }
}

#[snippet = "modp"]
impl std::ops::SubAssign for ModP {
    fn sub_assign(&mut self, rhs: ModP) {
        *self = *self - rhs;
    }
}

#[snippet = "modp"]
impl std::ops::SubAssign<ModPBase> for ModP {
    fn sub_assign(&mut self, rhs: ModPBase) {
        *self = *self - ModP::new(rhs)
    }
}

#[snippet = "modp"]
impl std::ops::Mul for ModP {
    type Output = ModP;

    fn mul(self, rhs: ModP) -> ModP {
        ModP { base: self.base() * (rhs.base() % MODULUS) % MODULUS }
    }
}

#[snippet = "modp"]
impl std::ops::Mul<ModPBase> for ModP {
    type Output = ModP;

    fn mul(self, rhs: ModPBase) -> ModP {
        self * ModP::new(rhs)
    }
}

#[snippet = "modp"]
impl std::ops::Mul<ModP> for ModPBase {
    type Output = ModP;

    fn mul(self, rhs: ModP) -> ModP {
        ModP::new(self) * rhs.base()
    }
}

#[snippet = "modp"]
impl std::ops::MulAssign for ModP {
    fn mul_assign(&mut self, rhs: ModP) {
        *self = *self * rhs
    }
}

#[snippet = "modp"]
impl std::ops::MulAssign<ModPBase> for ModP {
    fn mul_assign(&mut self, rhs: ModPBase) {
        *self = *self * ModP::new(rhs)
    }
}

#[snippet = "modp"]
impl std::ops::Div for ModP {
    type Output = ModP;

    fn div(self, rhs: ModP) -> ModP {
        self * rhs.inv()
    }
}

#[snippet = "modp"]
impl std::ops::Div<ModPBase> for ModP {
    type Output = ModP;

    fn div(self, rhs: ModPBase) -> ModP {
        self * ModP::new(rhs).inv()
    }
}

#[snippet = "modp"]
impl std::ops::Div<ModP> for ModPBase {
    type Output = ModP;

    fn div(self, rhs: ModP) -> ModP {
        ModP::new(self) * rhs.inv()
    }
}

#[snippet = "modp"]
impl std::ops::DivAssign for ModP {
    fn div_assign(&mut self, rhs: ModP) {
        *self = *self / rhs;
    }
}

#[snippet = "modp"]
impl std::ops::DivAssign<ModPBase> for ModP {
    fn div_assign(&mut self, rhs: ModPBase) {
        *self = *self / ModP::new(rhs)
    }
}

#[snippet = "modp"] forward_ref_binop!(impl Add, add for ModP, ModP);
#[snippet = "modp"] forward_ref_binop!(impl Add, add for ModP, ModPBase);
#[snippet = "modp"] forward_ref_binop!(impl Add, add for ModPBase, ModP);
#[snippet = "modp"] forward_ref_op_assign!(impl AddAssign, add_assign for ModP, ModP);
#[snippet = "modp"] forward_ref_op_assign!(impl AddAssign, add_assign for ModP, ModPBase);

#[snippet = "modp"] forward_ref_unop!(impl Neg, neg for ModP);

#[snippet = "modp"] forward_ref_binop!(impl Sub, sub for ModP, ModP);
#[snippet = "modp"] forward_ref_binop!(impl Sub, sub for ModP, ModPBase);
#[snippet = "modp"] forward_ref_binop!(impl Sub, sub for ModPBase, ModP);
#[snippet = "modp"] forward_ref_op_assign!(impl SubAssign, sub_assign for ModP, ModP);
#[snippet = "modp"] forward_ref_op_assign!(impl SubAssign, sub_assign for ModP, ModPBase);

#[snippet = "modp"] forward_ref_binop!(impl Mul, mul for ModP, ModP);
#[snippet = "modp"] forward_ref_binop!(impl Mul, mul for ModP, ModPBase);
#[snippet = "modp"] forward_ref_binop!(impl Mul, mul for ModPBase, ModP);
#[snippet = "modp"] forward_ref_op_assign!(impl MulAssign, mul_assign for ModP, ModP);
#[snippet = "modp"] forward_ref_op_assign!(impl MulAssign, mul_assign for ModP, ModPBase);

#[snippet = "modp"] forward_ref_binop!(impl Div, div for ModP, ModP);
#[snippet = "modp"] forward_ref_binop!(impl Div, div for ModP, ModPBase);
#[snippet = "modp"] forward_ref_binop!(impl Div, div for ModPBase, ModP);
#[snippet = "modp"] forward_ref_op_assign!(impl DivAssign, div_assign for ModP, ModP);
#[snippet = "modp"] forward_ref_op_assign!(impl DivAssign, div_assign for ModP, ModPBase);

#[snippet = "modp"]
impl WithZero for ModP {
    fn zero() -> ModP {
        unsafe { ModP::new_unchecked(0) }
    }
}

#[snippet = "modp"]
impl WithOne for ModP {
    fn one() -> ModP {
        unsafe { ModP::new_unchecked(1) }
    }
}

#[snippet = "modp"]
impl Numeric for ModP {}

#[snippet = "modp"]
impl std::iter::Sum for ModP {
    fn sum<I: Iterator<Item=ModP>>(iter: I) -> ModP {
        let mut ans = 0;
        for n in iter {
            ans += n.base();
        }
        ModP::new(ans)
    }
}

#[snippet = "modp"]
impl<'a> std::iter::Sum<&'a ModP> for ModP {
    fn sum<I: Iterator<Item=&'a ModP>>(iter: I) -> ModP {
        let mut ans = 0;
        for n in iter {
            ans += n.base();
        }
        ModP::new(ans)
    }
}

#[snippet = "modp"]
impl std::iter::Product for ModP {
    fn product<I: Iterator<Item=ModP>>(iter: I) -> ModP {
        let mut ans = ModP::one();
        for n in iter {
            ans *= n;
        }
        ans
    }
}

#[snippet = "modp"]
impl<'a> std::iter::Product<&'a ModP> for ModP {
    fn product<I: Iterator<Item=&'a ModP>>(iter: I) -> ModP {
        let mut ans = ModP::one();
        for &n in iter {
            ans *= n;
        }
        ans
    }
}

use read::{Readable, Words};

#[snippet = "modp"]
readable!(ModP, 1, |ws| ModP::new(ws[0].read::<u64>()));

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        assert_eq!(ModP::new(3), ModP::new(10));
        assert_eq!(modp(3), modp(10));
    }

    #[test]
    fn test_pow() {
        let zero = ModP::new(0);
        assert_eq!(zero.pow(0), ModP::new(1));
        assert_eq!(zero.pow(1), ModP::new(0));
        assert_eq!(zero.pow(u64::max_value()), ModP::new(0));

        let n = ModP::new(3);
        assert_eq!(n.pow(0), ModP::new(1));
        assert_eq!(n.pow(1), ModP::new(3));
        assert_eq!(n.pow(2), ModP::new(2));
        assert_eq!(n.pow(3), ModP::new(6));
        assert_eq!(n.pow(u64::max_value()), ModP::new(6));
    }

    #[test]
    fn test_inv() {
        assert_eq!(ModP::new(1).inv(), ModP::new(1));
        assert_eq!(ModP::new(2).inv(), ModP::new(4));
        assert_eq!(ModP::new(3).inv(), ModP::new(5));
        assert_eq!(ModP::new(4).inv(), ModP::new(2));
        assert_eq!(ModP::new(5).inv(), ModP::new(3));
        assert_eq!(ModP::new(6).inv(), ModP::new(6));
    }

    #[test]
    fn test_partial_eq() {
        assert_eq!(ModP::new(3), 10);
        assert_eq!(ModP::new(10), 3);
        assert_eq!(3, ModP::new(10));
        assert_eq!(10, ModP::new(3));
    }

    #[test]
    fn test_add() {
        assert_eq!(ModP::new(5) + ModP::new(5), ModP::new(3));
        assert_eq!(ModP::new(5) + &ModP::new(5), ModP::new(3));
        assert_eq!(&ModP::new(5) + ModP::new(5), ModP::new(3));
        assert_eq!(&ModP::new(5) + &ModP::new(5), ModP::new(3));
        assert_eq!(ModP::new(5) + 5, ModP::new(3));
        assert_eq!(ModP::new(5) + &5, ModP::new(3));
        assert_eq!(&ModP::new(5) + 5, ModP::new(3));
        assert_eq!(&ModP::new(5) + &5, ModP::new(3));
        assert_eq!(5 + ModP::new(5), ModP::new(3));
        assert_eq!(5 + &ModP::new(5), ModP::new(3));
        assert_eq!(&5 + ModP::new(5), ModP::new(3));
        assert_eq!(&5 + &ModP::new(5), ModP::new(3));
    }

    #[test]
    fn test_add_avoiding_overflow() {
        assert_eq!(ModP::new(5) + u64::max_value(), ModP::new(6));
        assert_eq!(u64::max_value() + ModP::new(5), ModP::new(6))
    }

    #[test]
    fn test_add_assign() {
        let mut n1 = ModP::new(5);
        n1 += ModP::new(5);
        assert_eq!(n1, ModP::new(3));

        let mut n1_for_ref = ModP::new(5);
        n1_for_ref += &ModP::new(5);
        assert_eq!(n1_for_ref, ModP::new(3));

        let mut n2 = ModP::new(5);
        n2 += 5;
        assert_eq!(n2, ModP::new(3));

        let mut n2_for_ref = ModP::new(5);
        n2_for_ref += &5;
        assert_eq!(n2_for_ref, ModP::new(3));
    }

    #[test]
    fn test_add_assign_avoiding_overflow() {
        let mut n = ModP::new(5);
        n += u64::max_value();
        assert_eq!(n, ModP::new(6));
    }

    #[test]
    fn test_neg() {
        assert_eq!(-ModP::new(3), ModP::new(4));
        assert_eq!(-(&ModP::new(3)), ModP::new(4));
        assert_eq!(-ModP::new(0), ModP::new(0));
        assert_eq!(-(&ModP::new(0)), ModP::new(0));
    }

    #[test]
    fn test_sub() {
        assert_eq!(ModP::new(3) - ModP::new(4), ModP::new(6));
        assert_eq!(ModP::new(3) - &ModP::new(4), ModP::new(6));
        assert_eq!(&ModP::new(3) - ModP::new(4), ModP::new(6));
        assert_eq!(&ModP::new(3) - &ModP::new(4), ModP::new(6));
        assert_eq!(ModP::new(3) - 4, ModP::new(6));
        assert_eq!(ModP::new(3) - &4, ModP::new(6));
        assert_eq!(&ModP::new(3) - 4, ModP::new(6));
        assert_eq!(&ModP::new(3) - &4, ModP::new(6));
        assert_eq!(3 - ModP::new(4), ModP::new(6));
        assert_eq!(3 - &ModP::new(4), ModP::new(6));
        assert_eq!(&3 - ModP::new(4), ModP::new(6));
        assert_eq!(&3 - &ModP::new(4), ModP::new(6));
    }

    #[test]
    fn test_sub_avoiding_overflow() {
        assert_eq!(ModP::new(5) - u64::max_value(), ModP::new(4));
    }

    #[test]
    fn test_sub_assign() {
        let mut n1 = ModP::new(3);
        n1 -= ModP::new(4);
        assert_eq!(n1, ModP::new(6));

        let mut n1_for_ref = ModP::new(3);
        n1_for_ref -= &ModP::new(4);
        assert_eq!(n1_for_ref, ModP::new(6));

        let mut n2 = ModP::new(3);
        n2 -= 4;
        assert_eq!(n2, ModP::new(6));

        let mut n2_for_ref = ModP::new(3);
        n2_for_ref -= &4;
        assert_eq!(n2_for_ref, ModP::new(6));
    }

    #[test]
    fn test_sub_assign_avoiding_overflow() {
        let mut n = ModP::new(5);
        n -= u64::max_value();
        assert_eq!(n, ModP::new(4));
    }

    #[test]
    fn test_mul() {
        assert_eq!(ModP::new(5) * ModP::new(5), ModP::new(4));
        assert_eq!(ModP::new(5) * &ModP::new(5), ModP::new(4));
        assert_eq!(&ModP::new(5) * ModP::new(5), ModP::new(4));
        assert_eq!(&ModP::new(5) * &ModP::new(5), ModP::new(4));
        assert_eq!(ModP::new(5) * 5, ModP::new(4));
        assert_eq!(ModP::new(5) * &5, ModP::new(4));
        assert_eq!(&ModP::new(5) * 5, ModP::new(4));
        assert_eq!(&ModP::new(5) * &5, ModP::new(4));
        assert_eq!(5 * ModP::new(5), ModP::new(4));
        assert_eq!(5 * &ModP::new(5), ModP::new(4));
        assert_eq!(&5 * ModP::new(5), ModP::new(4));
        assert_eq!(&5 * &ModP::new(5), ModP::new(4));
    }

    #[test]
    fn test_mul_avoiding_overflow() {
        assert_eq!(ModP::new(5) * u64::max_value(), ModP::new(5));
        assert_eq!(u64::max_value() * ModP::new(5), ModP::new(5))
    }

    #[test]
    fn test_mul_assign() {
        let mut n1 = ModP::new(5);
        n1 *= ModP::new(5);
        assert_eq!(n1, ModP::new(4));

        let mut n1_for_ref = ModP::new(5);
        n1_for_ref *= &ModP::new(5);
        assert_eq!(n1_for_ref, ModP::new(4));

        let mut n2 = ModP::new(5);
        n2 *= 5;
        assert_eq!(n2, ModP::new(4));

        let mut n2_for_ref = ModP::new(5);
        n2_for_ref *= &5;
        assert_eq!(n2_for_ref, ModP::new(4));
    }

    #[test]
    fn test_mul_assign_avoiding_overflow() {
        let mut n = ModP::new(5);
        n *= u64::max_value();
        assert_eq!(n, ModP::new(5));
    }

    #[test]
    fn test_div() {
        assert_eq!(ModP::new(3) / ModP::new(4), ModP::new(6));
        assert_eq!(ModP::new(3) / &ModP::new(4), ModP::new(6));
        assert_eq!(&ModP::new(3) / ModP::new(4), ModP::new(6));
        assert_eq!(&ModP::new(3) / &ModP::new(4), ModP::new(6));
        assert_eq!(ModP::new(3) / 4, ModP::new(6));
        assert_eq!(ModP::new(3) / &4, ModP::new(6));
        assert_eq!(&ModP::new(3) / 4, ModP::new(6));
        assert_eq!(&ModP::new(3) / &4, ModP::new(6));
        assert_eq!(3 / ModP::new(4), ModP::new(6));
        assert_eq!(3 / &ModP::new(4), ModP::new(6));
        assert_eq!(&3 / ModP::new(4), ModP::new(6));
        assert_eq!(&3 / &ModP::new(4), ModP::new(6));
    }

    #[test]
    fn test_div_assign() {
        let mut n1 = ModP::new(3);
        n1 /= ModP::new(4);
        assert_eq!(n1, ModP::new(6));

        let mut n1_for_ref = ModP::new(3);
        n1_for_ref /= &ModP::new(4);
        assert_eq!(n1_for_ref, ModP::new(6));

        let mut n2 = ModP::new(3);
        n2 /= 4;
        assert_eq!(n2, ModP::new(6));

        let mut n2_for_ref = ModP::new(3);
        n2_for_ref /= &4;
        assert_eq!(n2_for_ref, ModP::new(6));
    }

    #[test]
    fn test_sum() {
        let seq: Vec<ModP> = (1..=6).map(|n| ModP::new(n)).collect();
        assert_eq!(seq.iter().sum::<ModP>(), ModP::new(0));
        assert_eq!(seq.into_iter().sum::<ModP>(), ModP::new(0));
    }

    #[test]
    fn test_product() {
        let seq: Vec<ModP> = (1..=6).map(|n| ModP::new(n)).collect();
        assert_eq!(seq.iter().product::<ModP>(), ModP::new(6));
        assert_eq!(seq.into_iter().product::<ModP>(), ModP::new(6));
    }

    #[test]
    fn test_read() {
        assert_eq!(ModP::read_words(&["10"]), Ok(ModP::new(3)));
    }
}
