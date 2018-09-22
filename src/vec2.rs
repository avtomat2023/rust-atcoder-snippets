//! 2D geometric vector.
//!
//! # Example
//!
//! Solves [AtCoder Beginner Contest 108 Problem B](https://abc108.contest.atcoder.jp/tasks/abc108_b).
//!
//! ```no_run
//! # #[macro_use] extern crate atcoder_snippets;
//! # use::atcoder_snippets::read::*;
//! # use::atcoder_snippets::vec2::*;
//! #
//! // Use `read` and `vec2` snippet.
//!
//! fn main() {
//!     read!(point1 = Vec2<i16>, point2 = Vec2<i16>);
//!     let delta = point2 - point1;
//!     let delta_rotated = Vec2::new(-delta.y, delta.x);
//!     println!("{} {}", point2 + delta_rotated, point1 + delta_rotated);
//! }
//! ```


#[snippet = "vec2"]
use std::ops::{Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Div, DivAssign};
#[snippet = "vec2"]
use std::fmt::{self, Display, Formatter};

#[snippet = "vec2"]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Vec2<T> {
    pub x: T,
    pub y: T
}

#[snippet = "vec2"]
impl<T> Vec2<T> {
    pub fn new(x: T, y: T) -> Vec2<T> {
        Vec2 { x: x, y: y }
    }
}

#[snippet = "vec2"]
impl<T: Display> Display for Vec2<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{} {}", self.x, self.y)
    }
}

#[snippet = "vec2"]
impl<S, T: Add<S>> Add<Vec2<S>> for Vec2<T> {
    type Output = Vec2<T::Output>;

    fn add(self, rhs: Vec2<S>) -> Self::Output {
        Vec2::new(self.x + rhs.x, self.y + rhs.y)
    }
}

#[snippet = "vec2"]
impl<S, T: AddAssign<S>> AddAssign<Vec2<S>> for Vec2<T> {
    fn add_assign(&mut self, rhs: Vec2<S>) {
        self.x += rhs.x;
        self.y += rhs.y;
    }
}

#[snippet = "vec2"]
impl<S, T: Sub<S>> Sub<Vec2<S>> for Vec2<T> {
    type Output = Vec2<T::Output>;

    fn sub(self, rhs: Vec2<S>) -> Self::Output {
        Vec2::new(self.x - rhs.x, self.y - rhs.y)
    }
}

#[snippet = "vec2"]
impl<S, T: SubAssign<S>> SubAssign<Vec2<S>> for Vec2<T> {
    fn sub_assign(&mut self, rhs: Vec2<S>) {
        self.x -= rhs.x;
        self.y -= rhs.y;
    }
}

#[snippet = "vec2"]
impl<T: Neg> Neg for Vec2<T> {
    type Output = Vec2<T::Output>;

    fn neg(self) -> Self::Output {
        Vec2::new(-self.x, -self.y)
    }
}

#[snippet = "vec2"]
macro_rules! impl_mul_vec2 {
    ( $($t: ty)* ) => { $(
        impl Mul<Vec2<$t>> for $t {
            type Output = Vec2<<$t as Mul>::Output>;

            fn mul(self, rhs: Vec2<$t>) -> Self::Output {
                Vec2::new(self * rhs.x, self * rhs.y)
            }
        }
    )* }
}

#[snippet = "vec2"]
impl_mul_vec2!(i8 u8 i16 u16 i32 u32 i64 u64 f32 f64);

// Somehow this code doesn't compile
// #[snippet = "vec2"]
// impl<S, T: Copy + Mul<S>> Mul<Vec2<S>> for T {
//     type Output = Vec2<T::Output>;
//
//     fn mul(self, rhs: Vec2<S>) -> Self::Output {
//         Vec2::new(self * rhs.x, self * rhs.y)
//     }
// }

#[snippet = "vec2"]
impl<S: Copy, T: Mul<S>> Mul<S> for Vec2<T> {
    type Output = Vec2<T::Output>;

    fn mul(self, rhs: S) -> Self::Output {
        Vec2::new(self.x * rhs, self.y * rhs)
    }
}

#[snippet = "vec2"]
impl<S: Copy, T: MulAssign<S>> MulAssign<S> for Vec2<T> {
    fn mul_assign(&mut self, rhs: S) {
        self.x *= rhs;
        self.y *= rhs;
    }
}

#[snippet = "vec2"]
impl<S: Copy, T: Div<S>> Div<S> for Vec2<T> {
    type Output = Vec2<T::Output>;

   fn div(self, rhs: S) -> Self::Output {
        Vec2::new(self.x / rhs, self.y / rhs)
    }
}

#[snippet = "vec2"]
impl<S: Copy, T: DivAssign<S>> DivAssign<S> for Vec2<T> {
    fn div_assign(&mut self, rhs: S) {
        self.x /= rhs;
        self.y /= rhs;
    }
}

use read::FromFragments;

#[snippet = "vec2"]
impl<T: FromFragments> FromFragments for Vec2<T> {
    fn fragments_count() -> usize {
        T::fragments_count() * 2
    }

    fn from_fragments(fragments: &[&str]) -> Result<Vec2<T>, String> {
        let n = T::fragments_count();
        Ok(Vec2::new(T::from_fragments(&fragments[..n])?,
                     T::from_fragments(&fragments[n..])?))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_add() {
        let v1 = Vec2::new(1, 2);
        let v2 = Vec2::new(10, 20);
        assert_eq!(v1 + v2, Vec2::new(11, 22));
    }

    #[test]
    fn test_add_assign() {
        let mut v = Vec2::new(1, 2);
        v += Vec2::new(10, 20);
        assert_eq!(v, Vec2::new(11, 22));
    }

    #[test]
    fn test_sub() {
        let v1 = Vec2::new(1, 2);
        let v2 = Vec2::new(10, 20);
        assert_eq!(v1 - v2, Vec2::new(-9, -18));
    }

    #[test]
    fn test_sub_assign() {
        let mut v = Vec2::new(1, 2);
        v -= Vec2::new(10, 20);
        assert_eq!(v, Vec2::new(-9, -18));
    }

    #[test]
    fn test_neg() {
        let v = Vec2::new(1, 2);
        assert_eq!(-v, Vec2::new(-1, -2));
    }

    #[test]
    fn test_mul() {
        let v = Vec2::new(1, 2);
        assert_eq!(10 * v, Vec2::new(10, 20));
        assert_eq!(v * 10, Vec2::new(10, 20));
    }

    #[test]
    fn test_mul_assign() {
        let mut v = Vec2::new(1, 2);
        v *= 10;
        assert_eq!(v, Vec2::new(10, 20));
    }

    #[test]
    fn test_div() {
        let v = Vec2::new(10, 20);
        assert_eq!(v / 3, Vec2::new(3, 6));
    }

    #[test]
    fn test_div_assign() {
        let mut v = Vec2::new(10, 20);
        v /= 3;
        assert_eq!(v, Vec2::new(3, 6));
    }

    #[test]
    fn test_from_fragments() {
        let v = Vec2::<i32>::from_fragments(&["1", "2"]);
        assert_eq!(v, Ok(Vec2::new(1, 2)));
    }
}
