//! 2D and 3D geometric vectors.
//!
//! # Example
//!
//! Solves [AtCoder Beginner Contest 108: Problem B - Ruined Square](https://abc108.contest.atcoder.jp/tasks/abc108_b).
//!
//! ```no_run
//! # #[macro_use] extern crate atcoder_snippets;
//! # use::atcoder_snippets::read::*;
//! # use::atcoder_snippets::vec::*;
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

use std;

// BEGIN SNIPPET vec

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Vec2<T> {
    pub x: T,
    pub y: T
}

impl<T> Vec2<T> {
    pub fn new(x: T, y: T) -> Vec2<T> {
        Vec2 { x: x, y: y }
    }

    // ABC130
    /// Inner product of vectors.
    pub fn inner(self, other: Vec2<T>) -> T
    where
        T: std::ops::Add<T, Output=T> + std::ops::Mul<T, Output=T>
    {
        self.x * other.x + self.y * other.y
    }
}

impl<T: std::fmt::Display> std::fmt::Display for Vec2<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} {}", self.x, self.y)
    }
}

impl<S, T: std::ops::Add<S>> std::ops::Add<Vec2<S>> for Vec2<T> {
    type Output = Vec2<T::Output>;

    fn add(self, rhs: Vec2<S>) -> Self::Output {
        Vec2::new(self.x + rhs.x, self.y + rhs.y)
    }
}

impl<S, T: std::ops::AddAssign<S>> std::ops::AddAssign<Vec2<S>> for Vec2<T> {
    fn add_assign(&mut self, rhs: Vec2<S>) {
        self.x += rhs.x;
        self.y += rhs.y;
    }
}

impl<S, T: std::ops::Sub<S>> std::ops::Sub<Vec2<S>> for Vec2<T> {
    type Output = Vec2<T::Output>;

    fn sub(self, rhs: Vec2<S>) -> Self::Output {
        Vec2::new(self.x - rhs.x, self.y - rhs.y)
    }
}

impl<S, T: std::ops::SubAssign<S>> std::ops::SubAssign<Vec2<S>> for Vec2<T> {
    fn sub_assign(&mut self, rhs: Vec2<S>) {
        self.x -= rhs.x;
        self.y -= rhs.y;
    }
}

impl<T: std::ops::Neg> std::ops::Neg for Vec2<T> {
    type Output = Vec2<T::Output>;

    fn neg(self) -> Self::Output {
        Vec2::new(-self.x, -self.y)
    }
}

macro_rules! impl_mul_vec2 {
    ( $($t: ty)* ) => { $(
        impl std::ops::Mul<Vec2<$t>> for $t {
            type Output = Vec2<<$t as std::ops::Mul>::Output>;

            fn mul(self, rhs: Vec2<$t>) -> Self::Output {
                Vec2::new(self * rhs.x, self * rhs.y)
            }
        }
    )* }
}

impl_mul_vec2!(i8 u8 i16 u16 i32 u32 i64 u64 f32 f64);

// Somehow this code doesn't compile
// #[snippet = "vec2"]
// impl<S, T: Copy + std::ops::Mul<S>> std::ops::Mul<Vec2<S>> for T {
//     type Output = Vec2<T::Output>;
//
//     fn mul(self, rhs: Vec2<S>) -> Self::Output {
//         Vec2::new(self * rhs.x, self * rhs.y)
//     }
// }

impl<S: Copy, T: std::ops::Mul<S>> std::ops::Mul<S> for Vec2<T> {
    type Output = Vec2<T::Output>;

    fn mul(self, rhs: S) -> Self::Output {
        Vec2::new(self.x * rhs, self.y * rhs)
    }
}

impl<S: Copy, T: std::ops::MulAssign<S>> std::ops::MulAssign<S> for Vec2<T> {
    fn mul_assign(&mut self, rhs: S) {
        self.x *= rhs;
        self.y *= rhs;
    }
}

impl<S: Copy, T: std::ops::Div<S>> std::ops::Div<S> for Vec2<T> {
    type Output = Vec2<T::Output>;

   fn div(self, rhs: S) -> Self::Output {
        Vec2::new(self.x / rhs, self.y / rhs)
    }
}

impl<S: Copy, T: std::ops::DivAssign<S>> std::ops::DivAssign<S> for Vec2<T> {
    fn div_assign(&mut self, rhs: S) {
        self.x /= rhs;
        self.y /= rhs;
    }
}

use read::Readable;

impl<T: Readable> Readable for Vec2<T> {
    type Output = Vec2<T::Output>;

    fn words_count() -> usize {
        T::words_count() * 2
    }

    fn read_words(words: &[&str]) -> Result<Vec2<T::Output>, String> {
        let n = T::words_count();
        Ok(Vec2::new(T::read_words(&words[..n])?,
                     T::read_words(&words[n..])?))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Vec3<T> {
    pub x: T,
    pub y: T,
    pub z: T
}

impl<T> Vec3<T> {
    pub fn new(x: T, y: T, z: T) -> Vec3<T> {
        Vec3 { x: x, y: y , z: z }
    }

    pub fn inner(self, other: Vec3<T>) -> T
    where
        T: std::ops::Add<T, Output=T> + std::ops::Mul<T, Output=T>
    {
        self.x * other.x + self.y * other.y + self.z * other.z
    }
}

impl<T: std::fmt::Display> std::fmt::Display for Vec3<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} {} {}", self.x, self.y, self.z)
    }
}

impl<S, T: std::ops::Add<S>> std::ops::Add<Vec3<S>> for Vec3<T> {
    type Output = Vec3<T::Output>;

    fn add(self, rhs: Vec3<S>) -> Self::Output {
        Vec3::new(self.x + rhs.x, self.y + rhs.y, self.z + rhs.z)
    }
}

impl<S, T: std::ops::AddAssign<S>> std::ops::AddAssign<Vec3<S>> for Vec3<T> {
    fn add_assign(&mut self, rhs: Vec3<S>) {
        self.x += rhs.x;
        self.y += rhs.y;
        self.z += rhs.z;
    }
}

impl<S, T: std::ops::Sub<S>> std::ops::Sub<Vec3<S>> for Vec3<T> {
    type Output = Vec3<T::Output>;

    fn sub(self, rhs: Vec3<S>) -> Self::Output {
        Vec3::new(self.x - rhs.x, self.y - rhs.y, self.z - rhs.z)
    }
}

impl<S, T: std::ops::SubAssign<S>> std::ops::SubAssign<Vec3<S>> for Vec3<T> {
    fn sub_assign(&mut self, rhs: Vec3<S>) {
        self.x -= rhs.x;
        self.y -= rhs.y;
        self.z -= rhs.z;
    }
}

impl<T: std::ops::Neg> std::ops::Neg for Vec3<T> {
    type Output = Vec3<T::Output>;

    fn neg(self) -> Self::Output {
        Vec3::new(-self.x, -self.y, -self.z)
    }
}

macro_rules! impl_mul_vec3 {
    ( $($t: ty)* ) => { $(
        impl std::ops::Mul<Vec3<$t>> for $t {
            type Output = Vec3<<$t as std::ops::Mul>::Output>;

            fn mul(self, rhs: Vec3<$t>) -> Self::Output {
                Vec3::new(self * rhs.x, self * rhs.y, self * rhs.z)
            }
        }
    )* }
}

impl_mul_vec3!(i8 u8 i16 u16 i32 u32 i64 u64 f32 f64);

// Somehow this code doesn't compile
// #[snippet = "vec3"]
// impl<S, T: Copy + std::ops::Mul<S>> std::ops::Mul<Vec3<S>> for T {
//     type Output = Vec3<T::Output>;
//
//     fn mul(self, rhs: Vec3<S>) -> Self::Output {
//         Vec3::new(self * rhs.x, self * rhs.y, self * rhs.z)
//     }
// }

impl<S: Copy, T: std::ops::Mul<S>> std::ops::Mul<S> for Vec3<T> {
    type Output = Vec3<T::Output>;

    fn mul(self, rhs: S) -> Self::Output {
        Vec3::new(self.x * rhs, self.y * rhs, self.z * rhs)
    }
}

impl<S: Copy, T: std::ops::MulAssign<S>> std::ops::MulAssign<S> for Vec3<T> {
    fn mul_assign(&mut self, rhs: S) {
        self.x *= rhs;
        self.y *= rhs;
        self.z *= rhs;
    }
}

impl<S: Copy, T: std::ops::Div<S>> std::ops::Div<S> for Vec3<T> {
    type Output = Vec3<T::Output>;

   fn div(self, rhs: S) -> Self::Output {
        Vec3::new(self.x / rhs, self.y / rhs, self.z / rhs)
    }
}

impl<S: Copy, T: std::ops::DivAssign<S>> std::ops::DivAssign<S> for Vec3<T> {
    fn div_assign(&mut self, rhs: S) {
        self.x /= rhs;
        self.y /= rhs;
        self.z /= rhs;
    }
}

impl<T: Readable> Readable for Vec3<T> {
    type Output = Vec3<T::Output>;

    fn words_count() -> usize {
        T::words_count() * 3
    }

    fn read_words(words: &[&str]) -> Result<Vec3<T::Output>, String> {
        let n = T::words_count();
        Ok(Vec3::new(T::read_words(&words[..n])?,
                     T::read_words(&words[n..2*n])?,
                     T::read_words(&words[2*n..])?))
    }
}

// END SNIPPET

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_vec2_inner() {
        let v1 = Vec2::new(1, 2);
        let v2 = Vec2::new(10, 20);
        assert_eq!(v1.inner(v2), 50);
    }

    #[test]
    fn test_vec2_add() {
        let v1 = Vec2::new(1, 2);
        let v2 = Vec2::new(10, 20);
        assert_eq!(v1 + v2, Vec2::new(11, 22));
    }

    #[test]
    fn test_vec2_add_assign() {
        let mut v = Vec2::new(1, 2);
        v += Vec2::new(10, 20);
        assert_eq!(v, Vec2::new(11, 22));
    }

    #[test]
    fn test_vec2_sub() {
        let v1 = Vec2::new(1, 2);
        let v2 = Vec2::new(10, 20);
        assert_eq!(v1 - v2, Vec2::new(-9, -18));
    }

    #[test]
    fn test_vec2_sub_assign() {
        let mut v = Vec2::new(1, 2);
        v -= Vec2::new(10, 20);
        assert_eq!(v, Vec2::new(-9, -18));
    }

    #[test]
    fn test_vec2_neg() {
        let v = Vec2::new(1, 2);
        assert_eq!(-v, Vec2::new(-1, -2));
    }

    #[test]
    fn test_vec2_mul() {
        let v = Vec2::new(1, 2);
        assert_eq!(10 * v, Vec2::new(10, 20));
        assert_eq!(v * 10, Vec2::new(10, 20));
    }

    #[test]
    fn test_vec2_mul_assign() {
        let mut v = Vec2::new(1, 2);
        v *= 10;
        assert_eq!(v, Vec2::new(10, 20));
    }

    #[test]
    fn test_vec2_div() {
        let v = Vec2::new(10, 20);
        assert_eq!(v / 3, Vec2::new(3, 6));
    }

    #[test]
    fn test_vec2_div_assign() {
        let mut v = Vec2::new(10, 20);
        v /= 3;
        assert_eq!(v, Vec2::new(3, 6));
    }

    #[test]
    fn test_vec2_read_words() {
        let v = Vec2::<i32>::read_words(&["1", "2"]);
        assert_eq!(v, Ok(Vec2::new(1, 2)));
    }

    #[test]
    fn test_vec3_inner() {
        let v1 = Vec3::new(1, 2, 3);
        let v2 = Vec3::new(10, 20, 30);
        assert_eq!(v1.inner(v2), 140);
    }

    #[test]
    fn test_vec3_add() {
        let v1 = Vec3::new(1, 2, 3);
        let v2 = Vec3::new(10, 20, 30);
        assert_eq!(v1 + v2, Vec3::new(11, 22, 33));
    }

    #[test]
    fn test_vec3_add_assign() {
        let mut v = Vec3::new(1, 2, 3);
        v += Vec3::new(10, 20, 30);
        assert_eq!(v, Vec3::new(11, 22, 33));
    }

    #[test]
    fn test_vec3_sub() {
        let v1 = Vec3::new(1, 2, 3);
        let v2 = Vec3::new(10, 20, 30);
        assert_eq!(v1 - v2, Vec3::new(-9, -18, -27));
    }

    #[test]
    fn test_vec3_sub_assign() {
        let mut v = Vec3::new(1, 2, 3);
        v -= Vec3::new(10, 20, 30);
        assert_eq!(v, Vec3::new(-9, -18, -27));
    }

    #[test]
    fn test_vec3_neg() {
        let v = Vec3::new(1, 2, 3);
        assert_eq!(-v, Vec3::new(-1, -2, -3));
    }

    #[test]
    fn test_vec3_mul() {
        let v = Vec3::new(1, 2, 3);
        assert_eq!(10 * v, Vec3::new(10, 20, 30));
        assert_eq!(v * 10, Vec3::new(10, 20, 30));
    }

    #[test]
    fn test_vec3_mul_assign() {
        let mut v = Vec3::new(1, 2, 3);
        v *= 10;
        assert_eq!(v, Vec3::new(10, 20, 30));
    }

    #[test]
    fn test_vec3_div() {
        let v = Vec3::new(10, 20, 30);
        assert_eq!(v / 3, Vec3::new(3, 6, 10));
    }

    #[test]
    fn test_vec3_div_assign() {
        let mut v = Vec3::new(10, 20, 30);
        v /= 3;
        assert_eq!(v, Vec3::new(3, 6, 10));
    }

    #[test]
    fn test_vec3_read_words() {
        let v = Vec3::<i32>::read_words(&["1", "2", "3"]);
        assert_eq!(v, Ok(Vec3::new(1, 2, 3)));
    }
}
