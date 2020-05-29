//! 2D Geometric calculations.

use crate::option::BoolExt;
use crate::vec::Vec2;
use crate::xorshift::Xorshift;

// BEGIN SNIPPET geometry DEPENDS ON option vec xorshift

pub const GEOMETRY_EPSILON: f64 = 1e-10;

mod geometry_internal {
    use super::*;

    /// Returns (center, square of radius)
    pub fn circle_from_3_points(
        p1: Vec2<f64>, p2: Vec2<f64>, p3: Vec2<f64>
    ) -> Option<(Vec2<f64>, f64)> {
        // http://www.ambrsoft.com/trigocalc/circle3d.htm
        let det_denom = p1.x * (p2.y-p3.y) - p1.y * (p2.x-p3.x) + p2.x*p3.y - p3.x*p2.y;
        if det_denom.abs() <= GEOMETRY_EPSILON * GEOMETRY_EPSILON {
            return None;
        }

        let n1 = p1.square_norm();
        let n2 = p2.square_norm();
        let n3 = p3.square_norm();
        let det_x = n1 * (p2.y-p3.y) + n2 * (p3.y-p1.y) + n3 * (p1.y-p2.y);
        let det_y = n1 * (p3.x-p2.x) + n2 * (p1.x-p3.x) + n3 * (p2.x-p1.x);
        let x = det_x / (2.0 * det_denom);
        let y = det_y / (2.0 * det_denom);

        let center = Vec2::new(x, y);
        Some((center, (p1 - center).square_norm()))
    }

    /// Returns (center, square of radius)
    pub fn smallest_enclosing_circle_with_1_point(
        points: &[Vec2<f64>], p1: Vec2<f64>
    ) -> (Vec2<f64>, f64) {
        (0..points.len()).fold((p1, 0.0), |(center, square_radius), i| {
            let new_square_radius = (points[i] - center).square_norm();
            if new_square_radius <= square_radius {
                (center, square_radius)
            } else {
                smallest_enclosing_circle_with_2_points(&points[..i], p1, points[i])
            }
        })
    }

    /// Returns (center, square of radius)
    pub fn smallest_enclosing_circle_with_2_points(
        points: &[Vec2<f64>], p1: Vec2<f64>, p2: Vec2<f64>
    ) -> (Vec2<f64>, f64) {
        let center = (p1 + p2) / 2.0;
        let square_radius = (p1 - center).square_norm();
        points.iter().fold((center, square_radius), |(center, square_radius), &p| {
            let new_square_radius = (p - center).square_norm();
            if new_square_radius <= square_radius {
                (center, square_radius)
            } else {
                circle_from_3_points(p1, p2, p).unwrap_or((center, square_radius))
            }
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Circle {
    center: Vec2<f64>,
    radius: f64
}

impl Circle {
    /// Creates a circle from center and radius.
    ///
    /// If radius is smaller than 0.0, returns `None`.
    #[allow(unstable_name_collisions)]
    pub fn new(center: Vec2<f64>, radius: f64) -> Option<Circle> {
        (radius >= 0.0).then(Circle { center, radius })
    }

    /// Creates a circle without checking that radius is at least 0.0.
    pub unsafe fn new_unchecked(center: Vec2<f64>, radius: f64) -> Circle {
        Circle { center, radius }
    }

    /// Center of circle.
    pub fn center(&self) -> Vec2<f64> {
        self.center
    }

    /// Radius of circle.
    pub fn radius(&self) -> f64 {
        self.radius
    }

    /// Gets the circle passing througth the given 3 points.
    ///
    /// If at least 2 points are same or 3 points lies on a straight line, returns `None`.
    pub fn from_3_points(p1: Vec2<f64>, p2: Vec2<f64>, p3: Vec2<f64>) -> Option<Circle> {
        use geometry_internal::*;
        circle_from_3_points(p1, p2, p3).map(|(center, square_radius)| {
            unsafe { Circle::new_unchecked(center, square_radius.sqrt()) }
        })
    }

    /// Gets the smallest circle enclosing all the given points.
    ///
    /// If points are empty, returns `None`.
    ///
    /// The given slice of points are shuffled for randomizing input.
    /// The expectad time complexity is Θ(*n*), where *n* is the number of points.
    pub fn smallest_enclosing(points: &mut [Vec2<f64>]) -> Option<Circle> {
        use geometry_internal::*;

        if points.is_empty() {
            return None;
        }

        let mut rng = Xorshift::new();
        rng.shuffle(points);

        let (center, square_radius) = (1..points.len())
            .fold((points[0], 0.0), |(center, square_radius), i| {
                let new_square_radius = (center - points[i]).square_norm();
                if new_square_radius <= square_radius {
                    (center, square_radius)
                } else {
                    smallest_enclosing_circle_with_1_point(&points[..i], points[i])
                }
            });
        unsafe { Some(Circle::new_unchecked(center, square_radius.sqrt())) }
    }
}

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_circle_from_3_points() {
        let p00 = Vec2::new(0.0, 0.0);
        let p10 = Vec2::new(1.0, 0.0);
        let p20 = Vec2::new(2.0, 0.0);
        let p01 = Vec2::new(0.0, 1.0);
        assert!(Circle::from_3_points(p00, p00, p00).is_none());
        assert!(Circle::from_3_points(p00, p00, p10).is_none());
        assert!(Circle::from_3_points(p00, p10, p00).is_none());
        assert!(Circle::from_3_points(p10, p00, p00).is_none());
        assert!(Circle::from_3_points(p00, p10, p20).is_none());

        let actual = Circle::from_3_points(p00, p10, p01).unwrap();
        let expected = Circle::new(Vec2::new(0.5, 0.5), 0.5f64.sqrt()).unwrap();
        assert!((actual.center.x - expected.center.x).abs() < GEOMETRY_EPSILON);
        assert!((actual.center.y - expected.center.y).abs() < GEOMETRY_EPSILON);
        assert!((actual.radius - expected.radius).abs() < GEOMETRY_EPSILON);

        let p1 = Vec2::new(2.0, 6.0);
        let p2 = Vec2::new(-1.0, -3.0);
        let p3 = Vec2::new(4.0, -3.0);
        let actual = Circle::from_3_points(p1, p2, p3).unwrap();
        let expected = Circle::new(Vec2::new(1.5, 7.0/6.0), (425.0f64/18.0).sqrt()).unwrap();
        assert!((actual.center.x - expected.center.x).abs() < GEOMETRY_EPSILON);
        assert!((actual.center.y - expected.center.y).abs() < GEOMETRY_EPSILON);
        assert!((actual.radius - expected.radius).abs() < GEOMETRY_EPSILON);
    }
}
