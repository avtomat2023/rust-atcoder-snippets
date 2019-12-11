//! Intervals on a number line.
//!
//! An interval is basically a tuple `(a, b)` guranteed that `a <= b`.
//! It represents a set of real number `x` satisfying `a <= x <= b`.
//!
//! This module offers useful algorithms such as
//! [merging intervals](trait.IntervalIterator.html#method.merge)
//! or tertiary search on an interval (not implemented yet.)

// TODO: method to check whether an interval is contained, and whether an interval is overwrapped

// BEGIN SNIPPET interval

/// Point on a number line.
pub trait IntervalEndpoint: Ord {}

impl IntervalEndpoint for i8 {}
impl IntervalEndpoint for u8 {}
impl IntervalEndpoint for i16 {}
impl IntervalEndpoint for u16 {}
impl IntervalEndpoint for i32 {}
impl IntervalEndpoint for u32 {}
impl IntervalEndpoint for i64 {}
impl IntervalEndpoint for u64 {}

/// Interval including endpoints.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Interval<T> {
    left: T,
    right: T
}

impl<T: IntervalEndpoint> Interval<T> {
    /// Creates an interval.
    ///
    /// If `right < left`, returns `None`.
    pub fn new(left: T, right: T) -> Option<Interval<T>> {
        if right < left {
            None
        } else {
            Some(Interval {
                left,
                right
            })
        }
    }

    pub fn from_tuple(endpoints: (T, T)) -> Option<Interval<T>> {
        Interval::new(endpoints.0, endpoints.1)
    }

    /// Gets the left endpoint.
    pub fn left(&self) -> &T {
        &self.left
    }

    /// Gets the right endpoint.
    pub fn right(&self) -> &T {
        &self.right
    }

    /// Moves out both endpoints.
    pub fn endpoints(self) -> (T, T) {
        (self.left, self.right)
    }

    /// Checks if the interals contains `point`.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::interval::*;
    /// let interval = Interval::new(0, 10).unwrap();
    /// assert!(interval.contains(&0));
    /// assert!(interval.contains(&5));
    /// assert!(interval.contains(&10));
    /// assert!(!interval.contains(&15));
    /// ```
    pub fn contains(&self, point: &T) -> bool {
        self.left() <= point && point <= self.right()
    }

    /// Length of the interval.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::interval::*;
    /// let interval = Interval::new(0, 10).unwrap();
    /// assert_eq!(interval.length(), 10);
    /// let point = Interval::new(0, 0).unwrap();
    /// assert_eq!(point.length(), 0);
    /// ```
    pub fn length(&self) -> T
    where
        T: Clone + for<'a> std::ops::Sub<&'a T, Output=T>
    {
        self.right().clone() - self.left()
    }
}

impl<T: IntervalEndpoint + std::fmt::Debug> std::fmt::Debug for Interval<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Interval({:?}, {:?})", &self.left, &self.right)
    }
}

/// Iterator yielding intervals.
pub trait IntervalIterator<T: IntervalEndpoint>: Sized + Iterator<Item=Interval<T>> {
    /// Creates an iterator yielding intervals, merging overwrapping intervals into one.
    ///
    /// The intervals are yielded in the ascending order.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::interval::*;
    /// extern crate rand;
    /// use rand::seq::SliceRandom;
    /// use rand::thread_rng;
    ///
    /// # fn main() {
    /// let mut intervals = vec![
    ///     (0, 1), (1, 2), (1, 3),
    ///     (4, 5), (5, 5),
    ///     (6, 7)
    /// ];
    /// intervals.shuffle(&mut thread_rng());
    ///
    /// let mut merged_intervals = intervals.into_iter()
    ///     .map(|itv| Interval::from_tuple(itv).unwrap())
    ///     .merge();
    /// assert_eq!(merged_intervals.next(), Some(Interval::new(0, 3).unwrap()));
    /// assert_eq!(merged_intervals.next(), Some(Interval::new(4, 5).unwrap()));
    /// assert_eq!(merged_intervals.next(), Some(Interval::new(6, 7).unwrap()));
    /// assert_eq!(merged_intervals.next(), None);
    /// # }
    /// ```
    ///
    /// # Time complexity
    ///
    /// A call of `merge` takes Θ(*n* log *n*) time, where `n` is the intervals contained by `self`.
    ///
    /// To iterate the returned iterator until exhausted, it takes Θ(*n*) time.
    /// It is irrelevant to the number of the intervals after merging.
    ///
    /// Calling `next` of the returned iterator takes O(*n*) time.
    ///
    /// The Algorithm is explained in [CP-Algorithm](https://cp-algorithms.com/geometry/length-of-segments-union.html).
    fn merge(self) -> IntervalMerge<T> {
        let mut points: Vec<(T, isize)> = Vec::new();
        for interval in self {
            let (left, right) = interval.endpoints();
            points.push((left, 1));
            points.push((right, -1));
        }
        points.sort_by(|(point1, d1), (point2, d2)| (point2, -d2).cmp(&(point1, -d1)));

        IntervalMerge { points }
    }
}

impl<T, I> IntervalIterator<T> for I
where
    T: IntervalEndpoint,
    I: Iterator<Item=Interval<T>>
{}

/// Iterator created by [`merge`](trait.IntervalIterator.html#method.merge) method.
pub struct IntervalMerge<T> {
    points: Vec<(T, isize)>
}

impl<T: IntervalEndpoint> Iterator for IntervalMerge<T> {
    type Item = Interval<T>;

    fn next(&mut self) -> Option<Interval<T>> {
        self.points.pop().map(|(leftmost, d_first)| {
            assert_eq!(d_first, 1);

            let mut count = 1;
            while let Some((point, d)) = self.points.pop() {
                count += d;
                if count == 0 {
                    return Interval::new(leftmost, point).unwrap()
                }
            }

            unreachable!()
        })
    }
}

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        assert!(Interval::new(0, 1).is_some());
        assert!(Interval::new(0, 0).is_some());
        assert!(Interval::new(1, 0).is_none());
    }

    #[test]
    fn test_length() {
        assert_eq!(Interval::new(0, 0).unwrap().length(), 0);
        assert_eq!(Interval::new(0, 1).unwrap().length(), 1);
        assert_eq!(Interval::new(10, 20).unwrap().length(), 10);
    }

    #[test]
    fn test_contains_for_point() {
        let point = Interval::new(1, 1).unwrap();
        assert!(!point.contains(&0));
        assert!( point.contains(&1));
        assert!(!point.contains(&2));
    }

    #[test]
    fn test_contains_for_interval() {
        let point = Interval::new(1, 3).unwrap();
        assert!(!point.contains(&0));
        assert!( point.contains(&1));
        assert!( point.contains(&2));
        assert!( point.contains(&3));
        assert!(!point.contains(&4));
    }

    fn assert_eq_after_merge(intervals: Vec<(i32, i32)>, expected: Vec<(i32, i32)>) {
        let merged: Vec<(i32, i32)> = intervals.iter()
            .cloned()
            .map(|(left, right)| Interval::new(left, right).unwrap())
            .merge()
            .map(|itv| (*itv.left(), *itv.right()))
            .collect();

        assert!(
            merged == expected,
            "merged intervals are not as expected
  merging: {:?},
   yields: {:?},
 expected: {:?}",
            intervals, merged, expected
        );
    }

    #[test]
    fn test_merge_empty() {
        assert_eq_after_merge(vec![], vec![]);
    }

    #[test]
    fn test_merge_one_point_or_one_interval() {
        assert_eq_after_merge(vec![(0, 0)], vec![(0, 0)]);
        assert_eq_after_merge(vec![(0, 1)], vec![(0, 1)]);
    }

    #[test]
    fn test_merge_two_points() {
        assert_eq_after_merge(
            vec![(0, 0), (0, 0)],
            vec![(0, 0)]
        );
        assert_eq_after_merge(
            vec![(0, 0), (1, 1)],
            vec![(0, 0), (1, 1)]
        );
    }

    #[test]
    fn test_merge_one_interval_and_one_point() {
        assert_eq_after_merge(
            vec![(0, 0), (1, 3)],
            vec![(0, 0), (1, 3)],
        );
        assert_eq_after_merge(
            vec![(1, 1), (1, 3)],
            vec![(1, 3)],
        );
        assert_eq_after_merge(
            vec![(2, 2), (1, 3)],
            vec![(1, 3)],
        );
        assert_eq_after_merge(
            vec![(3, 3), (1, 3)],
            vec![(1, 3)],
        );
        assert_eq_after_merge(
            vec![(4, 4), (1, 3)],
            vec![(1, 3), (4, 4)],
        );
    }

    #[test]
    fn test_merge_two_intervals() {
        // from a point left of the interval
        assert_eq_after_merge(
            vec![(2, 5), (0, 1)],
            vec![(0, 1), (2, 5)]
        );
        assert_eq_after_merge(
            vec![(2, 5), (0, 2)],
            vec![(0, 5)]
        );
        assert_eq_after_merge(
            vec![(2, 5), (0, 3)],
            vec![(0, 5)]
        );
        assert_eq_after_merge(
            vec![(2, 5), (0, 5)],
            vec![(0, 5)]
        );
        assert_eq_after_merge(
            vec![(2, 5), (0, 6)],
            vec![(0, 6)]
        );

        // from left endpoint
        assert_eq_after_merge(
            vec![(2, 5), (2, 3)],
            vec![(2, 5)]
        );
        assert_eq_after_merge(
            vec![(2, 5), (2, 5)],
            vec![(2, 5)]
        );
        assert_eq_after_merge(
            vec![(2, 5), (2, 6)],
            vec![(2, 6)]
        );

        // from a point in the interval
        assert_eq_after_merge(
            vec![(2, 5), (3, 4)],
            vec![(2, 5)]
        );
        assert_eq_after_merge(
            vec![(2, 5), (3, 5)],
            vec![(2, 5)]
        );
        assert_eq_after_merge(
            vec![(2, 5), (3, 6)],
            vec![(2, 6)]
        );

        // from the right endpoint
        assert_eq_after_merge(
            vec![(2, 5), (5, 6)],
            vec![(2, 6)]
        );

        // from a point right of the interval
        assert_eq_after_merge(
            vec![(2, 5), (6, 7)],
            vec![(2, 5), (6, 7)]
        );
    }

    #[test]
    fn test_merge_many_intervals() {
        // intervals:
        // 0-1-2-3-4-5-6-7-8-9-0-1-2-3-4
        //                     |-|
        //         |
        //                             |
        // |-|
        //       |-------|
        //                   |
        //           |---|
        //         |-|
        //                   |-----|
        //
        // expected:
        // 0-1-2-3-4-5-6-7-8-9-0-1-2-3-4
        // |-|
        //       |-------|
        //                   |-----|
        //                             |
        assert_eq_after_merge(
            vec![(10, 11), (4, 4), (14, 14), (0, 1), (3, 7), (9, 9), (5, 7), (4, 5), (9, 12)],
            vec![(0, 1), (3, 7), (9, 12), (14, 14)]
        );
    }
}
