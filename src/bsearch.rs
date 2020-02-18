// TODO: document bsearch_index_***
//! Generalized binary search.
//!
//! # Example
//!
//! ```
//! # #[macro_use] extern crate atcoder_snippets;
//! # use atcoder_snippets::bsearch::*;
//! fn count_key(sorted_slice: &[i32], key: i32) -> usize {
//!     let len = sorted_slice.len();
//!     match ((0..len).bsearch_right_min(|&i| key <= sorted_slice[i]),
//!            (0..len).bsearch_right_min(|&i| key < sorted_slice[i])) {
//!         (Some(l), r) => r.unwrap_or(len) - l,
//!         _ => 0
//!     }
//! }
//!
//! assert_eq!(count_key(&[], 2), 0);
//! assert_eq!(count_key(&[1,1,1,1,1,1], 2), 0);
//! assert_eq!(count_key(&[3,3,3,3,3,3], 2), 0);
//! assert_eq!(count_key(&[1,1,1,1,2,2], 2), 2);
//! assert_eq!(count_key(&[2,2,3,3,3,3], 2), 2);
//! assert_eq!(count_key(&[1,1,2,2,3,3], 2), 2);
//! assert_eq!(count_key(&[2,2,2,2,2,2], 2), 6);
//! ```

use std;
use num::PrimitiveInteger;

// BEGIN SNIPPET bsearch DEPENDS ON num

/// A sequence that binary search is applicable to.
pub trait BSearch: Sized {
    /// Item type of the sequence.
    type Item;

    /// Returns whether the sequence is empty.
    fn is_empty(&self) -> bool;

    /// Returns the last item in the sequence.
    ///
    /// If the sequence is empty, this method may panic.
    fn leftmost_item(&self) -> Self::Item;

    /// Returns the first item in the sequence.
    ///
    /// If the sequence is empty, this method may panic.
    fn rightmost_item(&self) -> Self::Item;

    /// Returns the middle item in the sequence.
    ///
    /// If the sequence is discrete and contains an odd number of items,
    /// this method returns the exact middle of the sequence.
    /// If the sequence is discrete and contains an even number of items,
    /// it's not sure whether this method returns the left middle or the right middle.
    ///
    /// For the same two sequeces, this method always returns the same value.
    ///
    /// If the sequence is empty, this method may panic.
    fn middle_item(&self) -> Self::Item;

    /// Returns the left half of the sequence, including `self.middle_item()`
    /// placed at the last of the returned sequence.
    ///
    /// For any non-empty and non-converged sequence, this method returns
    /// an non-empty sequence.
    ///
    /// If the sequence is empty or already converged, this method may panic.
    fn left_half(&self) -> Self;

    /// Returns the right half of the sequence, including `self.middle_item()`
    /// placed at the first of the returned sequence.
    ///
    /// For any non-empty and non-converged sequence, this method returns
    /// an non-empty sequence.
    ///
    /// If the sequence is empty of already, this method may panic.
    fn right_half(&self) -> Self;

    /// Check convergence of halving process.
    ///
    /// An empty sequence returns `true`.
    ///
    /// For discrete sequences, this method is equivalent that `len <= 2`.
    fn is_bsearch_converged(&self) -> bool;

    /// Returns the rightmost item satisfing `is_left`.
    ///
    /// When calling `bsearch_left_max`, you must make sure that
    /// the sequence can be partitioned by `is_left`.
    /// That is, there must be a position satisfying that:
    ///
    /// - All items left of the position satisfies `is_left`.
    /// - All items right of the position doesn't satisfy `is_left`.
    ///
    /// The situation can be divided the following 4 cases:
    ///
    /// 1. The sequence is empty. Returns `None`.
    /// 2. The sequence is partitioned into non-empty left and right parts:
    ///    `[L, L, L, L, R, R]`. Returns `Some(the rightmost L item)`.
    /// 3. All items satisfy `is_left`: `[L, L, L, L, L, L]`.
    ///    Returns `Some(the rightmost item)`.
    /// 3. All items don't satisfy `is_left`: `[R, R, R, R, R, R]`.
    ///    Returns `None`.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::bsearch::*;
    /// let seq = [3, 6, 9, 12, 15];
    /// assert_eq!((0..seq.len()).bsearch_left_max(|&i| seq[i] <= 10), Some(2));
    /// ```
    fn bsearch_left_max<F>(&self, mut is_left: F) -> Option<Self::Item>
    where
        F: FnMut(&Self::Item) -> bool
    {
        if self.is_empty() {
            None
        } else if !is_left(&self.leftmost_item()) {
            None
        } else {
            let rightmost = self.rightmost_item();
            if is_left(&rightmost) {
                Some(rightmost)
            } else {
                Some(bsearch_left_max_sub(self, is_left))
            }
        }
    }

    /// Returns the minimum item satisfing `is_right`.
    ///
    /// See doc of [`bsearch_left_max`](#method.bsearch_left_max).
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::bsearch::*;
    /// let seq = [3, 6, 9, 12, 15];
    /// assert_eq!((0..seq.len()).bsearch_right_min(|&i| seq[i] >= 10), Some(3));
    /// ```
    fn bsearch_right_min<F>(&self, mut is_right: F) -> Option<Self::Item>
    where
        F: FnMut(&Self::Item) -> bool
    {
        if self.is_empty() {
            None
        } else if !is_right(&self.rightmost_item()) {
            None
        } else {
            let leftmost = self.leftmost_item();
            if is_right(&leftmost) {
                Some(leftmost)
            } else {
                Some(bsearch_right_min_sub(self, is_right))
            }
        }
    }
}

fn bsearch_left_max_sub<Items, T, F>(items: &Items, mut is_left: F) -> T
where
    Items: BSearch<Item=T>,
    F: FnMut(&T) -> bool
{
    if items.is_bsearch_converged() {
        items.leftmost_item()
    } else {
        if is_left(&items.middle_item()) {
            bsearch_left_max_sub(&items.right_half(), is_left)
        } else {
            bsearch_left_max_sub(&items.left_half(), is_left)
        }
    }
}

fn bsearch_right_min_sub<Items, T, F>(items: &Items, mut is_right: F) -> T
where
    Items: BSearch<Item=T>,
    F: FnMut(&T) -> bool
{
    if items.is_bsearch_converged() {
        items.rightmost_item()
    } else {
        if is_right(&items.middle_item()) {
            bsearch_right_min_sub(&items.left_half(), is_right)
        } else {
            bsearch_right_min_sub(&items.right_half(), is_right)
        }
    }
}

impl<T: PrimitiveInteger + Clone> BSearch for std::ops::Range<T> {
    type Item = T;

    fn is_empty(&self) -> bool {
        self.end <= self.start
    }

    fn leftmost_item(&self) -> T {
        self.start.clone()
    }

    fn rightmost_item(&self) -> T {
        self.end.clone() - T::one()
    }

    fn middle_item(&self) -> T {
        (self.leftmost_item() + self.rightmost_item()) / (T::one() + T::one())
    }

    fn left_half(&self) -> std::ops::Range<T> {
        self.start.clone()..(self.middle_item() + T::one())
    }

    fn right_half(&self) -> std::ops::Range<T> {
        self.middle_item()..self.end.clone()
    }

    fn is_bsearch_converged(&self) -> bool {
        BSearch::is_empty(self) || self.end.clone() - self.start.clone() <= T::one() + T::one()
    }
}

impl<'a, T> BSearch for &'a [T] {
    type Item = &'a T;

    fn is_empty(&self) -> bool {
        <[T]>::is_empty(self)
    }

    fn leftmost_item(&self) -> &'a T {
        self.first().unwrap()
    }

    fn rightmost_item(&self) -> &'a T {
        self.last().unwrap()
    }

    fn middle_item(&self) -> &'a T {
        self.get(self.len() / 2).unwrap()
    }

    fn left_half(&self) -> &'a [T] {
        &self[..(self.len() / 2 + 1)]
    }

    fn right_half(&self) -> &'a [T] {
        &self[(self.len() / 2)..]
    }

    fn is_bsearch_converged(&self) -> bool {
        self.len() <= 2
    }
}

pub trait SliceBSearch {
    type Item;

    fn bsearch_left_max<F>(&self, is_left: F) -> Option<&Self::Item>
    where
        F: FnMut(&Self::Item) -> bool;

    fn bsearch_index_left_max<F>(&self, is_left: F) -> Option<usize>
    where
        F: FnMut(&Self::Item) -> bool;

    fn bsearch_right_min<F>(&self, is_right: F) -> Option<&Self::Item>
    where
        F: FnMut(&Self::Item) -> bool;

    fn bsearch_index_right_min<F>(&self, is_right: F) -> Option<usize>
    where
        F: FnMut(&Self::Item) -> bool;
}

impl<T> SliceBSearch for [T] {
    type Item = T;

    fn bsearch_left_max<F>(&self, mut is_left: F) -> Option<&T>
    where
        F: FnMut(&T) -> bool
    {
        BSearch::bsearch_left_max(&self, |&x| is_left(x))
    }

    fn bsearch_index_left_max<F>(&self, mut is_left: F) -> Option<usize>
    where
        F: FnMut(&T) -> bool
    {
        (0..self.len()).bsearch_left_max(|&i| {
            let x = unsafe { self.get_unchecked(i) };
            is_left(x)
        })
    }

    fn bsearch_right_min<F>(&self, mut is_right: F) -> Option<&T>
    where
        F: FnMut(&T) -> bool
    {
        BSearch::bsearch_right_min(&self, |&x| is_right(x))
    }

    fn bsearch_index_right_min<F>(&self, mut is_right: F) -> Option<usize>
    where
        F: FnMut(&T) -> bool
    {
        (0..self.len()).bsearch_right_min(|&i| {
            let x = unsafe { self.get_unchecked(i) };
            is_right(x)
        })
    }
}

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::BSearch;

    #[test]
    fn test_range_middle_item() {
        assert_eq!((10..11).middle_item(), 10);
        assert!((10..12).middle_item() == 10 || (10..12).middle_item() == 11);
        assert_eq!((10..13).middle_item(), 11);
        assert_eq!((10..21).middle_item(), 15);

        assert_eq!((-10..-9).middle_item(), -10);
        assert!((-10..-8).middle_item() == -10 || (-10..-8).middle_item() == -9);
        assert_eq!((-10..-7).middle_item(), -9);
        assert_eq!((-10..1).middle_item(), -5);
    }

    #[test]
    fn test_slice_bsearch_left_max() {
        use super::SliceBSearch;

        let empty: Vec<i32> = Vec::new();
        assert_eq!(empty.bsearch_left_max(|&x| x <= 0), None);
        let seq = vec![3, 6, 9, 12, 15];
        assert_eq!(seq.bsearch_left_max(|&x| x <= 0), None);
        assert_eq!(seq.bsearch_left_max(|&x| x <= 10), Some(&9));
        assert_eq!(seq.bsearch_left_max(|&x| x <= 20), Some(&15));
    }

    #[test]
    fn test_slice_bsearch_index_left_max() {
        use super::SliceBSearch;

        let empty: Vec<i32> = Vec::new();
        assert_eq!(empty.bsearch_index_left_max(|&x| x <= 0), None);
        let seq = vec![3, 6, 9, 12, 15];
        assert_eq!(seq.bsearch_index_left_max(|&x| x <= 0), None);
        assert_eq!(seq.bsearch_index_left_max(|&x| x <= 10), Some(2));
        assert_eq!(seq.bsearch_index_left_max(|&x| x <= 20), Some(4));
    }

    #[test]
    fn test_slice_bsearch_right_min() {
        use super::SliceBSearch;

        let empty: Vec<i32> = Vec::new();
        assert_eq!(empty.bsearch_right_min(|&x| x <= 0), None);
        let seq = vec![3, 6, 9, 12, 15];
        assert_eq!(seq.bsearch_right_min(|&x| x >= 0), Some(&3));
        assert_eq!(seq.bsearch_right_min(|&x| x >= 10), Some(&12));
        assert_eq!(seq.bsearch_right_min(|&x| x >= 20), None);
    }

    #[test]
    fn test_slice_bsearch_index_right_min() {
        use super::SliceBSearch;

        let empty: Vec<i32> = Vec::new();
        assert_eq!(empty.bsearch_index_right_min(|&x| x <= 0), None);
        let seq = vec![3, 6, 9, 12, 15];
        assert_eq!(seq.bsearch_index_right_min(|&x| x >= 0), Some(0));
        assert_eq!(seq.bsearch_index_right_min(|&x| x >= 10), Some(3));
        assert_eq!(seq.bsearch_index_right_min(|&x| x >= 20), None);
    }
}
