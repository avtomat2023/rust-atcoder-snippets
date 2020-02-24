//! Segment tree.
//!
//! For implementation details, see [this article](https://codeforces.com/blog/entry/18051).

use crate::range::UsizeRangeBoundsExt;

// BEGIN SNIPPET segtree DEPENDS ON range option

// use num::Numeric;

/// Seqence updateble by point and aggregatable by interval.
///
/// The items of the sequence must be monoidal. That is:
///
/// - Aggregation of a subsequence is performed by repeating aggregation of
///   adjacent two item. In any order of two-item aggregations,
///   the final result must be the same.
/// - The must be identity element *id*. For any item *x*, aggregation of
///   *id* and *x* and aggregation of *x* and *id* must be *x*.
///
/// For example, `i32` is monoidal under addition, and its identity element is `0`.
///
/// Any update and aggregation is performed in Θ(log(*n*)) time,
/// as *n* is the number of items in the sequence.
pub struct SegmentTree<T: Clone, F: Fn(&T, &T) -> T> {
    heap: Vec<T>,
    identity: T,
    aggregate: F
}

mod segment_tree_internal {
    pub fn parent_of(heap_index: usize) -> usize {
        (heap_index - 1) / 2
    }

    pub fn left_of(heap_index: usize) -> usize {
        heap_index * 2 + 1
    }

    pub fn right_of(heap_index: usize) -> usize {
        left_of(heap_index) + 1
    }

    pub fn is_root_or_right(heap_index: usize) -> bool {
        heap_index % 2 == 0
    }
}

impl<T: Clone, F: Fn(&T, &T) -> T> SegmentTree<T, F> {
    /// Create a new segment tree with `len` items.
    ///
    /// `T` must be monoidal under `aggregate`,
    /// and its identity element must be `identity`.
    ///
    /// All items in the segment tree is set as `identity`.
    pub fn new(len: usize, identity: T, aggregate: F) -> SegmentTree<T, F> {
        SegmentTree {
            heap: vec![identity.clone(); (len * 2).saturating_sub(1)],
            identity: identity,
            aggregate: aggregate
        }
    }

    /// Create a new segment tree from items in a vector.
    pub fn from_vec(mut items: Vec<T>, identity: T, aggregate: F) -> SegmentTree<T, F> {
        use self::segment_tree_internal::*;

        let node_count = items.len().saturating_sub(1);
        let mut heap = Vec::with_capacity(node_count + items.len());
        unsafe { heap.set_len(node_count); }
        heap.append(&mut items);
        for i in (0..node_count).rev() {
            heap[i] = aggregate(&heap[left_of(i)], &heap[right_of(i)]);
        }

        SegmentTree {
            heap: heap,
            identity: identity,
            aggregate: aggregate
        }
    }

    fn node_count(&self) -> usize {
        self.heap.len() / 2
    }

    /// The number of items.
    pub fn len(&self) -> usize {
        self.heap.len() - self.node_count()
    }

    /// Returns whether the tree has no items.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets all items as a slice.
    ///
    /// This takes constant time.
    pub fn items(&self) -> &[T] {
        &self.heap[self.node_count() .. self.node_count()+self.len()]
    }

    /// Aggregate items in the range of `index`.
    ///
    /// If the index is out of bound, returns `None`.
    ///
    /// This method takes Θ(log(`len`)) time.
    /// If you want to get an item instead of aggregation of a range,
    /// use `tree.items().get(index)`. It's constant time.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::segtree::*;
    ///
    /// // let segment_tree = (0..10).range_sum_segment_tree();
    /// let segment_tree = (0..10).segment_tree(0, |&x, &y| x + y);
    ///
    /// assert_eq!(segment_tree.query(3..=6), Some(18));
    /// assert_eq!(segment_tree.query(3..), Some(42));
    /// assert_eq!(segment_tree.query(3..=10), None);
    /// ```
    pub fn query<R: std::ops::RangeBounds<usize>>(&self, range: R) -> Option<T> {
        range.to_range(self.len()).map(|range| {
            self.aggregate_interval(
                self.node_count() + range.start, self.node_count() + range.end,
                self.identity.clone(), self.identity.clone()
            )
        })
    }

    fn aggregate_interval(&self, mut heap_start: usize, mut heap_end: usize,
                          mut acc_left: T, mut acc_right: T) -> T {
        use self::segment_tree_internal::*;

        if heap_end == heap_start {
            (self.aggregate)(&acc_left, &acc_right)
        } else {
            if is_root_or_right(heap_start) {
                acc_left = (self.aggregate)(&acc_left, &self.heap[heap_start]);
                heap_start += 1;
            }
            if is_root_or_right(heap_end) {
                heap_end -= 1;
                acc_right = (self.aggregate)(&self.heap[heap_end], &acc_right);
            }
            self.aggregate_interval(
                parent_of(heap_start), parent_of(heap_end), acc_left, acc_right
            )
        }
    }

    /// Gets mutable reference to an item.
    ///
    /// When the reference is dropped,
    /// the internal structure of the segment tree is updated.
    /// The drop takes Θ(log(`len`)) time.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::segtree::*;
    ///
    /// let mut segment_tree = SegmentTree::new(10, 0, |&a, &b| a+b);
    /// {
    ///     let mut item_ref = segment_tree.get_mut(1).unwrap();
    ///     for _ in 0..100 {
    ///         *item_ref += 1;
    ///     }
    ///     // `item_ref` is dropped here.
    ///     // Update of `segment_tree` only once when `item_ref` is dropped.
    /// }
    ///
    /// assert_eq!(segment_tree.query(1..5), Some(100));
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<SegmentTreeItemRef<T, F>> {
        if index < self.len() {
            let heap_index = self.node_count() + index;
            Some(SegmentTreeItemRef {
                tree: self,
                heap_index: heap_index
            })
        } else {
            None
        }
    }

    /// Shorthand for `tree.get_mut(index).unwrap()`
    pub fn at(&mut self, index: usize) -> SegmentTreeItemRef<T, F> {
        self.get_mut(index).unwrap()
    }

    fn update_ancestors(&mut self, heap_index: usize) {
        use self::segment_tree_internal::*;

        if heap_index != 0 {
            let parent = parent_of(heap_index);
            let l = left_of(parent);
            let r = right_of(parent);
            self.heap[parent] = (self.aggregate)(&self.heap[l], &self.heap[r]);
            self.update_ancestors(parent);
        }
    }
}

pub struct SegmentTreeItemRef<'a, T: Clone, F: Fn(&T, &T) -> T> {
    tree: &'a mut SegmentTree<T, F>,
    heap_index: usize
}

impl<T, F> std::ops::Deref for SegmentTreeItemRef<'_, T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T
{
    type Target = T;

    fn deref(&self) -> &T {
        &self.tree.heap[self.heap_index]
    }
}

impl<T, F> std::ops::DerefMut for SegmentTreeItemRef<'_, T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T
{
    fn deref_mut(&mut self) -> &mut T {
        &mut self.tree.heap[self.heap_index]
    }
}

impl<T, F> Drop for SegmentTreeItemRef<'_, T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T
{
    fn drop(&mut self) {
        self.tree.update_ancestors(self.heap_index);
    }
}

/*
pub fn range_sum_segment_tree<T>(len: usize) -> SegmentTree<T, impl Fn(&T, &T) -> T>
where
    T: Clone + Numeric
{
    SegmentTree::new(len, T::zero(), |x, y| x.clone() + y)
}
*/

pub trait IteratorExtForSegmentTree: Sized + Iterator
where
    Self::Item: Clone
{
    fn segment_tree<F>(self, identity: Self::Item, aggregate: F) -> SegmentTree<Self::Item, F>
    where
        F: Fn(&Self::Item, &Self::Item) -> Self::Item
    {
        SegmentTree::from_vec(self.collect(), identity, aggregate)
    }
}

impl<I: Iterator> IteratorExtForSegmentTree for I where Self::Item: Clone {}

// END SNIPPET

#[cfg(test)]
mod test {
    use super::*;

    fn sum(a: &i32, b: &i32) -> i32 {
        a + b
    }

    #[test]
    fn test_node_count() {
        assert_eq!(SegmentTree::new(0, 0, sum).node_count(), 0);
        assert_eq!(SegmentTree::new(1, 0, sum).node_count(), 0);
        assert_eq!(SegmentTree::new(2, 0, sum).node_count(), 1);
        assert_eq!(SegmentTree::new(3, 0, sum).node_count(), 2);
        assert_eq!(SegmentTree::new(4, 0, sum).node_count(), 3);
        assert_eq!(SegmentTree::new(10, 0, sum).node_count(), 9);
    }

    #[test]
    fn test_node_len() {
        assert_eq!(SegmentTree::new(0, 0, sum).len(), 0);
        assert_eq!(SegmentTree::new(1, 0, sum).len(), 1);
        assert_eq!(SegmentTree::new(2, 0, sum).len(), 2);
        assert_eq!(SegmentTree::new(3, 0, sum).len(), 3);
        assert_eq!(SegmentTree::new(4, 0, sum).len(), 4);
        assert_eq!(SegmentTree::new(10, 0, sum).len(), 10);
    }

    #[test]
    fn test_heap_size() {
        assert_eq!(SegmentTree::new(0, 0, sum).heap.len(), 0);
        assert_eq!(SegmentTree::new(1, 0, sum).heap.len(), 1);
        assert_eq!(SegmentTree::new(2, 0, sum).heap.len(), 3);
        assert_eq!(SegmentTree::new(3, 0, sum).heap.len(), 5);
        assert_eq!(SegmentTree::new(4, 0, sum).heap.len(), 7);
        assert_eq!(SegmentTree::new(10, 0, sum).heap.len(), 19);
    }

    #[test]
    fn test_from_vec() {
        let range_sum_0 = SegmentTree::from_vec(Vec::new(), 0, sum);
        assert_eq!(range_sum_0.heap, vec![]);

        let range_sum_1 = SegmentTree::from_vec(vec![0], 0, sum);
        assert_eq!(range_sum_1.heap, vec![0]);

        let range_sum_2 = SegmentTree::from_vec(vec![0,1], 0, sum);
        assert_eq!(range_sum_2.heap, vec![1,0,1]);

        let range_sum_3 = SegmentTree::from_vec(vec![0,1,2], 0, sum);
        assert_eq!(range_sum_3.heap, vec![3,3,0,1,2]);

        let range_sum_6 = SegmentTree::from_vec((0..6).collect(), 0, sum);
        let expected_6 = vec![
            15,
            14, 1,
            5, 9, 0, 1,
            2, 3, 4, 5
        ];
        assert_eq!(range_sum_6.heap, expected_6);

        let range_sum_7 = SegmentTree::from_vec((0..7).collect(), 0, sum);
        let expected_7 = vec![
            21,
            10, 11,
            3, 7, 11, 0,
            1, 2, 3, 4, 5, 6
        ];
        assert_eq!(range_sum_7.heap, expected_7);
    }

    #[test]
    fn test_get_mut() {
        let mut range_sum_1 = SegmentTree::new(6, 0, sum);
        *range_sum_1.get_mut(0).unwrap() = 0;
        *range_sum_1.get_mut(1).unwrap() = 1;
        *range_sum_1.get_mut(2).unwrap() = 2;
        *range_sum_1.get_mut(3).unwrap() = 3;
        *range_sum_1.get_mut(4).unwrap() = 4;
        *range_sum_1.get_mut(5).unwrap() = 5;

        let expected_1 = vec![
            15,
            14, 1,
            5, 9, 0, 1,
            2, 3, 4, 5
        ];
        assert_eq!(range_sum_1.heap, expected_1);

        let mut range_sum_2 = SegmentTree::new(7, 0, sum);
        *range_sum_2.get_mut(0).unwrap() = 0;
        *range_sum_2.get_mut(1).unwrap() = 1;
        *range_sum_2.get_mut(2).unwrap() = 2;
        *range_sum_2.get_mut(3).unwrap() = 3;
        *range_sum_2.get_mut(4).unwrap() = 4;
        *range_sum_2.get_mut(5).unwrap() = 5;
        *range_sum_2.get_mut(6).unwrap() = 6;

        let expected_2 = vec![
            21,
            10, 11,
            3, 7, 11, 0,
            1, 2, 3, 4, 5, 6
        ];
        assert_eq!(range_sum_2.heap, expected_2);
    }

    #[test]
    fn test_at() {
        let mut range_sum = SegmentTree::new(6, 0, sum);
        *range_sum.at(0) = 1;

        let expected = vec![
            1,
            0, 1,
            0, 0, 1, 0,
            0, 0, 0, 0
        ];
        assert_eq!(range_sum.heap, expected);
    }

    #[test]
    fn test_query() {
        let mut range_sum = SegmentTree::new(6, 0, sum);
        *range_sum.at(0) = 0;
        *range_sum.at(1) = 1;
        *range_sum.at(2) = 2;
        *range_sum.at(3) = 3;
        *range_sum.at(4) = 4;
        *range_sum.at(5) = 5;

        assert_eq!(range_sum.query(0..=0), Some(0));
        assert_eq!(range_sum.query(0..=1), Some(1));
        assert_eq!(range_sum.query(0..=2), Some(3));
        assert_eq!(range_sum.query(0..=3), Some(6));
        assert_eq!(range_sum.query(0..=4), Some(10));
        assert_eq!(range_sum.query(0..=5), Some(15));
        assert_eq!(range_sum.query(0..=6), None);

        assert_eq!(range_sum.query(1..1), Some(0));
        assert_eq!(range_sum.query(1..2), Some(1));
        assert_eq!(range_sum.query(1..3), Some(3));
        assert_eq!(range_sum.query(1..4), Some(6));
        assert_eq!(range_sum.query(1..5), Some(10));
        assert_eq!(range_sum.query(1..6), Some(15));
        assert_eq!(range_sum.query(1..7), None);

        assert_eq!(range_sum.query(2..), Some(14));
        assert_eq!(range_sum.query(..3), Some(3));
        assert_eq!(range_sum.query(..=3), Some(6));

        assert_eq!(range_sum.query(3..2), None);
    }

    #[test]
    fn test_query_from_end() {
        let mut range_sum = SegmentTree::new(3, 0, sum);
        *range_sum.at(0) = 0;
        *range_sum.at(1) = 0;
        *range_sum.at(2) = 0;

        assert_eq!(range_sum.query(3..), Some(0));
        assert_eq!(range_sum.query(3..3), Some(0));
    }
}
