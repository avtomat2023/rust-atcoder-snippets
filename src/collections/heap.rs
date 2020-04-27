//! Priority queues implemented by binary heaps.
//!
//! This module covers use cases `std::collection::BinaryHeap` misses.
//!
//! - You can use both of maximum heap and minimum heap.
//! - You can pass key function for comparing elements. You don't have to implemnt `Ord` for the element.
//!
//! As a typical example, `std::collection:::BinaryHeap` requires a lot of boilerplate
//! for implmeting Dijkstra's single source shortest paths algorithm.
//!
//! ```no_run
//! use std::collections::BinaryHeap;
//! use std::cmp::Ordering;
//!
//! struct Edge {
//!     incoming_node: usize,
//!     cost: u32
//! }
//!
//! #[derive(PartialEq, Eq)]
//! struct Node {
//!     id: usize,
//!     distance: u32
//! }
//!
//! impl Ord for Node {
//!     fn cmp(&self, other: &Node) -> Ordering {
//!         // reversed compare for using a maximum heap as minimum heap
//!         other.distance.cmp(&self.distance)
//!     }
//! }
//!
//! impl PartialOrd for Node {
//!     fn partial_cmp(&self, other: &Node) -> Option<Ordering> {
//!         Some(self.cmp(other))
//!     }
//! }
//!
//! // gets shortest distances for each node from node 0
//! fn dijkstra(adjacency_list: &[Vec<Edge>]) -> Vec<Option<u32>> {
//!     let mut queue = BinaryHeap::new();
//!     let mut distances = vec![None; adjacency_list.len()];
//!     queue.push(Node { id: 0, distance: 0});
//!     distances[0] = Some(0);
//!
//!     while let Some(node) = queue.pop() {
//!         if node.distance > distances[node.id].unwrap() {
//!             continue;
//!         }
//!         for edge in &adjacency_list[node.id] {
//!             let next_distance = node.distance + edge.cost;
//!             if distances[edge.incoming_node].map_or(true, |d| next_distance < d) {
//!                 queue.push(Node { id: edge.incoming_node, distance: next_distance });
//!                 distances[edge.incoming_node] = Some(next_distance);
//!             }
//!         }
//!     }
//!     distances
//! }
//! ```
//!
//! You can omit `impl Ord` and `impl PartialOrd` by using a minimum heap.
//!
//! ```no_run
//! # use atcoder_snippets::collections::heap::*;
//! struct Edge {
//!     incoming_node: usize,
//!     cost: u32
//! }
//!
//! struct Node {
//!     id: usize,
//!     distance: u32
//! }
//!
//! fn dijkstra(adjacency_list: &[Vec<Edge>]) -> Vec<Option<u32>> {
//!     let mut queue = min_heap_by_key(|node: &Node| node.distance);
//!     let mut distances = vec![None; adjacency_list.len()];
//!     queue.push(Node { id: 0, distance: 0});
//!     distances[0] = Some(0);
//!
//!     while let Some(node) = queue.pop() {
//!         if node.distance > distances[node.id].unwrap() {
//!             continue;
//!         }
//!         for edge in &adjacency_list[node.id] {
//!             let next_distance = node.distance + edge.cost;
//!             if distances[edge.incoming_node].map_or(true, |d| next_distance < d) {
//!                 queue.push(Node { id: edge.incoming_node, distance: next_distance });
//!                 distances[node.id] = Some(next_distance);
//!             }
//!         }
//!     }
//!     distances
//! }
//! ```

// TODO: Add examples: EDPC N

// BEGIN SNIPPET heap

mod max_heap_internal {
    use std::cmp::Ordering::{self, *};

    /// Calculates the parent's index of the node at `pos` in a heap.
    ///
    /// If `pos` is 0, returns `None`.
    pub fn parent_of(pos: usize) -> Option<usize> {
        if pos == 0 {
            None
        } else {
            Some(parent_of_unchecked(pos))
        }
    }

    /// Calculates the parent's index of the node at `pos` in a heap.
    ///
    /// `pos` must not be 0.
    fn parent_of_unchecked(pos: usize) -> usize {
        (pos - 1) / 2
    }

    /// Calculates the left child's index of the node at `pos` in `heap`.
    ///
    /// If `pos` is out of the length of `heap`, returns `None`.
    pub fn left_of<T>(pos: usize, heap: &Vec<T>) -> Option<usize> {
        let left = left_of_unchecked(pos);
        if heap.len() <= left {
            None
        } else {
            Some(left)
        }
    }

    /// Calculates the left child's index of the node at `pos` in a heap.
    fn left_of_unchecked(pos: usize) -> usize {
        pos * 2 + 1
    }

    /// Calculates the right child's index of the node at `pos` in `heap`.
    ///
    /// If `pos` is out of the length of `heap`, returns `None`.
    pub fn right_of<T>(pos: usize, heap: &Vec<T>) -> Option<usize> {
        let right = right_of_unchecked(pos);
        if heap.len() <= right {
            None
        } else {
            Some(right)
        }
    }

    /// Calculates the right child's index of the node at `pos` in a heap.
    fn right_of_unchecked(pos: usize) -> usize {
        left_of_unchecked(pos) + 1
    }

    /// Rearranges `vec` into a maximum heap, using `cmp` for comparison.
    pub fn build<T, F: Fn(&T, &T) -> Ordering + Copy>(vec: &mut Vec<T>, cmp: F) {
        for i in (0..vec.len()/2).rev() {
            sift_down(vec, i, cmp)
        }
    }

    /// Sifts the node at `pos` in `heap` toward its leaves,
    /// and makes the subtree rooted by the item into a maximum heap.
    ///
    /// # Preconditions
    ///
    /// The left and right subtrees of the node must be a maximum heap.
    ///
    /// `pos` must be less than `heap.len()`.
    pub fn sift_down<T, F: Fn(&T, &T) -> Ordering + Copy>(heap: &mut Vec<T>, pos: usize, cmp: F) {
        let next = left_of(pos, heap).map_or(pos, |l| {
            if cmp(&heap[pos], &heap[l]) == Less { l } else { pos }
        });
        let next = right_of(pos, heap).map_or(next, |r| {
            if cmp(&heap[next], &heap[r]) == Less { r } else { next }
        });

        if next != pos {
            heap.swap(pos, next);
            sift_down(heap, next, cmp);
        }
    }

    /// Sifts the node at `pos` in `heap` toward its root,
    /// and makes the all nodes on the path to the root sorted.
    ///
    /// # Precondition
    ///
    /// The node on the path except for the node at `pos` must be sorted.
    pub fn sift_up<T, F: Fn(&T, &T) -> Ordering + Copy>(heap: &mut Vec<T>, pos: usize, cmp: F) {
        parent_of(pos).into_iter().for_each(|parent| {
            if cmp(&heap[parent], &heap[pos]) == Less {
                heap.swap(parent, pos);
                sift_up(heap, parent, cmp);
            }
        });
    }
}

/// Priority queue trait.
///
/// Providing this as a trait is useful for concise coding.
/// When you write a function receiving a `MaxHeap`,
/// you don't have to write a trait bound for comparison function.
/// If you write type directly, the signature looks like:
///
/// ```no_run
/// # use atcoder_snippets::collections::heap::*;
/// use std::cmp::Ordering;
///
/// fn f(heap: &mut MaxHeap<i32, impl Fn(&i32, &i32) -> Ordering>) {
///     /* ... */
/// }
/// ```
///
/// Thanks to `PriorityQueue` trait, you can write as:
///
/// ```no_run
/// # use atcoder_snippets::collections::heap::*;
/// fn f(heap: &mut impl PriorityQueue<i32>) {
///     /* ... */
/// }
/// ```
pub trait PriorityQueue<T>: IntoIterator<Item=T> + Extend<T> {
    /// Returns how many items the queue contains.
    fn len(&self) -> usize;

    /// Returns if the queue is empty.
    fn is_empty(&self) -> bool;

    /// Pushes an item.
    fn push(&mut self, x: T);

    /// Pops the most prioritized item.
    fn pop(&mut self) -> Option<T>;

    /// Gets the most prioritized item without removing it.
    fn peek(&self) -> Option<&T>;
}

/// Priority queue yielding its maximum item.
#[derive(Clone)]
pub struct MaxHeap<T, F> {
    heap: Vec<T>,
    cmp: F
}

impl<T, F> MaxHeap<T, F> {
    /// Creates an empty priority queue using `cmp` for comparison.
    fn new(cmp: F) -> MaxHeap<T, F> {
        MaxHeap {
            heap: Vec::new(),
            cmp: cmp
        }
    }

    /// Returns underlying `Vec` as a slice.
    ///
    /// The slice is not necessarily sorted.
    pub fn as_slice(&self) -> &[T] {
        &self.heap
    }

    /// Consumes the priority queue and returns the underlying `Vec`.
    ///
    /// The vector is not necessarily sorted.
    /// To get sorted `Vec` use `queue.into_iter().collect()`.
    /// It takes Θ(*n* log *n*) time, whereas `into_vec` takes just constant time.
    pub fn into_vec(self) -> Vec<T> {
        self.heap
    }
}

impl<T, F: Fn(&T, &T) -> std::cmp::Ordering> MaxHeap<T, F> {
    /// Creates a priority queue of all items in `vec`, using `cmp` for comparison.
    fn from_vec(mut vec: Vec<T>, cmp: F) -> MaxHeap<T, F> {
        use self::max_heap_internal::*;

        build(&mut vec, &cmp);
        MaxHeap {
            heap: vec,
            cmp: cmp
        }
    }
}

/// Creates an empty maximum heap.
pub fn max_heap<T: Ord>() -> MaxHeap<T, impl Fn(&T, &T) -> std::cmp::Ordering> {
    MaxHeap::new(Ord::cmp)
}

/// Creates a maximum heap of all items in `vec`.
pub fn max_heap_from_vec<T: Ord>(vec: Vec<T>) -> MaxHeap<T, impl Fn(&T, &T) -> std::cmp::Ordering> {
    MaxHeap::from_vec(vec, Ord::cmp)
}

/// Creates an empty maximum heap using `cmp` for comparison.
pub fn max_heap_by<T, F: Fn(&T, &T) -> std::cmp::Ordering>(cmp: F) -> MaxHeap<T, F> {
    MaxHeap::new(cmp)
}

/// Creates a maximum heap of all items in `vec`, using `cmp` for comparison.
pub fn max_heap_from_vec_by<T, F: Fn(&T, &T) -> std::cmp::Ordering>(vec: Vec<T>, cmp: F) -> MaxHeap<T, F> {
    MaxHeap::from_vec(vec, cmp)
}

/// Creates an empty maximum heap using `key` for comparison.
pub fn max_heap_by_key<T, K: Ord>(key: impl Fn(&T) -> K) -> MaxHeap<T, impl Fn(&T, &T) -> std::cmp::Ordering> {
    MaxHeap::new(move |a: &T, b: &T| key(a).cmp(&key(b)))
}

/// Creates a maximum heap of all items in `vec`, using `key` for comparison.
pub fn max_heap_from_vec_by_key<T, K: Ord>(vec: Vec<T>, key: impl Fn(&T) -> K) -> MaxHeap<T, impl Fn(&T, &T) -> std::cmp::Ordering> {
    MaxHeap::from_vec(vec, move |a: &T, b: &T| key(a).cmp(&key(b)))
}

/// Creates an empty minimum heap.
pub fn min_heap<T: Ord>() -> MaxHeap<T, impl Fn(&T, &T) -> std::cmp::Ordering> {
    MaxHeap::new(|a: &T, b: &T| b.cmp(a))
}

/// Creates a minimum heap of all items in `vec`.
pub fn min_heap_from_vec<T: Ord>(vec: Vec<T>) -> MaxHeap<T, impl Fn(&T, &T) -> std::cmp::Ordering> {
    MaxHeap::from_vec(vec, |a: &T, b: &T| b.cmp(a))
}

/// Creates an empty minimum heap using `cmp` for comparison.
pub fn min_heap_by<T, F: Fn(&T, &T) -> std::cmp::Ordering>(cmp: F) -> MaxHeap<T, impl Fn(&T, &T) -> std::cmp::Ordering> {
    MaxHeap::new(move |a: &T, b: &T| cmp(b, a))
}

/// Creates a minimum heap of all items in `vec`, using `cmp` for comparison.
pub fn min_heap_from_vec_by<T, F: Fn(&T, &T) -> std::cmp::Ordering>(vec: Vec<T>, cmp: F) -> MaxHeap<T, impl Fn(&T, &T) -> std::cmp::Ordering> {
    MaxHeap::from_vec(vec, move |a: &T, b: &T| cmp(b, a))
}

/// Creates an empty minimum heap using `key` for comparison.
pub fn min_heap_by_key<T, K: Ord>(key: impl Fn(&T) -> K) -> MaxHeap<T, impl Fn(&T, &T) -> std::cmp::Ordering> {
    MaxHeap::new(move |a: &T, b: &T| key(b).cmp(&key(a)))
}

/// Creates a minimum heap of all items in `vec`, using `key` for comparison.
pub fn min_heap_from_vec_by_key<T, K: Ord>(vec: Vec<T>, key: impl Fn(&T) -> K) -> MaxHeap<T, impl Fn(&T, &T) -> std::cmp::Ordering> {
    MaxHeap::from_vec(vec, move |a: &T, b: &T| key(b).cmp(&key(a)))
}

impl<T, F: Fn(&T, &T) -> std::cmp::Ordering> PriorityQueue<T> for MaxHeap<T, F> {
    fn len(&self) -> usize {
        self.heap.len()
    }

    fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    fn push(&mut self, x: T) {
        use self::max_heap_internal::*;

        self.heap.push(x);
        let last = self.heap.len() - 1;
        sift_up(&mut self.heap, last, &self.cmp);
    }

    fn pop(&mut self) -> Option<T> {
        use self::max_heap_internal::*;

        if !self.heap.is_empty() {
            let max = self.heap.swap_remove(0);
            sift_down(&mut self.heap, 0, &self.cmp);
            Some(max)
        } else {
            None
        }
    }

    fn peek(&self) -> Option<&T> {
        self.heap.get(0)
    }
}

impl<T: std::fmt::Debug, F: Fn(&T, &T) -> std::cmp::Ordering> std::fmt::Debug for MaxHeap<T, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut refs: Vec<&T> = self.as_slice().iter().collect();
        refs.sort_by(|&a, &b| (self.cmp)(a, b));
        f.debug_list().entries(refs.into_iter()).finish()
    }
}

pub struct MaxHeapIterator<T, F> {
    heap: MaxHeap<T, F>
}

impl<T, F: Fn(&T, &T) -> std::cmp::Ordering> IntoIterator for MaxHeap<T, F> {
    type Item = T;
    type IntoIter = MaxHeapIterator<T, F>;

    /// Creates an iterator yielding all element in the order of priority.
    fn into_iter(self) -> MaxHeapIterator<T, F> {
        MaxHeapIterator {
            heap: self
        }
    }
}

impl<T, F: Fn(&T, &T) -> std::cmp::Ordering> Iterator for MaxHeapIterator<T, F> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.heap.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.heap.len(), Some(self.heap.len()))
    }

    fn count(self) -> usize {
        self.heap.len()
    }
}

impl<T, F: Fn(&T, &T) -> std::cmp::Ordering> ExactSizeIterator for MaxHeapIterator<T, F> {}
impl<T, F: Fn(&T, &T) -> std::cmp::Ordering> std::iter::FusedIterator for MaxHeapIterator<T, F> {}

impl<T, F: Fn(&T, &T) -> std::cmp::Ordering> Extend<T> for MaxHeap<T, F> {
    fn extend<I: IntoIterator<Item=T>>(&mut self, iter: I) {
        for x in iter {
            self.push(x)
        }
    }
}

// TODO: Iterator extension for collecting min-heap and max-heap

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::{*, max_heap_internal::*};
    use std::fmt::Debug;

    #[test]
    fn test_sift_down() {
        let mut vec1 = vec![0];
        sift_down(&mut vec1, 0, |x, y| x.cmp(y));
        assert_eq!(vec1, vec![0]);

        let mut vec2_1 = vec![0, 1];
        sift_down(&mut vec2_1, 0, |x, y| x.cmp(y));
        assert_eq!(vec2_1, vec![1, 0]);

        let mut vec2_2 = vec![1, 0];
        sift_down(&mut vec2_2, 0, |x, y| x.cmp(y));
        assert_eq!(vec2_2, vec![1, 0]);

        let mut vec3_1 = vec![0, 1, 2];
        sift_down(&mut vec3_1, 0, |x, y| x.cmp(y));
        assert_eq!(vec3_1, vec![2, 1, 0]);

        let mut vec3_2 = vec![0, 2, 1];
        sift_down(&mut vec3_2, 0, |x, y| x.cmp(y));
        assert_eq!(vec3_2, vec![2, 0, 1]);

        let mut vec = vec![9, 1, 8, 5, 2, 6, 7, 4, 3];
        sift_down(&mut vec, 1, |x, y| x.cmp(y));
        assert_eq!(vec, vec![9, 5, 8, 4, 2, 6, 7, 1, 3]);
    }

    #[test]
    fn test_build() {
        let mut vec0: Vec<i32> = vec![];
        build(&mut vec0, |x, y| x.cmp(y));
        assert_eq!(vec0, vec![]);

        let mut vec1: Vec<i32> = vec![0];
        build(&mut vec1, |x, y| x.cmp(y));
        assert_eq!(vec1, vec![0]);

        let mut vec2: Vec<i32> = vec![0, 1];
        build(&mut vec2, |x, y| x.cmp(y));
        assert_eq!(vec2, vec![1, 0]);

        let mut vec3: Vec<i32> = vec![0, 1, 2];
        build(&mut vec3, |x, y| x.cmp(y));
        assert_eq!(vec3, vec![2, 1, 0]);

        let mut vec10: Vec<i32> = vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4];
        build(&mut vec10, |x, y| x.cmp(y));
        assert!((1..vec10.len()).all(|i| {
            vec10[parent_of(i).unwrap()] >= vec10[i]
        }));

        let mut vec11: Vec<i32> = vec![8, 5, 0, 2, 10, 1, 6, 3, 7, 9, 4];
        build(&mut vec11, |x, y| x.cmp(y));
        assert!((1..vec11.len()).all(|i| {
            vec11[parent_of(i).unwrap()] >= vec11[i]
        }));
    }

    fn assert_heap_eq<T: Eq + Debug>(mut heap: impl PriorityQueue<T>, expected: Vec<T>) {
        for x in expected {
            assert_eq!(heap.peek(), Some(&x));
            assert_eq!(heap.pop(), Some(x));
        }
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_max_heap() {
        let mut heap = max_heap();
        for x in vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4] {
            heap.push(x);
        }
        assert_heap_eq(heap, (0..10).rev().collect());
    }

    #[test]
    fn test_max_heap_from_vec() {
        let heap = max_heap_from_vec(vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4]);
        assert_heap_eq(heap, (0..10).rev().collect());
    }

    #[test]
    fn test_max_heap_by() {
        let mut heap = max_heap_by(|s: &&str, t: &&str| s.len().cmp(&t.len()));
        for x in vec!["bbbb", "aaaaa", "e", "ccc", "dd"] {
            heap.push(x);
        }
        assert_heap_eq(heap, vec!["aaaaa", "bbbb", "ccc", "dd", "e"]);
    }

    #[test]
    fn test_max_heap_from_vec_by() {
        let heap = max_heap_from_vec_by(
            vec!["bbbb", "aaaaa", "e", "ccc", "dd"],
            |s: &&str, t: &&str| s.len().cmp(&t.len())
        );
        assert_heap_eq(heap, vec!["aaaaa", "bbbb", "ccc", "dd", "e"]);
    }

    #[test]
    fn test_max_heap_by_key() {
        let mut heap = max_heap_by_key(|s: &&str| s.len());
        for x in vec!["bbbb", "aaaaa", "e", "ccc", "dd"] {
            heap.push(x);
        }
        assert_heap_eq(heap, vec!["aaaaa", "bbbb", "ccc", "dd", "e"]);
    }

    #[test]
    fn test_max_heap_from_vec_by_key() {
        let heap = max_heap_from_vec_by_key(
            vec!["bbbb", "aaaaa", "e", "ccc", "dd"],
            |s: &&str| s.len()
        );
        assert_heap_eq(heap, vec!["aaaaa", "bbbb", "ccc", "dd", "e"]);
    }

    #[test]
    fn test_min_heap() {
        let mut heap = min_heap();
        for x in vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4] {
            heap.push(x);
        }
        assert_heap_eq(heap, (0..10).collect());
    }

    #[test]
    fn test_min_heap_from_vec() {
        let heap = min_heap_from_vec(vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4]);
        assert_heap_eq(heap, (0..10).collect());
    }

    #[test]
    fn test_min_heap_by() {
        let mut heap = min_heap_by(|s: &&str, t: &&str| s.len().cmp(&t.len()));
        for x in vec!["bbbb", "aaaaa", "e", "ccc", "dd"] {
            heap.push(x);
        }
        assert_heap_eq(heap, vec!["e", "dd", "ccc", "bbbb", "aaaaa"]);
    }

    #[test]
    fn test_min_heap_from_vec_by() {
        let heap = min_heap_from_vec_by(
            vec!["bbbb", "aaaaa", "e", "ccc", "dd"],
            |s: &&str, t: &&str| s.len().cmp(&t.len())
        );
        assert_heap_eq(heap, vec!["e", "dd", "ccc", "bbbb", "aaaaa"]);
    }

    #[test]
    fn test_min_heap_by_key() {
        let mut heap = min_heap_by_key(|s: &&str| s.len());
        for x in vec!["bbbb", "aaaaa", "e", "ccc", "dd"] {
            heap.push(x);
        }
        assert_heap_eq(heap, vec!["e", "dd", "ccc", "bbbb", "aaaaa"]);
    }

    #[test]
    fn test_min_heap_from_vec_by_key() {
        let heap = min_heap_from_vec_by_key(
            vec!["bbbb", "aaaaa", "e", "ccc", "dd"],
            |s: &&str| s.len()
        );
        assert_heap_eq(heap, vec!["e", "dd", "ccc", "bbbb", "aaaaa"]);
    }

    #[test]
    fn test_into_iter() {
        let heap = min_heap_from_vec(vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4]);
        assert_eq!(heap.into_iter().collect::<Vec<_>>(), (0..10).collect::<Vec<_>>());
    }
}
