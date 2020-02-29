//! Queue each item can be inserted only once.

// BEGIN SNIPPET once_queue

use std::collections::{HashSet, VecDeque};
use std::hash::Hash;

/// Queue each item can be inserted only once.
///
/// Useful for breadh-first search.
pub struct HashOnceQueue<T: Clone + Eq + Hash> {
    queue: VecDeque<T>,
    visited: HashSet<T>,
}

impl<T: Clone + Eq + Hash> HashOnceQueue<T> {
    /// Craates an empty queue.
    pub fn new() -> HashOnceQueue<T> {
        HashOnceQueue {
            queue: VecDeque::new(),
            visited: HashSet::new(),
        }
    }

    /// Enqueues a new item unless it has not been pushed before.
    ///
    /// When the item is actually inserted, returns `true`.
    pub fn push(&mut self, x: T) -> bool {
        if self.visited.contains(&x) {
            return false;
        }

        self.visited.insert(x.clone());
        self.queue.push_back(x);
        true
    }

    /// Dequeues the frontmost item if the queue is not empty.
    pub fn pop(&mut self) -> Option<T> {
        self.queue.pop_front()
    }

    /// Gets a reference to the frontmost item if the queue is not empty.
    pub fn peek(&self) -> Option<&T> {
        self.queue.front()
    }

    pub fn len(&self) -> usize {
        self.queue.len()
    }

    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    /// Set of all items that has been pushed before.
    pub fn pushed_items(&self) -> &HashSet<T> {
        &self.visited
    }
}

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let mut queue = HashOnceQueue::new();
        assert!( queue.push(1));
        assert!( queue.push(2));
        assert!(!queue.push(1));
        assert!( queue.push(3));
        assert!( queue.push(4));
        assert!(!queue.push(2));

        assert_eq!(queue.pop(), Some(1));
        assert_eq!(queue.pop(), Some(2));
        assert_eq!(queue.pop(), Some(3));
        assert_eq!(queue.pop(), Some(4));
        assert_eq!(queue.pop(), None);
    }
}
