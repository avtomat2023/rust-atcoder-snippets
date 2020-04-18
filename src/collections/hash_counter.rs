//! Counter by a hash map from keys to counter values.
//!
//! AGC031 Aとかが楽に解ける

use crate::read::{Readable, ReadableFromLine, read_words_into_vec, split_into_words_for_collection};

// BEGIN SNIPPET hash_counter

/// Counter by a hash map from keys to counter values.
///
/// Similar to Python's `collections.Counter`.
///
/// `HashCounter` is readable from a line of stdin.
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::collections::hash_counter::*;
/// # use atcoder_snippets::read::*;
/// // stdin: "5 a a b b b"
/// read!(len = usize, counter = HashCounter<char>);
/// ```
#[derive(Clone)]
pub struct HashCounter<T> {
    counter: std::collections::HashMap<T, usize>
}

pub struct HashCounterItemRef<'a, 'b, T, Q: ?Sized>
where
    T: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
    Q: Eq + std::hash::Hash
{
    counter: &'a mut HashCounter<T>,
    key: &'b Q,
    item: *mut usize
}

impl<T, Q: ?Sized> std::ops::Deref for HashCounterItemRef<'_, '_, T, Q>
where
    T: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
    Q: Eq + std::hash::Hash
{
    type Target = usize;

    fn deref(&self) -> &usize {
        unsafe { self.item.as_ref() }.unwrap()
    }
}

impl<T, Q: ?Sized> std::ops::DerefMut for HashCounterItemRef<'_, '_, T, Q>
where
    T: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
    Q: Eq + std::hash::Hash
{
    fn deref_mut(&mut self) -> &mut usize {
        unsafe { self.item.as_mut() }.unwrap()
    }
}

impl<T, Q: ?Sized> Drop for HashCounterItemRef<'_, '_, T, Q>
where
    T: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
    Q: Eq + std::hash::Hash
{
    fn drop(&mut self) {
        if **self == 0 {
            self.counter.counter.remove(self.key);
        }
    }
}

// TODO: Use impl Iterator if possible

/// An iterator created by [`iter`](struct.HashCounter.html#method.iter) method on counters.
pub struct HashCounterIter<'a, T: 'a> {
    iter: std::collections::hash_map::Iter<'a, T, usize>
}

impl<'a, T> Iterator for HashCounterIter<'a, T> {
    type Item = (&'a T, usize);

    fn next(&mut self) -> Option<(&'a T, usize)> {
        while let Some((key, &count)) = self.iter.next() {
            if count > 0 {
                return Some((key, count))
            }
        }
        None
    }
}

/// An iterator created by `into_iter` method on counters.
pub struct HashCounterIntoIter<T> {
    iter: std::collections::hash_map::IntoIter<T, usize>
}

impl<'a, T> Iterator for HashCounterIntoIter<T> {
    type Item = (T, usize);

    fn next(&mut self) -> Option<(T, usize)> {
        while let Some((key, count)) = self.iter.next() {
            if count > 0 {
                return Some((key, count))
            }
        }
        None
    }
}

/// An iterator created by [`values`](struct.HashCounter.html#method.values) method on counters.
pub struct HashCounterValues<'a, T: 'a> {
    iter: std::collections::hash_map::Values<'a, T, usize>
}

impl<'a, T> Iterator for HashCounterValues<'a, T> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        while let Some(&n) = self.iter.next() {
            if n > 0 {
                return Some(n)
            }
        }
        None
    }
}

impl<T: Eq + std::hash::Hash> HashCounter<T> {
    /// Creates an empty counter.
    pub fn new() -> HashCounter<T> {
        HashCounter { counter: std::collections::HashMap::new() }
    }

    /// Creates an empty counter with the specified capacity.
    pub fn with_capacity(capacity: usize) -> HashCounter<T> {
        HashCounter { counter: std::collections::HashMap::with_capacity(capacity) }
    }

    // TODO: pub fn capacity

    /// Gets how many keys the counter contains.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::hash_counter::*;
    /// let counter = hash_counter![1, 1, 2, 2, 2, 3, 3, 4, 5, 5];
    /// assert_eq!(counter.keys_len(), 5);
    /// ```
    pub fn keys_len(&self) -> usize {
        self.counter.len()
    }

    /// Gets the counter value of `key`.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::hash_counter::*;
    /// let counter = hash_counter![1, 1, 2, 2, 2, 3, 3];
    /// assert_eq!(counter.count(&2), 3);
    /// assert_eq!(counter.count(&0), 0);
    /// ```
    pub fn count<Q: ?Sized>(&self, key: &Q) -> usize
    where
        T: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
        Q: Eq + std::hash::Hash
    {
        self.counter.get(key).cloned().unwrap_or(0)
    }

    /// Increments the counter value for `key`.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::hash_counter::*;
    /// let mut counter = hash_counter![1, 1];
    /// counter.insert(1);
    /// assert_eq!(counter.count(&1), 3);
    /// ```
    pub fn insert(&mut self, key: T) {
        *self.counter.entry(key).or_insert(0) += 1;
    }

    /// Decrements the counter value for `key`.
    ///
    /// If the counter is already 0, does nothing and returns false.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::hash_counter::*;
    /// let mut counter = hash_counter![1];
    /// assert!(counter.remove(&1));
    /// assert_eq!(counter.count(&1), 0);
    /// assert!(!counter.remove(&1));
    /// assert_eq!(counter.count(&1), 0);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> bool
    where
        T: std::borrow::Borrow<Q>,
        Q: Eq + std::hash::Hash
    {
        let removes;
        match self.counter.get_mut(key) {
            None => return false,
            Some(x) => {
                *x -= 1;
                removes = *x == 0
            }
        }
        if removes {
            self.counter.remove(key);
        }
        true
    }

    /// Gets the mutable reference to the counter value of `key`.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::hash_counter::*;
    /// let mut counter = hash_counter![1, 1, 2, 2, 2, 3, 3];
    /// *counter.at(&2) += 10;
    /// assert_eq!(counter.count(&2), 13);
    /// *counter.at(&0) += 10;
    /// assert_eq!(counter.count(&0), 10);
    /// ```
    pub fn at<'a, 'b, Q: ?Sized>(&'a mut self, key: &'b Q) -> HashCounterItemRef<'a, 'b, T, Q>
    where
        T: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
        Q: Eq + std::hash::Hash + std::borrow::ToOwned<Owned=T>
    {
        let item = self.counter.entry(key.to_owned()).or_insert(0) as *mut usize;
        // TODO: use field init shorthand
        HashCounterItemRef {
            counter: self,
            key: key,
            item: item
        }
    }

    /// Creates an iterator yielding how many items are contained in the counter
    /// for each kind of item.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::hash_counter::*;
    /// let counter = hash_counter!['a', 'a', 'b', 'c', 'c', 'c', 'd', 'd'];
    /// let mut values: Vec<usize> = counter.values().collect();
    /// values.sort();
    /// assert_eq!(values, vec![1, 2, 2, 3]);
    /// ```
    pub fn values(&self) -> HashCounterValues<T> {
        HashCounterValues { iter: self.counter.values() }
    }

    /// Creates an iterator yielding (&key, count) pairs.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::hash_counter::*;
    /// let counter = hash_counter!['a', 'b', 'a'];
    /// assert!(counter.iter().find(|&(&key, count)| key == 'a' && count == 2).is_some())
    /// ```
    pub fn iter(&self) -> HashCounterIter<T> {
        HashCounterIter { iter: self.counter.iter() }
    }
}

// HashCounter doesn't provide indexing methods
// because they looks that the operation may panic.

impl<T: std::hash::Hash + Eq> std::iter::FromIterator<T> for HashCounter<T> {
    fn from_iter<I>(iter: I) -> HashCounter<T> where I: IntoIterator<Item=T> {
        let mut counter = HashCounter::new();
        for item in iter {
            *counter.counter.entry(item).or_insert(0) += 1;
        }
        counter
    }
}

impl<T: std::hash::Hash + Eq> std::iter::IntoIterator for HashCounter<T> {
    type Item = (T, usize);
    type IntoIter = HashCounterIntoIter<T>;

    fn into_iter(self) -> HashCounterIntoIter<T> {
        HashCounterIntoIter { iter: self.counter.into_iter() }
    }
}

impl<'a, T: std::hash::Hash + Eq> std::iter::IntoIterator for &'a HashCounter<T> {
    type Item = (&'a T, usize);
    type IntoIter = HashCounterIter<'a, T>;

    fn into_iter(self) -> HashCounterIter<'a, T> {
        HashCounterIter { iter: self.counter.iter() }
    }
}

#[macro_export]
macro_rules! hash_counter {
    ($($item:expr),*) => {
        {
            let mut counter = HashCounter::new();
            $( *counter.at(&$item) += 1; )*
            counter
        }
    }
}

readable_collection!(U: Eq, std::hash::Hash => HashCounter<U>, HashCounter<U::Output>);

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_into_iter() {
        let counter = hash_counter!['a', 'b', 'a'];
        assert!(
            counter.into_iter()
                .find(|&(key, count)| key == 'a' && count == 2)
                .is_some()
        );
    }

    #[test]
    fn test_item_ref_remove() {
        let mut counter = hash_counter!['a', 'b', 'a'];
        *counter.at(&'a') = 0;
        assert!(counter.keys_len() == 1);
    }

    #[test]
    fn test_insert_remove() {
        let mut counter = hash_counter!['a', 'b', 'a'];
        counter.insert('a');
        assert_eq!(counter.count(&'a'), 3);

        counter.insert('c');
        assert_eq!(counter.count(&'c'), 1);

        assert!(counter.remove(&'b'));
        assert_eq!(counter.count(&'b'), 0);
        assert_eq!(counter.keys_len(), 2);

        assert!(!counter.remove(&'b'));
        assert_eq!(counter.count(&'b'), 0);
        assert_eq!(counter.keys_len(), 2);
    }
}
