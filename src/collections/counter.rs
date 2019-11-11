//! Multiset similar to Python's collections.Counter.
//!
//! AGC031 Aとかが楽に解ける

use std;

// BEGIN SNIPPET counter

/// An multiset similar to Python's collections.Counter.
#[derive(Clone)]
pub struct HashCounter<T: Eq + std::hash::Hash> {
    counter: std::collections::HashMap<T, usize>
}

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
    /// Creates a new counter.
    pub fn new() -> HashCounter<T> {
        HashCounter { counter: std::collections::HashMap::new() }
    }

    pub fn with_capacity(capacity: usize) -> HashCounter<T> {
        HashCounter { counter: std::collections::HashMap::with_capacity(capacity) }
    }

    /// Creates an iterator yielding how many items are contained in the counter
    /// for each kind of item.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::counter::*;
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
    /// # use atcoder_snippets::collections::counter::*;
    /// let counter = hash_counter!['a', 'b', 'a'];
    /// assert!(counter.iter().find(|&(&key, count)| key == 'a' && count == 2).is_some())
    /// ```
    pub fn iter(&self) -> HashCounterIter<T> {
        HashCounterIter { iter: self.counter.iter() }
    }
}

static HASH_COUNTER_ZERO: usize = 0;

impl<'a, T, Q: ?Sized> std::ops::Index<&'a Q> for HashCounter<T>
where
    T: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
    Q: Eq + std::hash::Hash
{
    type Output = usize;

    fn index(&self, key: &Q) -> &usize {
        // Rust 1.15.1 doesn't allow the following code
        // self.counter.get(key).unwrap_or(&0)

        self.counter.get(key).unwrap_or(&HASH_COUNTER_ZERO)
    }
}

impl<'a, T, Q: ?Sized> std::ops::IndexMut<&'a Q> for HashCounter<T>
where
    T: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
    Q: Eq + std::hash::Hash + std::borrow::ToOwned<Owned=T>
{
    fn index_mut(&mut self, key: &Q) -> &mut usize {
        // Calling `to_owned` every time may be inefficient,
        // but I can't cope with ownership problem.
        self.counter.entry(key.to_owned()).or_insert(0)
    }
}

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

#[macro_export]
macro_rules! hash_counter {
    ($($item:expr),*) => {
        {
            let mut counter = HashCounter::new();
            $( counter[&$item] += 1; )*
            counter
        }
    }
}

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
}
