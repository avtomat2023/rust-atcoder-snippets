//! Comparation and sorting.

// ABC 038 D

// BEGIN SNIPPET cmp

use std::cmp::{Ord, Ordering};

/// Gets `(min, max)`.
///
/// When the two arguments are equal, returns `(a, b)`.
pub fn minmax<T: Ord>(a: T, b: T) -> (T, T) {
    if a <= b { (a, b) } else { (b, a) }
}

/// Assigns the given value if it is smaller than the current one.
///
/// # Example
///
/// Floyd-Warshall algorithm can be written consicely using `chmin`.
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// const INF: u32 = 1_000_000_000;
/// let mut cost = vec![
///     vec![  0,   1, INF, INF,   1],
///     vec![  1,   0,   1, INF, INF],
///     vec![INF, INF,   0,   1,   3],
///     vec![INF, INF, INF,   0,   1],
///     vec![INF,   1, INF, INF,   0]
/// ];
///
/// for mid in 0..5 {
///     for u in 0..5 {
///         for v in 0..5 {
///              chmin!(cost[u][v], cost[u][mid] + cost[mid][v]);
///         }
///     }
/// }
/// assert_eq!(cost, vec![
///     vec![0, 1, 2, 3, 1],
///     vec![1, 0, 1, 2, 2],
///     vec![4, 3, 0, 1, 2],
///     vec![3, 2, 3, 0, 1],
///     vec![2, 1, 2, 3, 0]
/// ]);
/// ```
#[macro_export]
macro_rules! chmin {
    ($place: expr, $expr: expr) => {
        let value = $expr;
        if value < $place {
            $place = value;
        }
    }
}

/// Assigns the given value if it is greater than the current one.
#[macro_export]
macro_rules! chmax {
    ($place: expr, $expr: expr) => {
        let value = $expr;
        if value > $place {
            $place = value;
        }
    }
}

/// For reversed ordering.
///
/// See [Qiita article by hatoo](https://qiita.com/hatoo@github/items/fa14ad36a1b568d14f3e#%E9%80%86%E9%A0%86%E3%81%A7%E3%80%87%E3%80%87%E3%81%99%E3%82%8B%E3%81%AB%E3%81%AF).
///
/// # Example
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::cmp::*;
/// let mut seq = vec![1, 5, 3, 2, 4];
/// seq.sort_by_key(|&x| Reverse(x));
/// assert_eq!(seq, vec![5, 4, 3, 2, 1]);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Hash)]
pub struct Reverse<T: Ord>(pub T);

impl<T: Ord> PartialOrd for Reverse<T> {
    fn partial_cmp(&self, other: &Reverse<T>) -> Option<Ordering> {
        other.0.partial_cmp(&self.0)
    }
}

impl<T: Ord> Ord for Reverse<T> {
    fn cmp(&self, other: &Reverse<T>) -> Ordering {
        other.0.cmp(&self.0)
    }
}

pub trait SortDesc<T> {
    // ABC112 D
    fn sort_desc(&mut self) where T: Ord;

    // ABC104 C
    fn sort_desc_by_key<K: Ord, F: FnMut(&T) -> K>(&mut self, f: F);

    // TODO: sort_unstable_desc_*
}

impl<T> SortDesc<T> for [T] {
    fn sort_desc(&mut self) where T: Ord {
        self.sort();
        self.reverse();
    }

    fn sort_desc_by_key<K: Ord, F: FnMut(&T) -> K>(&mut self, mut f: F) {
        self.sort_by_key(|x| Reverse(f(x)));
    }
}

/// Forcibly makes `PartialOrd` into `Ord`, typically for sorting floating point numbers.
///
/// # Example
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::cmp::*;
/// let mut seq = vec![1.0, 5.0, 3.0, 2.0, 4.0];
/// seq.sort_by_key(|&x| Total(x));
/// assert_eq!(seq, vec![1.0, 2.0, 3.0, 4.0, 5.0]);
/// ```
#[derive(Clone, Copy, PartialEq, PartialOrd, Debug, Default, Hash)]
pub struct Total<T: PartialOrd + PartialEq>(pub T);

impl<T: PartialOrd + PartialEq> Eq for Total<T> {}

impl<T: PartialOrd + PartialEq> Ord for Total<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Enriches iterators by adding `minmax` method.
pub trait IteratorMinmax: Iterator {
    /// Gets `(min, max)`.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// When there are multiple mininum or multiple maximum,
    /// returns the first ones as min and max.
    ///
    /// Only when the iterator has only one item, it is cloned.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::cmp::*;
    /// let seq = vec![5, 3, 2, 0, 4, 1];
    /// assert_eq!(seq.into_iter().minmax().unwrap(), (0, 5));
    /// ```
    fn minmax(self) -> Option<(Self::Item, Self::Item)>;

    /// Gets `(min, max)` compared by `key_fn`.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// When there are multiple mininum or multiple maximum,
    /// returns the first ones as min and max.
    ///
    /// Only when the iterator has only one item, it is cloned.
    fn minmax_by_key<K, F>(self, key_fn: F) -> Option<(Self::Item, Self::Item)>
    where
        K: Ord,
        F: FnMut(&Self::Item) -> K;

    /// Gets `(min, max)` compared by `compare`.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// When there are multiple mininum or multiple maximum,
    /// returns the first ones as min and max.
    ///
    /// Only when the iterator has only one item, it is cloned.
    fn minmax_by<F>(self, compare: F) -> Option<(Self::Item, Self::Item)>
    where
        F: FnMut(&Self::Item, &Self::Item) -> Ordering;
}

impl<T: Ord + Clone, I: Iterator<Item=T>> IteratorMinmax for I {
    fn minmax(self) -> Option<(Self::Item, Self::Item)> {
        self.minmax_by(|a, b| a.cmp(b))
    }

    fn minmax_by_key<K, F>(self, mut key_fn: F) -> Option<(Self::Item, Self::Item)>
    where
        K: Ord,
        F: FnMut(&Self::Item) -> K
    {
        self.minmax_by(|a, b| key_fn(a).cmp(&key_fn(b)))
    }

    fn minmax_by<F>(mut self, mut compare: F) -> Option<(Self::Item, Self::Item)>
    where
        F: FnMut(&Self::Item, &Self::Item) -> Ordering
    {
        let first = match self.next() {
            Some(x) => x,
            None => return None
        };
        let second = match self.next() {
            Some(x) => x,
            None => return Some((first.clone(), first))
        };
        let mut result = minmax(first, second);
        while let Some(x) = self.next() {
            let (min, max) = result;
            result = if compare(&x, &min) == Ordering::Less {
                (x, max)
            } else if compare(&max, &x) == Ordering::Less {
                (min, x)
            } else {
                (min, max)
            };
        }
        Some(result)
    }
}

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter;

    #[test]
    fn test_sort_desc() {
        let mut vec = vec![1,5,2,4,3];
        vec.sort_desc();
        assert_eq!(vec, vec![5,4,3,2,1]);
    }

    #[test]
    fn test_sort_desc_by_key() {
        let mut vec = vec!["1", "12345", "12", "1234", "123"];
        vec.sort_desc_by_key(|s| s.len());
        assert_eq!(vec, vec!["12345", "1234", "123", "12", "1"]);
    }

    #[test]
    fn test_minmax() {
        assert_eq!(minmax(0, 0), (0, 0));
        assert_eq!(minmax(0, 1), (0, 1));
        assert_eq!(minmax(1, 0), (0, 1));
    }

    #[test]
    fn test_iter_minmax() {
        assert_eq!(iter::empty::<i32>().minmax(), None);
        assert_eq!(iter::once(0).minmax(), Some((0, 0)));
        assert_eq!(vec![0, 0].into_iter().minmax(), Some((0, 0)));
        assert_eq!(vec![0, 1].into_iter().minmax(), Some((0, 1)));
        assert_eq!(vec![1, 0].into_iter().minmax(), Some((0, 1)));
        assert_eq!(vec![3, 2, 5, 1, 0, 4].into_iter().minmax(), Some((0, 5)));
    }

    #[test]
    fn test_iter_minmax_by_key() {
        let seq = vec![(0, 'a'), (0, 'b')];
        assert_eq!(seq.into_iter().minmax_by_key(|&(i, _)| i), Some(((0, 'a'), (0, 'b'))));

        let seq = vec![
            (3, 'a'),
            (5, 'b'),
            (2, 'c'),
            (5, 'd'),
            (1, 'e'),
            (0, 'f'),
            (5, 'g'),
            (4, 'h'),
            (0, 'i'),
        ];
        assert_eq!(seq.into_iter().minmax_by_key(|&(i, _)| i), Some(((0, 'f'), (5, 'b'))));
    }
}
