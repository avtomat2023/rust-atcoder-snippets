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

    fn sort_desc_by<F>(&mut self, cmp: F)
    where
        F: FnMut(&T, &T) -> std::cmp::Ordering;

    // ABC104 C
    fn sort_desc_by_key<K: Ord, F: FnMut(&T) -> K>(&mut self, key: F);

    fn sort_unstable_desc(&mut self) where T: Ord;

    fn sort_unstable_desc_by<F>(&mut self, cmp: F)
    where
        F: FnMut(&T, &T) -> std::cmp::Ordering;

    fn sort_unstable_desc_by_key<K: Ord, F: FnMut(&T) -> K>(&mut self, key: F);
}

impl<T> SortDesc<T> for [T] {
    fn sort_desc(&mut self) where T: Ord {
        self.sort_by(|x, y| y.cmp(x));
    }

    fn sort_desc_by<F>(&mut self, mut cmp: F)
    where
        F: FnMut(&T, &T) -> std::cmp::Ordering
    {
        self.sort_by(|x, y| cmp(y, x));
    }

    fn sort_desc_by_key<K: Ord, F: FnMut(&T) -> K>(&mut self, mut key: F) {
        self.sort_by_key(|x| Reverse(key(x)));
    }

    fn sort_unstable_desc(&mut self) where T: Ord {
        self.sort_unstable_by(|x, y| y.cmp(x));
    }

    fn sort_unstable_desc_by<F>(&mut self, mut cmp: F)
    where
        F: FnMut(&T, &T) -> std::cmp::Ordering
    {
        self.sort_unstable_by(|x, y| cmp(y, x));
    }

    fn sort_unstable_desc_by_key<K: Ord, F: FnMut(&T) -> K>(&mut self, mut key: F) {
        self.sort_unstable_by_key(|x| Reverse(key(x)));
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
        let first = self.next()?;
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

/// Monoid over selection of optimal value, providing `Option`-like methods.
///
/// Typical implementors are [`MaybeNeginf`](enum.MaybeNegInf.html)
/// and [`MaybeInf`](enum.MaybeInf.html).
pub trait WithCmpIdentity<T>: Sized {
    fn new(x: T) -> Self;

    fn inf() -> Self;

    fn as_option(&self) -> Option<&T>;

    fn as_option_mut(&mut self) -> Option<&mut T>;

    fn into_option(self) -> Option<T>;

    fn is_fin(&self) -> bool {
        self.as_option().is_some()
    }

    fn is_inf(&self) -> bool {
        self.as_option().is_none()
    }

    fn expect_fin(self, msg: &str) -> T {
        self.into_option().expect(msg)
    }

    fn fin(self) -> T {
        self.into_option().unwrap()
    }

    fn fin_or(self, default: T) -> T {
        self.into_option().unwrap_or(default)
    }

    fn fin_or_else<F: FnOnce() -> T>(self, f: F) -> T {
        self.into_option().unwrap_or_else(f)
    }

    fn map_or<U, F: FnOnce(T) -> U>(self, default: U, f: F) -> U {
        self.into_option().map_or(default, f)
    }

    fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        D: FnOnce() -> U,
        F: FnOnce(T) -> U
    {
        self.into_option().map_or_else(default, f).into()
    }
}

/// Negative infinite or finite value.
///
/// Typical application is `SegmentTree`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum MaybeNegInf<T> {
    Inf,
    Fin(T)
}

// TODO: Add example for segment tree
/// Alias of `MaybeNegInf`.
///
/// `MaybeNegInf` makes `Ord` into a monoid over maximum.
pub type Max<T> = MaybeNegInf<T>;

/// Positive infinite or finite value.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum MaybeInf<T> {
    Fin(T),
    Inf
}

/// Alias of `MaybeInf`.
///
/// `MaybeInf` makes `Ord` into a monoid over minimum.
pub type Min<T> = MaybeInf<T>;

macro_rules! impl_with_cmp_identity {
    ($t:ident) => {
        // Maybe it's good to have `Functor` trait. See this article:
        // https://keens.github.io/blog/2016/02/28/rustnohigherkinded_type_trait/
        impl<T> $t<T> {
            pub fn map<U: Ord, F: FnOnce(T) -> U>(self, f: F) -> $t<U> {
                match self {
                    $t::Fin(x) => $t::Fin(f(x)),
                    $t::Inf => $t::Inf
                }
            }
        }

        impl<T> WithCmpIdentity<T> for $t<T> {
            fn new(x: T) -> $t<T> { $t::Fin(x) }

            fn inf() -> $t<T> { $t::Inf }

            fn as_option(&self) -> Option<&T> {
                match self {
                    $t::Fin(x) => Some(x),
                    $t::Inf => None
                }
            }

            fn as_option_mut(&mut self) -> Option<&mut T> {
                match self {
                    $t::Fin(x) => Some(x),
                    $t::Inf => None
                }
            }

            fn into_option(self) -> Option<T> {
                match self {
                    $t::Fin(x) => Some(x),
                    $t::Inf => None
                }
            }
        }
    }
}

impl_with_cmp_identity!(MaybeNegInf);
impl_with_cmp_identity!(MaybeInf);

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

    #[test]
    fn test_maybe_neg_inf_cmp() {
        let mut seq = vec![
            MaybeNegInf::Fin(3),
            MaybeNegInf::Fin(1),
            MaybeNegInf::Inf,
            MaybeNegInf::Fin(2),
            MaybeNegInf::Inf
        ];
        seq.sort();

        let expected = vec![
            MaybeNegInf::Inf,
            MaybeNegInf::Inf,
            MaybeNegInf::Fin(1),
            MaybeNegInf::Fin(2),
            MaybeNegInf::Fin(3)
        ];
        assert_eq!(seq, expected);
    }

    #[test]
    fn test_max_cmp() {
        let mut seq = vec![
            Max::new(3), Max::new(1), Max::inf(), Max::new(2), Max::inf()
        ];
        seq.sort();

        let expected = vec![
            Max::inf(), Max::inf(), Max::new(1), Max::new(2), Max::new(3)
        ];
        assert_eq!(seq, expected);
    }

    #[test]
    fn test_maybe_inf_cmp() {
        let mut seq = vec![
            MaybeInf::Fin(3),
            MaybeInf::Fin(1),
            MaybeInf::Inf,
            MaybeInf::Fin(2),
            MaybeInf::Inf
        ];
        seq.sort();

        let expected = vec![
            MaybeInf::Fin(1),
            MaybeInf::Fin(2),
            MaybeInf::Fin(3),
            MaybeInf::Inf,
            MaybeInf::Inf
        ];
        assert_eq!(seq, expected);
    }

    #[test]
    fn test_min_cmp() {
        let mut seq = vec![
            Min::new(3), Min::new(1), Min::inf(), Min::new(2), Min::inf()
        ];
        seq.sort();

        let expected = vec![
            Min::new(1), Min::new(2), Min::new(3), Min::inf(), Min::inf()
        ];
        assert_eq!(seq, expected);
    }

    #[test]
    fn test_max_create() {
        assert_eq!(Max::new(3), MaybeNegInf::Fin(3));
        assert_eq!(Max::<i32>::inf(), MaybeNegInf::Inf);
    }

    #[test]
    fn test_max_map() {
        assert_eq!(Max::new(3).map(|x| x*2), Max::new(6));
        assert_eq!(Max::<i32>::inf().map(|x| x*2), Max::inf());
    }
}
