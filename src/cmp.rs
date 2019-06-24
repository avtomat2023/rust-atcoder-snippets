//! Comparation and sorting.

// ABC 038 D

#[snippet = "cmp"]
use std::cmp::{Ord, Ordering};

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
#[snippet = "cmp"]
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Hash)]
pub struct Reverse<T: Ord>(pub T);

#[snippet = "cmp"]
impl<T: Ord> PartialOrd for Reverse<T> {
    fn partial_cmp(&self, other: &Reverse<T>) -> Option<Ordering> {
        other.0.partial_cmp(&self.0)
    }
}

#[snippet = "cmp"]
impl<T: Ord> Ord for Reverse<T> {
    fn cmp(&self, other: &Reverse<T>) -> Ordering {
        other.0.cmp(&self.0)
    }
}

#[snippet = "cmp"]
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

#[snippet = "cmp"]
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
#[snippet = "cmp"]
#[derive(Clone, Copy, PartialEq, PartialOrd, Debug, Default, Hash)]
pub struct Total<T: PartialOrd + PartialEq>(pub T);

#[snippet = "cmp"]
impl<T: PartialOrd + PartialEq> Eq for Total<T> {}

#[snippet = "cmp"]
impl<T: PartialOrd + PartialEq> Ord for Total<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Monoid over selection of optimal value, providing `Option`-like methods.
///
/// Typical implementors are [`MaybeNeginf`](enum.MaybeNegInf.html)
/// and [`MaybeInf`](enum.MaybeInf.html).
#[snippet = "cmp"]
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
#[snippet = "cmp"]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum MaybeNegInf<T> {
    Inf,
    Fin(T)
}

// TODO: Add example for segment tree
/// Alias of `MaybeNegInf`.
///
/// `MaybeNegInf` makes `Ord` into a monoid over maximum.
#[snippet = "cmp"]
pub type Max<T> = MaybeNegInf<T>;

/// Positive infinite or finite value.
#[snippet = "cmp"]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum MaybeInf<T> {
    Fin(T),
    Inf
}

/// Alias of `MaybeInf`.
///
/// `MaybeInf` makes `Ord` into a monoid over minimum.
#[snippet = "cmp"]
pub type Min<T> = MaybeInf<T>;

#[snippet = "cmp"]
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

#[snippet = "cmp"] impl_with_cmp_identity!(MaybeNegInf);
#[snippet = "cmp"] impl_with_cmp_identity!(MaybeInf);

#[cfg(test)]
mod tests {
    use super::*;

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
