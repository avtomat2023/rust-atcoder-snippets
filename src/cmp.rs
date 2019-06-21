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
#[derive(Clone, Copy, PartialEq, Eq)]
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
#[derive(PartialEq, PartialOrd)]
pub struct Total<T: PartialOrd + PartialEq>(pub T);

#[snippet = "cmp"]
impl<T: PartialOrd + PartialEq> Eq for Total<T> {}

#[snippet = "cmp"]
impl<T: PartialOrd + PartialEq> Ord for Total<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

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
}
