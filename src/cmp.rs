// ABC 038 D

#[snippet = "cmp"]
use std::cmp::{Ord, Ordering};

#[snippet = "cmp"]
#[derive(Clone, Copy, PartialEq, Eq)]
struct Reverse<T>(T);

#[snippet = "cmp"]
impl<T: PartialOrd> PartialOrd for Reverse<T> {
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
trait SortDesc<T> {
    // ABC112 D
    fn sort_desc(&mut self) where T: Ord;

    // ABC104 C
    fn sort_desc_by_key<K: Ord, F: FnMut(&T) -> K>(&mut self, f: F);

    // TODO: sort_unstable_desc_*
}

#[snippet = "cmp"]
impl<T> SortDesc<T> for [T] {
    fn sort_desc(&mut self) where T: Ord {
        self.sort();
        self.reverse();
    }

    fn sort_desc_by_key<K: Ord, F: FnMut(&T) -> K>(&mut self, mut f: F) {
        self.sort_by_key(|x| Reverse(f(x)));
    }
}

#[snippet = "cmp"]
#[derive(PartialEq, PartialOrd)]
struct Total<T: PartialOrd + PartialEq>(T);

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
    fn test_sort_by_reverse() {
        let mut vec = vec![1,5,2,4,3];
        vec.sort_by_key(|&x| Reverse(x));
        assert_eq!(vec, vec![5,4,3,2,1]);
    }

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
    fn test_total() {
        let mut vec = vec![1.0, 3.0, 2.0, 5.0, 4.0];
        vec.sort_by_key(|&x| Total(x));
        assert_eq!(vec, vec![1.0, 2.0, 3.0, 4.0, 5.0]);
    }
}
