//! Enriches slices.

// TODO: ABC038 D, AGC026 A
/// An iterator created by [`group_by`](trait.SliceExt.html#tymethod.group_by) method on slices.
#[snippet = "slice"]
pub struct SliceGroupBy<'a, T: 'a, K: Eq, F: Fn(&T) -> K> {
    key_fn: F,
    rest: &'a [T],
}

#[snippet = "slice"]
impl<'a, T, K: Eq, F: Fn(&T) -> K> Iterator for SliceGroupBy<'a, T, K, F> {
    type Item = (K, &'a [T]);

    fn next(&mut self) -> Option<(K, &'a [T])> {
        if self.rest.is_empty() {
            return None;
        }


        let key = (self.key_fn)(&self.rest[0]);
        let mut end = 1;
        while end < self.rest.len() && (self.key_fn)(&self.rest[end]) == key {
            end += 1;
        }

        let (left, right) = self.rest.split_at(end);
        self.rest = right;
        Some((key, left))
    }
}

/// An iterator created by [`permutations`](trait.SliceExt.html#tymethod.permutations)
/// method on slices.
#[snippet = "slice"]
pub struct Permutations<'a, T: 'a> {
    items: &'a [T],
    indices: Option<Vec<usize>>,
    is_first: bool,
}

// I don't understand why T: 'a works.
#[snippet = "slice"]
impl<'a, T: 'a> Iterator for Permutations<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Vec<&'a T>> {
        if !self.is_first {
            let indices_opt = self.indices.take();
            if let Some(indices) = indices_opt {
                self.indices = next_permutation(indices);
            }
        } else {
            self.is_first = false;
        }

        self.indices.as_ref().map(|indices| {
            indices.into_iter().map(|&i| &self.items[i]).collect()
        })
    }
}

// https://stackoverflow.com/questions/11483060/stdnext-permutation-implementation-explanation
#[snippet = "slice"]
fn next_permutation(mut indices: Vec<usize>) -> Option<Vec<usize>> {
    (0 .. indices.len().saturating_sub(1)).rev()
        .find(|&left| indices[left] < indices[left+1])
        .map(|left| {
            let right = (0..indices.len()).rev()
                .find(|&right| indices[left] < indices[right])
                .unwrap();
            indices.swap(left, right);
            indices[left+1..].reverse();
            indices
        })
}

fn count_inversions_sub<T: Clone + Ord>(seq: &[T]) -> (Vec<T>, usize) {
    if seq.len() <= 1 {
        (seq.to_vec(), 0)
    } else {
        let mid = seq.len() / 2;
        let (sub1, inv1) = count_inversions_sub(&seq[..mid]);
        let (sub2, inv2) = count_inversions_sub(&seq[mid..]);

        let mut sorted = Vec::new();
        let (mut i1, mut i2) = (0, 0);
        let mut inv = 0;

        loop {
            match (sub1.get(i1), sub2.get(i2)) {
                (Some(x1), Some(x2)) => {
                    if x1 <= x2 {
                        sorted.push(x1.clone());
                        i1 += 1;
                    } else {
                        inv += sub1.len() - i1;
                        sorted.push(x2.clone());
                        i2 += 1;
                    }
                },
                (Some(_), None) => {
                    sorted.extend(sub1[i1..].iter().cloned());
                    // i1 = sub1.len();
                    break;
                },
                (None, Some(_)) => {
                    sorted.extend(sub2[i2..].iter().cloned());
                    // i2 = sub2.len();
                    break;
                },
                (None, None) => break,
            }
        }

        (sorted, inv + inv1 + inv2)
    }
}

/// Enriches slices by adding various methods.
#[snippet = "slice"]
pub trait SliceExt<T> {
    /// Returns an iterator yielding groups.
    ///
    /// Each group is a pair of key and subslice.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate atcoder_snippets;
    /// # use atcoder_snippets::slice::*;
    /// let seq = [('a', 0), ('a', 1), ('a', 2), ('b', 0), ('a', 0), ('a', 1)];
    /// let grouped: Vec<(char, Vec<(char, i32)>)> = seq
    ///     .group_by(|&(ch, _)| ch)
    ///     .map(|(ch, pairs)| (ch, pairs.to_vec()))
    ///     .collect();
    /// assert_eq!(grouped,
    ///            vec![('a', vec![('a', 0), ('a', 1), ('a', 2)]),
    ///                 ('b', vec![('b', 0)]),
    ///                 ('a', vec![('a', 0), ('a', 1)])]);
    /// ```
    fn group_by<K: Eq, F: Fn(&T) -> K>(&self, key_fn: F) -> SliceGroupBy<T, K, F>;

    // TODO: ABC103 A
    /// Returns an iterator yielding all permutations of the slice.
    ///
    /// Each permutation is a `Vec` of shared references to items in the slice.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate atcoder_snippets;
    /// # use atcoder_snippets::slice::*;
    /// let mut perms = [1, 2, 3].permutations();
    /// assert_eq!(perms.next(), Some(vec![&1, &2, &3]));
    /// assert_eq!(perms.next(), Some(vec![&1, &3, &2]));
    /// assert_eq!(perms.next(), Some(vec![&2, &1, &3]));
    /// assert_eq!(perms.next(), Some(vec![&2, &3, &1]));
    /// assert_eq!(perms.next(), Some(vec![&3, &1, &2]));
    /// assert_eq!(perms.next(), Some(vec![&3, &2, &1]));
    /// assert_eq!(perms.next(), None);
    /// ```
    fn permutations(&self) -> Permutations<T>;

    /// Counts the number of pairs of indices `(i, j)`
    /// satisfing `i < j` and `self[i] > self[j]`.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate atcoder_snippets;
    /// # use atcoder_snippets::slice::*;
    /// assert_eq!([1, 0, 3, 2, 0].count_inversions(), 5);
    /// ```
    fn count_inversions(&self) -> usize where T: Clone + Ord;
}

#[snippet = "slice"]
impl<T> SliceExt<T> for [T] {
    fn group_by<K: Eq, F: Fn(&T) -> K>(&self, key_fn: F) -> SliceGroupBy<T, K, F> {
        SliceGroupBy { key_fn: key_fn, rest: self }
    }

    fn permutations(&self) -> Permutations<T> {
        let indices = if self.is_empty() {
            None
        } else {
            Some((0..self.len()).collect())
        };

        Permutations {
            items: self,
            indices: indices,
            is_first: true,
        }
    }

    fn count_inversions(&self) -> usize where T: Clone + Ord {
        count_inversions_sub(self).1
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_next_permutations() {
        fn to_vec<'a, I: Iterator<Item = Vec<&'a i32>>>(permutations: I) -> Vec<Vec<i32>> {
            permutations.map(|xs| xs.into_iter().cloned().collect()).collect()
        }
        assert_eq!(to_vec(Vec::new().permutations()), Vec::<Vec<i32>>::new());
        assert_eq!(to_vec(vec![1].permutations()), vec![vec![1]]);
        assert_eq!(to_vec(vec![1, 2].permutations()), vec![vec![1, 2], vec![2, 1]]);
        assert_eq!(to_vec(vec![1, 2, 3].permutations()),
                   vec![vec![1, 2, 3], vec![1, 3, 2],
                        vec![2, 1, 3], vec![2, 3, 1],
                        vec![3, 1, 2], vec![3, 2, 1]]);
    }

    #[test]
    fn test_count_inversions() {
        assert_eq!(Vec::<i32>::new().count_inversions(), 0);
        assert_eq!([0].count_inversions(), 0);
        assert_eq!([0, 1].count_inversions(), 0);
        assert_eq!([1, 0].count_inversions(), 1);
        assert_eq!([2, 1, 0].count_inversions(), 3);
        assert_eq!([0, 0, 0, 0, 0, 0, 0, 0, 0].count_inversions(), 0);
        assert_eq!([0, 1, 2, 3, 4, 5, 6, 7, 8].count_inversions(), 0);
        assert_eq!([2, 2, 2, 1, 1, 1, 0, 0, 0].count_inversions(), 27);
    }
}
