// ABC 038 D
struct SliceGroupBy<'a, T: 'a, K: Eq, F: Fn(&T) -> K> {
    key_fn: F,
    slice: &'a [T],
    index: usize
}

impl<'a, T, K: Eq, F: Fn(&T) -> K> Iterator for SliceGroupBy<'a, T, K, F> {
    type Item = (K, &'a [T]);

    fn next(&mut self) -> Option<(K, &'a [T])> {
        if self.index == self.slice.len() {
            return None;
        }

        let start = self.index;
        let key = (self.key_fn)(&self.slice[self.index]);
        self.index += 1;
        while self.index < self.slice.len() &&
            (self.key_fn)(&self.slice[self.index]) == key {
            self.index += 1;
        }

        Some((key, &self.slice[start..self.index]))
    }
}

trait SliceGroupByTrait<T, K: Eq, F: Fn(&T) -> K> {
    fn group_by(&self, key_fn: F) -> SliceGroupBy<T, K, F>;
}

impl<T, K: Eq, F: Fn(&T) -> K> SliceGroupByTrait<T, K, F> for [T] {
    fn group_by(&self, key_fn: F) -> SliceGroupBy<T, K, F> {
        SliceGroupBy { key_fn: key_fn, slice: self, index: 0 }
    }
}

#[snippet = "slice"]
struct Permutations<'a, T: 'a> {
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

#[snippet = "slice"]
trait SliceExt<T> {
    // ABC103 A
    fn permutations(&self) -> Permutations<T>;
}

#[snippet = "slice"]
impl<T> SliceExt<T> for [T] {
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
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_group_by() {
        let seq = [('a', 0), ('a', 1), ('a', 2), ('b', 0), ('a', 0), ('a', 1)];
        let grouped: Vec<(char, Vec<(char, i32)>)> = seq
            .group_by(|&(ch, _)| ch)
            .map(|(ch, pairs)| (ch, pairs.to_vec()))
            .collect();
        assert_eq!(grouped,
                   vec![('a', vec![('a', 0), ('a', 1), ('a', 2)]),
                        ('b', vec![('b', 0)]),
                        ('a', vec![('a', 0), ('a', 1)])]);
    }

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
}
