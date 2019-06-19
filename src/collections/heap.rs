#[snippet = "heap"]
mod max_heap_internal {
    use std::cmp::Ordering::{self, *};

    /// heap_indexは1以上でなければならない
    pub fn parent_of(pos: usize) -> usize {
        (pos - 1) / 2
    }

    pub fn left_of(pos: usize) -> usize {
        pos * 2 + 1
    }

    pub fn right_of(pos: usize) -> usize {
        left_of(pos) + 1
    }

    pub fn build<T, F: Fn(&T, &T) -> Ordering + Copy>(vec: &mut Vec<T>, cmp: F) {
        for i in (0..vec.len()/2).rev() {
            sift_down(vec, i, cmp)
        }
    }

    /// self.heapのpos番目の要素を木の深い方へ滑り落とし、完全なMaxヒープを作る
    ///
    /// pos番目の要素を根とする部分ヒープは、ヒープ条件を満たしていなければならない
    ///
    /// pos < self.heap.len()でなければならない
    pub fn sift_down<T, F: Fn(&T, &T) -> Ordering + Copy>(heap: &mut Vec<T>, pos: usize, cmp: F) {
        let l = left_of(pos);
        let next = if l < heap.len() && cmp(&heap[pos], &heap[l]) == Less {
            l
        } else {
            pos
        };

        let r = right_of(pos);
        let next = if r < heap.len() && cmp(&heap[next], &heap[r]) == Less {
            r
        } else {
            next
        };

        if next != pos {
            heap.swap(pos, next);
            sift_down(heap, next, cmp);
        }
    }

    pub fn sift_up<T, F: Fn(&T, &T) -> Ordering + Copy>(heap: &mut Vec<T>, pos: usize, cmp: F) {
        if pos == 0 {
            return;
        }

        let parent = parent_of(pos);
        if cmp(&heap[parent], &heap[pos]) == Less {
            heap.swap(parent, pos);
            sift_up(heap, parent, cmp);
        }
    }
}

#[snippet = "heap"]
#[derive(Clone)]
pub struct MaxHeap<T, F> {
    heap: Vec<T>,
    cmp: F
}

#[snippet = "heap"]
impl<T, F: Fn(&T, &T) -> std::cmp::Ordering> MaxHeap<T, F> {
    pub fn new_by(cmp: F) -> MaxHeap<T, F> {
        MaxHeap {
            heap: Vec::new(),
            cmp: cmp
        }
    }

    pub fn from_vec_by(mut vec: Vec<T>, cmp: F) -> MaxHeap<T, F> {
        use self::max_heap_internal::*;

        build(&mut vec, &cmp);
        MaxHeap {
            heap: vec,
            cmp: cmp
        }
    }

    pub fn push(&mut self, x: T) {
        use self::max_heap_internal::*;

        self.heap.push(x);
        let last = self.heap.len() - 1;
        sift_up(&mut self.heap, last, &self.cmp);
    }

    pub fn pop(&mut self) -> Option<T> {
        use self::max_heap_internal::*;

        if !self.heap.is_empty() {
            let max = self.heap.swap_remove(0);
            sift_down(&mut self.heap, 0, &self.cmp);
            Some(max)
        } else {
            None
        }
    }
}

#[snippet = "heap"]
impl<T: Ord> MaxHeap<T, fn(&T, &T) -> std::cmp::Ordering> {
    pub fn new() -> MaxHeap<T, fn(&T, &T) -> std::cmp::Ordering> {
        MaxHeap::new_by(Ord::cmp)
    }

    pub fn from_vec(vec: Vec<T>) -> MaxHeap<T, fn(&T, &T) -> std::cmp::Ordering> {
        MaxHeap::from_vec_by(vec, Ord::cmp)
    }
}

#[snippet = "heap"]
impl<T, F> MaxHeap<T, F> {
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    pub fn peek(&self) -> Option<&T> {
        self.heap.get(0)
    }

    pub fn iter(&self) -> std::slice::Iter<T> {
        self.heap.iter()
    }

    pub fn into_vec(self) -> Vec<T> {
        self.heap
    }
}

#[snippet = "heap"]
impl<T: std::fmt::Debug, F> std::fmt::Debug for MaxHeap<T, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[snippet = "heap"]
impl<'a, T, F> IntoIterator for &'a MaxHeap<T, F> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> std::slice::Iter<'a, T> {
        self.iter()
    }
}

#[snippet = "heap"]
impl<T, F> IntoIterator for MaxHeap<T, F> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> std::vec::IntoIter<T> {
        self.heap.into_iter()
    }
}

#[snippet = "heap"]
pub struct MinHeap<T, F> {
    heap: Vec<T>,
    cmp: F
}

#[snippet = "heap"]
impl<T, F: Fn(&T, &T) -> std::cmp::Ordering + Clone> MinHeap<T, F> {
    pub fn new_by(cmp: F) -> MinHeap<T, F> {
        MinHeap {
            heap: Vec::new(),
            cmp: cmp
        }
    }

    pub fn from_vec_by(mut vec: Vec<T>, cmp: F) -> MinHeap<T, F> {
        use self::max_heap_internal::*;

        build(&mut vec, |x, y| cmp(y, x));
        MinHeap {
            heap: vec,
            cmp: cmp
        }
    }

    pub fn push(&mut self, x: T) {
        use self::max_heap_internal::*;

        self.heap.push(x);
        let last = self.heap.len() - 1;
        let cmp = self.cmp.clone();
        sift_up(&mut self.heap, last, |x, y| cmp(y, x));
    }

    pub fn pop(&mut self) -> Option<T> {
        use self::max_heap_internal::*;

        if !self.heap.is_empty() {
            let min = self.heap.swap_remove(0);
            let cmp = self.cmp.clone();
            sift_down(&mut self.heap, 0, |x, y| cmp(y, x));
            Some(min)
        } else {
            None
        }
    }
}

#[snippet = "heap"]
impl<T: Ord> MinHeap<T, fn(&T, &T) -> std::cmp::Ordering> {
    pub fn new() -> MinHeap<T, fn(&T, &T) -> std::cmp::Ordering> {
        MinHeap::new_by(Ord::cmp)
    }

    pub fn from_vec(vec: Vec<T>) -> MinHeap<T, fn(&T, &T) -> std::cmp::Ordering> {
        MinHeap::from_vec_by(vec, Ord::cmp)
    }
}

#[snippet = "heap"]
impl<T, F> MinHeap<T, F> {
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    pub fn peek(&self) -> Option<&T> {
        self.heap.get(0)
    }

    pub fn iter(&self) -> std::slice::Iter<T> {
        self.heap.iter()
    }

    pub fn into_vec(self) -> Vec<T> {
        self.heap
    }
}

#[snippet = "heap"]
impl<T: std::fmt::Debug, F> std::fmt::Debug for MinHeap<T, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[snippet = "heap"]
impl<'a, T, F> IntoIterator for &'a MinHeap<T, F> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> std::slice::Iter<'a, T> {
        self.iter()
    }
}

#[snippet = "heap"]
impl<T, F> IntoIterator for MinHeap<T, F> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> std::vec::IntoIter<T> {
        self.heap.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::{*, max_heap_internal::*};

    #[test]
    fn test_sift_down() {
        let mut vec1 = vec![0];
        sift_down(&mut vec1, 0, |x, y| x.cmp(y));
        assert_eq!(vec1, vec![0]);

        let mut vec2_1 = vec![0, 1];
        sift_down(&mut vec2_1, 0, |x, y| x.cmp(y));
        assert_eq!(vec2_1, vec![1, 0]);

        let mut vec2_2 = vec![1, 0];
        sift_down(&mut vec2_2, 0, |x, y| x.cmp(y));
        assert_eq!(vec2_2, vec![1, 0]);

        let mut vec3_1 = vec![0, 1, 2];
        sift_down(&mut vec3_1, 0, |x, y| x.cmp(y));
        assert_eq!(vec3_1, vec![2, 1, 0]);

        let mut vec3_2 = vec![0, 2, 1];
        sift_down(&mut vec3_2, 0, |x, y| x.cmp(y));
        assert_eq!(vec3_2, vec![2, 0, 1]);

        let mut vec = vec![9, 1, 8, 5, 2, 6, 7, 4, 3];
        sift_down(&mut vec, 1, |x, y| x.cmp(y));
        assert_eq!(vec, vec![9, 5, 8, 4, 2, 6, 7, 1, 3]);
    }

    #[test]
    fn test_build() {
        let mut vec0: Vec<i32> = vec![];
        build(&mut vec0, |x, y| x.cmp(y));
        assert_eq!(vec0, vec![]);

        let mut vec1: Vec<i32> = vec![0];
        build(&mut vec1, |x, y| x.cmp(y));
        assert_eq!(vec1, vec![0]);

        let mut vec2: Vec<i32> = vec![0, 1];
        build(&mut vec2, |x, y| x.cmp(y));
        assert_eq!(vec2, vec![1, 0]);

        let mut vec3: Vec<i32> = vec![0, 1, 2];
        build(&mut vec3, |x, y| x.cmp(y));
        assert_eq!(vec3, vec![2, 1, 0]);

        let mut vec10: Vec<i32> = vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4];
        build(&mut vec10, |x, y| x.cmp(y));
        assert!((1..vec10.len()).all(|i| {
            vec10[parent_of(i)] >= vec10[i]
        }));

        let mut vec11: Vec<i32> = vec![8, 5, 0, 2, 10, 1, 6, 3, 7, 9, 4];
        build(&mut vec11, |x, y| x.cmp(y));
        assert!((1..vec11.len()).all(|i| {
            vec11[parent_of(i)] >= vec11[i]
        }));
    }

    #[test]
    fn test_max_heap_new() {
        let mut heap = MaxHeap::new();
        for x in vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4] {
            heap.push(x);
        }
        for x in (0..10).rev() {
            assert_eq!(heap.peek(), Some(&x));
            assert_eq!(heap.pop(), Some(x));
        }
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_max_heap_from_vec() {
        let mut heap = MaxHeap::from_vec(vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4]);
        for x in (0..10).rev() {
            assert_eq!(heap.peek(), Some(&x));
            assert_eq!(heap.pop(), Some(x));
        }
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_max_heap_new_by() {
        let mut heap = MaxHeap::new_by(|s: &&str, t: &&str| s.len().cmp(&t.len()));

        for x in vec!["bbbb", "aaaaa", "e", "ccc", "dd"] {
            heap.push(x);
        }
        for x in vec!["aaaaa", "bbbb", "ccc", "dd", "e"] {
            assert_eq!(heap.peek(), Some(&x));
            assert_eq!(heap.pop(), Some(x));
        }
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_max_heap_from_vec_by() {
        let mut heap = MaxHeap::from_vec_by(
            vec!["bbbb", "aaaaa", "e", "ccc", "dd"],
            |s: &&str, t: &&str| s.len().cmp(&t.len())
        );

        for x in vec!["aaaaa", "bbbb", "ccc", "dd", "e"] {
            assert_eq!(heap.peek(), Some(&x));
            assert_eq!(heap.pop(), Some(x));
        }
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_min_heap_new() {
        let mut heap = MinHeap::new();
        for x in vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4] {
            heap.push(x);
        }
        for x in 0..10 {
            assert_eq!(heap.peek(), Some(&x));
            assert_eq!(heap.pop(), Some(x));
        }
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_min_heap_from_vec() {
        let mut heap = MinHeap::from_vec(vec![8, 5, 0, 2, 1, 6, 3, 7, 9, 4]);
        for x in 0..10 {
            assert_eq!(heap.peek(), Some(&x));
            assert_eq!(heap.pop(), Some(x));
        }
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_min_heap_new_by() {
        let mut heap = MinHeap::new_by(|s: &&str, t: &&str| s.len().cmp(&t.len()));

        for x in vec!["bbbb", "aaaaa", "e", "ccc", "dd"] {
            heap.push(x);
        }
        for x in vec!["e", "dd", "ccc", "bbbb", "aaaaa"] {
            assert_eq!(heap.peek(), Some(&x));
            assert_eq!(heap.pop(), Some(x));
        }
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_min_heap_from_vec_by() {
        let mut heap = MinHeap::from_vec_by(
            vec!["bbbb", "aaaaa", "e", "ccc", "dd"],
            |s: &&str, t: &&str| s.len().cmp(&t.len())
        );

        for x in vec!["e", "dd", "ccc", "bbbb", "aaaaa"] {
            assert_eq!(heap.peek(), Some(&x));
            assert_eq!(heap.pop(), Some(x));
        }
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }
}
