//! Enriches iterators.

use crate::option::BoolExt;

// BEGIN SNIPPET iter DEPENDS ON option

/// An iterator created by [`chunks`](trait.IteratorExt.html#method.chunks) method on iterators.
pub struct Chunks<I: Iterator> {
    iter: I,
    size: usize
}

impl<I: Iterator> Iterator for Chunks<I> {
    type Item = Vec<I::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        let first = self.iter.next();
        if first.is_none() {
            return None;
        }

        let mut chunk = Vec::with_capacity(self.size);
        chunk.push(first.unwrap());
        for _ in 0..self.size-1 {
            match self.iter.next() {
                Some(x) => chunk.push(x),
                None => break
            }
        }
        Some(chunk)
    }
}

/// An iterator created by [`lscan`](trait.IteratorExt.html#method.lscan) method
/// on iterators.
#[derive(Clone)]
pub struct LScan<I: Iterator, S: Clone, F: FnMut(&S, I::Item) -> S> {
    iter: I,
    state: Option<S>,
    f: F,
}

impl<I: Iterator, S: Clone, F> Iterator for LScan<I, S, F>
where
    F: FnMut(&S, I::Item) -> S,
{
    type Item = S;
    fn next(&mut self) -> Option<S> {
        if self.state.is_none() {
            return None;
        }
        let state_inner = self.state.take().unwrap();
        if let Some(item) = self.iter.next() {
            self.state = Some((self.f)(&state_inner, item));
        }
        Some(state_inner)
    }
}

/// An iterator created by [`group_by`](trait.IteratorExt#method.group_by) method
/// on iterators.
pub struct GroupBy<K: Eq, I: Iterator, F: FnMut(&I::Item) -> K> {
    cur: Option<(I::Item, K)>,
    iter: I,
    key_fn: F
}

impl<K: Eq, I: Iterator, F: FnMut(&I::Item) -> K> Iterator for GroupBy<K, I, F> {
    type Item = (K, Vec<I::Item>);

    fn next(&mut self) -> Option<(K, Vec<I::Item>)> {
        let cur = self.cur.take();
        cur.map(|(item, key)| {
            let mut group = vec![item];
            loop {
                let next = self.iter.next();
                match next {
                    Some(next_item) => {
                        let next_key = (self.key_fn)(&next_item);
                        if key == next_key {
                            group.push(next_item);
                        } else {
                            self.cur = Some((next_item, next_key));
                            break;
                        }
                    }
                    None => {
                        self.cur = None;
                        break;
                    }
                }
            }
            (key, group)
        })
    }
}

/// An iterator created by [`run_length`](trait.IteratorExt#method.run_length) method
/// on iterators.
pub struct RunLength<I: Iterator> {
    cur: Option<I::Item>,
    iter: I
}

impl<I: Iterator> Iterator for RunLength<I> where I::Item: Eq {
    type Item = (I::Item, usize);

    fn next(&mut self) -> Option<(I::Item, usize)> {
        let cur = self.cur.take();
        cur.map(|value| {
            let mut length = 1;
            loop {
                let next = self.iter.next();
                match next {
                    Some(next_value) => {
                        if value == next_value {
                            length += 1;
                        } else {
                            self.cur = Some(next_value);
                            break;
                        }
                    }
                    None => {
                        self.cur = None;
                        break;
                    }
                }
            }
            (value, length)
        })
    }
}

/// Enriches iterators by adding various methods.
pub trait IteratorExt: Iterator {
    /// Returns an iterator yielding chunks.
    ///
    /// # Panic
    ///
    /// Panics if `size` is 0;
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::iter::*;
    /// let seq = vec![1, 2, 3, 4, 5, 6, 7, 8];
    /// let chunks: Vec<Vec<i32>> = seq.into_iter().chunks(3).collect();
    /// assert_eq!(chunks, vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8]]);
    /// ```
    fn chunks(self, size: usize) -> Chunks<Self> where Self: Sized {
        assert!(size > 0);
        Chunks {
            iter: self,
            size: size
        }
    }

    /// Returns an iterator folding the inner iterator
    /// and yielding all intermidiate states.
    ///
    /// This method acts like [Haskell's scanl function](https://hackage.haskell.org/package/base-4.12.0.0/docs/Prelude.html#v:scanl).
    /// The name `lscan` corresponds to `rfold` method of `DoubleEndedIterator`.
    ///
    /// # Example
    ///
    /// Calculates a cumulative sum.
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::iter::*;
    /// let data = vec![1, 2, 3, 4, 5];
    /// // the sum of data[start..end] is calculated by cumsum[end] - cumsum[start].
    /// let cumsum: Vec<i32> = data.into_iter().lscan(0, |&acc, x| acc + x).collect();
    /// assert_eq!(cumsum, vec![0, 1, 3, 6, 10, 15]);
    /// ```
    fn lscan<S: Clone, F>(self, state: S, f: F) -> LScan<Self, S, F>
    where
        Self: Sized,
        F: FnMut(&S, Self::Item) -> S,
    {
        LScan {
            iter: self,
            state: Some(state),
            f: f,
        }
    }

    /// `lscan` using the first item as initial state.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// # Example
    ///
    /// Calculates a cumulative max.
    ///
    /// ```
    /// # use atcoder_snippets::iter::*;
    /// use std::cmp;
    ///
    /// let data = vec![10, 1, 20, 2, 30];
    /// // maxs[i] means the maximum value in data[..=i].
    /// let maxs: Vec<i32> = data.into_iter()
    ///     .lscan1(|&acc, x| cmp::max(acc, x)).unwrap().collect();
    /// assert_eq!(maxs, vec![10, 10, 20, 20, 30]);
    /// ```
    fn lscan1<F>(mut self, f: F) -> Option<LScan<Self, Self::Item, F>>
    where
        Self: Sized,
        Self::Item: Clone,
        F: FnMut(&Self::Item, Self::Item) -> Self::Item
    {
        self.next().map(|first| self.lscan(first, f))
    }

    /// If the iterator has any item and all the items are same, returns `Some` of the first item.
    /// Othewise (having no items or non-unique items), returns `None`.
    fn get_unique(mut self) -> Option<Self::Item> where Self: Sized, Self::Item: Eq {
        let first_opt = self.next();
        first_opt.and_then(|first| {
            if self.all(|item| item == first) { Some(first) } else { None }
        })
    }

    /// `f`によってグループ分けされた`Vec`を生成するイテレータを返す
    ///
    /// SQLのgroup_byではなく、PythonのitertoolやRustのitertoolと同じ意味論である
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::iter::*;
    /// let seq = vec![('a', 0), ('a', 1), ('a', 2), ('b', 0), ('a', 0), ('a', 1)];
    /// let grouped: Vec<(char, Vec<(char, i32)>)> = seq
    ///     .into_iter()
    ///     .group_by(|&(ch, _)| ch)
    ///     .collect();
    /// assert_eq!(grouped,
    ///            vec![('a', vec![('a', 0), ('a', 1), ('a', 2)]),
    ///                 ('b', vec![('b', 0)]),
    ///                 ('a', vec![('a', 0), ('a', 1)])]);
    /// ```
    fn group_by<K: Eq, F: FnMut(&Self::Item) -> K>(mut self, mut f: F) -> GroupBy<K, Self, F> where Self: Sized {
        let next = self.next();
        GroupBy {
            cur: next.map(|item| {
                let key = f(&item);
                (item, key)
            }),
            iter: self,
            key_fn: f
        }
    }

    /// Returns an iterator yielding groups of same values as tuples of `(value, length)`.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::iter::*;
    /// let seq = vec!['a', 'a', 'a', 'b', 'a', 'a'];
    /// let grouped: Vec<(char, usize)> = seq
    ///     .into_iter()
    ///     .run_length()
    ///     .collect();
    /// assert_eq!(grouped, vec![('a', 3), ('b', 1), ('a', 2)]);
    /// ```
    fn run_length(mut self) -> RunLength<Self> where Self: Sized, Self::Item: Eq {
        RunLength {
            cur: self.next(),
            iter: self
        }
    }

    /// Concatenates items into a string with interleaving separators.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::iter::*;
    /// assert_eq!(&vec![1, 2, 3].into_iter().join(", "), "1, 2, 3");
    /// ```
    fn join<T: std::fmt::Display>(mut self, sep: T) -> String
    where
        Self: Sized, Self::Item: std::fmt::Display
    {
        let mut result = String::new();
        if let Some(first) = self.next() {
            result.push_str(&format!("{}", first));
        }
        for s in self {
            result.push_str(&format!("{}{}", sep, s));
        }
        result
    }

    /// Concatenates items into a string.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::iter::*;
    /// assert_eq!(&vec![1, 2, 3].into_iter().cat(), "123");
    /// ```
    fn cat(self) -> String where Self: Sized, Self::Item: std::fmt::Display { self.join("") }
}

impl<I: Iterator> IteratorExt for I {}

/// Enriches exact-sized iterators by adding `inner_product` method.
pub trait IteratorInnerProduct<T, Rhs=T>: ExactSizeIterator<Item=T> {
    /// Calculate inner product of two iterators.
    ///
    /// If the iterators have different lengths, returns `None`
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::iter::*;
    /// let v1: Vec<i32> = vec![1, 2, 3];
    /// let v2: Vec<i32> = vec![10, 20, 30];
    /// assert_eq!(v1.iter().inner_product(&v2), Some(10 + 40 + 90));
    ///
    /// // You can calculate inner_product of `i32` and `&i32` because `i32: Mul<&i32>` holds.
    /// // The output type is `i32`, which is `<i32 as Mul<&i32>>::Output`.
    /// assert_eq!(v1.iter().inner_product(v2), Some(10 + 40 + 90));
    ///
    /// // You can use any types impl-ing `Mul`.
    /// use std::time::Duration;
    /// let factors: Vec<u32> = vec![1, 2, 3];
    /// let durations: Vec<Duration> = vec![
    ///     Duration::from_secs(10),
    ///     Duration::from_secs(20),
    ///     Duration::from_secs(30)
    /// ];
    /// assert_eq!(factors.into_iter().inner_product(durations),
    ///            Some(Duration::from_secs(10 + 40 + 90)));
    /// ```
    fn inner_product<I, J>(self, other: I) -> Option<<T as std::ops::Mul<Rhs>>::Output>
    where
        Self: Sized,
        I: IntoIterator<Item=Rhs, IntoIter=J>,
        J: Iterator<Item=Rhs> + ExactSizeIterator,
        T: std::ops::Mul<Rhs>,
        <T as std::ops::Mul<Rhs>>::Output: std::iter::Sum
    {
        let iter = other.into_iter();
        (self.len() == iter.len()).then_with(|| {
            self.zip(iter).map(|(a, b)| a * b).sum()
        })
    }
}

impl<T1, T2, I> IteratorInnerProduct<T1, T2> for I
where
    I: Iterator<Item=T1> + ExactSizeIterator,
    T1: std::ops::Mul<T2>
{}

/// An iterator created by [`unfold`](fn.unfold.html) function.
pub struct Unfold<T, F> where F: FnMut(&T) -> Option<T> {
    state: Option<T>,
    f: F
}

impl<T, F> Iterator for Unfold<T, F> where F: FnMut(&T) -> Option<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.state.is_none() {
            return None;
        }

        let state_inner = self.state.take().unwrap();
        self.state = (self.f)(&state_inner);
        Some(state_inner)
    }
}

/// Returns an iterator applying `f` to `init` repeatedly.
///
/// The iterator yields inner values of `Options` until `f` returns `None`.
///
/// In Rust >= 1.34.0, the same functionality is provided as `iter::succesors`.
///
/// # Example
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::iter::*;
/// fn twice_until_10(x: &i32) -> Option<i32> {
///    let y = *x * 2;
///    if y < 10 { Some(y) } else { None }
/// }
///
/// assert_eq!(unfold(1, twice_until_10).collect::<Vec<_>>(), vec![1, 2, 4, 8]);
/// ```
pub fn unfold<T, F>(init: T, f: F) -> Unfold<T, F> where F: FnMut(&T) -> Option<T> {
    Unfold { state: Some(init), f: f }
}

/// An iterator created by [`iterate`](fn.iterate.html) function.
pub struct Iterate<T, F> where F: FnMut(&T) -> T {
    state: T,
    f: F
}

impl<T, F> Iterator for Iterate<T, F> where F: FnMut(&T) -> T {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        use std::mem::swap;
        // reborrow
        let mut state = (self.f)(&self.state);
        swap(&mut state, &mut self.state);
        Some(state)
    }
}

/// Returns an iterator yielding `init`, `f(init)`, `f(f(init))`, ... infinitely.
///
/// # Example
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::iter::*;
/// assert_eq!(
///     iterate(1, |x| x * 2).take_while(|&y| y < 10).collect::<Vec<_>>(),
///     vec![1, 2, 4, 8]
/// );
/// ```
pub fn iterate<T, F>(init: T, f: F) -> Iterate<T, F>
where
    F: FnMut(&T) -> T,
{
    Iterate { state: init, f: f }
}

// END SNIPPET

/*
#[snippet = "product"]
#[derive(Clone)]
struct Product2<I, J>
where
    I: Iterator,
    I::Item: Clone,
    J: Iterator + Clone
{
    iters: (I, J),
    orig_iter: J,
    cur: Option<I::Item>,
}

#[snippet = "product"]
impl<I, J> Product2<I, J>
where
    I: Iterator,
    I::Item: Clone,
    J: Iterator + Clone
{
    pub fn new(iter1: I, iter2: J) -> Product2<I, J> {
        Product2 {
            iters: (iter1, iter2.clone()),
            orig_iter: iter2,
            cur: None
        }
    }
}

#[snippet = "product"]
impl<I, J> Iterator for Product2<I, J>
where
    I: Iterator,
    I::Item: Clone,
    J: Iterator + Clone
{
    type Item = (I::Item, J::Item);

    fn next(&mut self) -> Option<(I::Item, J::Item)> {
        match self.cur.clone() {
            None => {
                match self.iters.0.next() {
                    None => None,
                    Some(a) => {
                        match self.iters.1.next() {
                            None => None,
                            Some(b) => {
                                let a_cloned = a.clone();
                                self.cur = Some(a);
                                Some((a_cloned, b))
                            }
                        }
                    }
                }
            },
            Some(a) => {
                match self.iters.1.next() {
                    Some(b) => Some((a.clone(), b)),
                    None => {
                        match self.iters.0.next() {
                            None => None,
                            Some(a) => {
                                self.iters.1 = self.orig_iter.clone();
                                match self.iters.1.next() {
                                    None => None,
                                    Some(b) => {
                                        let a_cloned = a.clone();
                                        self.cur = Some(a);
                                        Some((a_cloned, b))
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[snippet = "product"]
#[derive(Clone)]
struct Product3<I, J, K>
where
    I: Iterator,
    I::Item: Clone,
    J: Iterator + Clone,
    J::Item: Clone,
    K: Iterator + Clone
{
    inner: Product2<Product2<I, J>, K>
}

#[snippet = "product"]
impl<I, J, K> Product3<I, J, K>
where
    I: Iterator,
    I::Item: Clone,
    J: Iterator + Clone,
    J::Item: Clone,
    K: Iterator + Clone
{
    pub fn new(iter1: I, iter2: J, iter3: K) -> Product3<I, J, K> {
        Product3 { inner: Product2::new(Product2::new(iter1, iter2), iter3) }
    }
}

#[snippet = "product"]
impl<I, J, K> Iterator for Product3<I, J, K>
where
    I: Iterator,
    I::Item: Clone,
    J: Iterator + Clone,
    J::Item: Clone,
    K: Iterator + Clone
{
    type Item = (I::Item, J::Item, K::Item);

    fn next(&mut self) -> Option<(I::Item, J::Item, K::Item)> {
        self.inner.next().map(|((a, b), c)| (a, b, c))
    }
}

#[snippet = "product"]
macro_rules! product {
    ($i:expr, $j:expr) => ( Product2::new($i, $j) );
    ($i:expr, $j:expr, $k:expr) => ( Product3::new($i, $j, $k) );
}

#[snippet = "combinations"]
struct Combinations<I: Iterator + Clone>
where
    I::Item: Clone
{
    with_replacement: bool,
    iters: Vec<I>,
    next_item: Option<Vec<I::Item>>
}

#[snippet = "combinations"]
impl<I: Iterator + Clone> Combinations<I>
where
    I::Item: Clone
{
    pub fn new(mut iter: I, size: usize, with_replacement: bool) -> Combinations<I> {
        let mut result = Combinations {
            with_replacement: with_replacement,
            iters: Vec::new(),
            next_item: None,
        };

        let mut next_item = Vec::new();

        if with_replacement {
            if let Some(x) = iter.next() {
                for _ in 0..size {
                    result.iters.push(iter.clone());
                    next_item.push(x.clone());
                }
            }

            result.next_item = Some(next_item);
        } else {
            for _ in 0..size {
                match iter.next() {
                    Some(x) => {
                        result.iters.push(iter.clone());
                        next_item.push(x);
                    },
                    None => {
                        result.iters.clear();
                        break;
                    }
                }
            }

            if result.iters.len() == size {
                result.next_item = Some(next_item);
            }
        }

        result
    }

    fn size(&self) -> usize {
        self.iters.len()
    }

    fn do_next_with_replacement(
        iters: &mut[I],
        next_item: &mut[I::Item]
    ) -> bool {
        match iters.split_last_mut() {
            None => false,
            Some((iter, mut iters_rest)) => {
                match iter.next() {
                    Some(x) => {
                        *next_item.last_mut().unwrap() = x;
                    },
                    None => {
                        let (mut item_last, mut item_rest) =
                            next_item.split_last_mut().unwrap();
                        if !Self::do_next_with_replacement(
                            &mut iters_rest, &mut item_rest)
                        {
                            return false;
                        }
                        let new_iter = iters_rest.last().unwrap().clone();
                        *iter = new_iter;
                        *item_last = item_rest.last().unwrap().clone();
                    }
                }

                true
            }
        }
    }

    fn do_next_without_replacement(
        iters: &mut[I],
        next_item: &mut[I::Item],
        left_index: usize,
    ) -> bool {
        let end = iters.len();
        let mut success = true;
        for i in left_index..end {
            match iters[i].next() {
                None => {
                    success = false;
                    break;
                },
                Some(x) => {
                    next_item[i] = x;
                    if i+1 < end {
                        iters[i+1] = iters[i].clone();
                    }
                }
            }
        }

        if success {
            true
        } else if left_index == 0 {
            false
        } else {
            Self::do_next_without_replacement(iters, next_item, left_index - 1)
        }
    }
}

// Iteration is too slow
#[snippet = "combinations"]
impl<I: Iterator + Clone> Iterator for Combinations<I>
where
    I::Item: Clone
{
    type Item = Vec<I::Item>;

    fn next(&mut self) -> Option<Vec<I::Item>> {
        use std::mem::swap;

        let mut continuing = true;
        let mut next_item = self.next_item.clone().map(|mut item| {
            continuing = if self.with_replacement {
                Self::do_next_with_replacement(&mut self.iters, &mut item)
            } else {
                let end = self.size();
                Self::do_next_without_replacement(&mut self.iters, &mut item, end - 1)
            };
            item
        });
        swap(&mut next_item, &mut self.next_item);
        if !continuing {
            self.next_item = None;
        }
        next_item
    }
}

#[snippet = "combinations"]
macro_rules! combinations {
    ($iter:expr, 2) => {
        Combinations::new($iter, 2, false).map(|v| (v[0], v[1]))
    };
    ($iter:expr, 3) => {
        Combinations::new($iter, 3, false).map(|v| (v[0], v[1], v[2]))
    };
    ($iter:expr, 4) => {
        Combinations::new($iter, 4, false).map(|v| (v[0], v[1], v[2], v[3]))
    };
}

#[snippet = "combinations"]
#[allow(unused_macros)]
macro_rules! combinations_repl {
    ($iter:expr, 2) => {
        Combinations::new($iter, 2, true).map(|v| (v[0], v[1]))
    };
    ($iter:expr, 3) => {
        Combinations::new($iter, 3, true).map(|v| (v[0], v[1], v[2]))
    };
    ($iter:expr, 4) => {
        Combinations::new($iter, 4, true).map(|v| (v[0], v[1], v[2], v[3]))
    };
}
*/

#[cfg(test)]
mod test {
    use super::*;
    use std::iter;

    #[test]
    fn test_get_unique() {
        assert_eq!(iter::empty::<i32>().get_unique(), None);
        assert_eq!(iter::once(42).get_unique(), Some(42));
        assert_eq!([42, 42].iter().get_unique(), Some(&42));
        assert_eq!([42, 43].iter().get_unique(), None);
        assert_eq!(iter::repeat(42).take(10).get_unique(), Some(42));
    }

    #[test]
    fn test_group_by() {
        let groups1 = iter::empty::<i32>().group_by(|&x| x % 2)
            .collect::<Vec<_>>();
        let expected: Vec<(i32, Vec<i32>)> = Vec::new();
        assert_eq!(groups1, expected);

        let groups2 = iter::once(1).group_by(|&x| x % 2)
            .collect::<Vec<_>>();
        assert_eq!(groups2, vec![(1, vec![1])]);

        let groups3 = vec![1, 3].into_iter().group_by(|&x| x % 2)
            .collect::<Vec<_>>();
        assert_eq!(groups3, vec![(1, vec![1, 3])]);

        let groups4 = vec![1, 2].into_iter().group_by(|&x| x % 2)
            .collect::<Vec<_>>();
        assert_eq!(groups4, vec![(1, vec![1]), (0, vec![2])]);

        let seq = vec![(0, 'a'), (1, 'a'), (2, 'b'), (3, 'a'), (4, 'c'), (5, 'c')];
        let groups5 = seq.into_iter().group_by(|x| x.1)
            .collect::<Vec<_>>();
        assert_eq!(groups5, vec![
            ('a', vec![(0, 'a'), (1, 'a')]),
            ('b', vec![(2, 'b')]),
            ('a', vec![(3, 'a')]),
            ('c', vec![(4, 'c'), (5, 'c')])
        ]);
    }

    #[test]
    fn test_inner_product_length() {
        let empty: Vec<i32> = vec![];
        assert_eq!(empty.iter().inner_product(&empty), Some(0));

        let seq1 = vec![10];
        assert_eq!(empty.iter().inner_product(&seq1), None);
        assert_eq!(seq1.iter().inner_product(&empty), None);
        assert_eq!(seq1.iter().inner_product(&seq1), Some(100));
    }

    #[test]
    fn test_inner_product_type() {
        use std::time::Duration;

        let i32_seq = vec![10, 20, 30];
        assert_eq!(i32_seq.iter().cloned().inner_product(i32_seq.clone()),
                   Some(100 + 400 + 900));
        assert_eq!(i32_seq.iter().inner_product(i32_seq.clone()),
                   Some(100 + 400 + 900));
        assert_eq!(i32_seq.iter().inner_product(&i32_seq),
                   Some(100 + 400 + 900));

        let dur_seq = vec![
            Duration::from_secs(10),
            Duration::from_secs(20),
            Duration::from_secs(30)
        ];
        assert_eq!(dur_seq.iter().cloned().inner_product(i32_seq.clone()),
                   Some(Duration::from_secs(100 + 400 + 900)));
        assert_eq!(i32_seq.iter().cloned().inner_product(dur_seq.clone()),
                   Some(Duration::from_secs(100 + 400 + 900)));
    }

    #[test]
    fn test_join() {
        assert_eq!(iter::empty::<i32>().join(" "), "");
        assert_eq!(iter::once(1).join(" "), "1");
        assert_eq!([1,2,3].iter().join(" "), "1 2 3");
        assert_eq!([1,2,3].iter().join(0), "10203");
    }
}

/*
#[cfg(bench)]
mod bench {
    extern crate test;
    use super::*;
    use self::test::Bencher;

    #[bench]
    fn bench_product_2(b: &mut Bencher) {
        b.iter(|| {
            let mut v: Vec<u32> = Vec::new();
            for (i, j) in product!(0..100, 0..100) {
                v.sort();
            }
            println!("{:?}", v);
        });
    }

    #[bench]
    fn bench_product_2_nested_loop(b: &mut Bencher) {
        b.iter(|| {
            let mut v: Vec<u32> = Vec::new();
            for i in 0..100 {
                for j in 0..100 {
                    v.sort();
                }
            }
            println!("{:?}", v);
        });
    }

    #[bench]
    fn bench_product_3(b: &mut Bencher) {
        b.iter(|| {
            let mut v: Vec<u32> = Vec::new();
            for (i, j, k) in product!(0..100, 0..100, 0..100) {
                v.sort();
            }
            println!("{:?}", v);
        });
    }

    #[bench]
    fn bench_product_3_nested_loop(b: &mut Bencher) {
        b.iter(|| {
            let mut v: Vec<u32> = Vec::new();
            for i in 0..100 {
                for j in 0..100 {
                    for k in 0..100 {
                        v.sort();
                    }
                }
            }
            println!("{:?}", v);
        });
    }
}
*/
