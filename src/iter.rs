//! Enriches iterators.

/// An iterator created by [`step_by_`](trait.IteratorExt.html#method.step_by_) method on iterators.
#[snippet = "iter"]
#[derive(Clone)]
pub struct StepBy<I> {
    iter: I,
    step: usize,
    first_take: bool
}

#[snippet = "iter"]
impl<I: Iterator> Iterator for StepBy<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.first_take {
            self.first_take = false;
            self.iter.next()
        } else {
            self.iter.nth(self.step)
        }
    }
}

/// An iterator created by [`lscan`](trait.IteratorExt.html#method.lscan) method
/// on iterators.
#[snippet = "iter"]
#[derive(Clone)]
pub struct LScan<I: Iterator, S: Clone, F: FnMut(&S, I::Item) -> S> {
    iter: I,
    state: Option<S>,
    f: F,
}

#[snippet = "iter"]
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

/// An iterator created by [`flatten`](trait.IteratorExt.html#method.flatten) method
/// on iterators.
#[snippet = "iter"]
// #[derive(Clone)]
pub struct Flatten<I: Iterator>
where
    I::Item: IntoIterator
{
    outer_iter: I,
    inner_iter: Option<<<I as Iterator>::Item as IntoIterator>::IntoIter>
}

#[snippet = "iter"]
impl<I, J> Iterator for Flatten<I>
where
    I: Iterator<Item = J>,
    J: IntoIterator
{
    type Item = <<J as IntoIterator>::IntoIter as Iterator>::Item;

    fn next(&mut self) -> Option<J::Item> {
        loop {
            if let Some(inner_iter) = self.inner_iter.as_mut() {
                if let item@Some(_) = inner_iter.next() {
                    return item
                }
            }

            match self.outer_iter.next() {
                None => return None,
                Some(inner) => self.inner_iter = Some(inner.into_iter())
            }
        }
    }
}

/*
impl<I, J> DoubleEndedIterator for Flatten<I>
where
    I: DoubleEndedIterator,
    J: DoubleEndedIterator,
    I::Item: J {}
*/

/// An iterator created by [`group_by`](trait.IteratorExt#method.group_by) method
/// on iterators.
#[snippet = "iter"]
pub struct GroupBy<K: Eq, I: Iterator, F: FnMut(&I::Item) -> K> {
    cur: Option<(I::Item, K)>,
    iter: I,
    key_fn: F
}

#[snippet = "iter"]
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

/// Enriches iterators by adding various methods.
#[snippet = "iter"]
pub trait IteratorExt: Iterator {
    /// Returns an iterator skipping a constant number of items in each iteration.
    ///
    /// This method is introduced in Rust 1.28.0 for `Iterator`.
    /// The trailing underbar is for avoiding the name collision.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::iter::*;
    /// let mut iter = (0..10).step_by(4);
    /// assert_eq!(iter.next(), Some(0));
    /// assert_eq!(iter.next(), Some(4));
    /// assert_eq!(iter.next(), Some(8));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn step_by_(self, step: usize) -> StepBy<Self> where Self: Sized {
        assert_ne!(step, 0);
        StepBy {
            iter: self,
            step: step - 1,
            first_take: true
        }
    }

    /// Applying an function (usually producing a side effect) for each items.
    ///
    /// This method is introduced in Rust 1.21.0 for `Iterator`.
    ///
    /// # Example
    ///
    /// ```ignore
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::iter::*;
    /// let mut sum = 0;
    /// (0..10).for_each(|x| sum += x);
    /// assert_eq!(sum, 45);
    /// ```
    fn for_each<F: FnMut(Self::Item)>(self, mut f: F) where Self: Sized {
        for item in self {
            f(item);
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

    // If the iterator has any item and all the items are same, returns `Some` of the first item.
    // Othewise (having no items or non-unique items), returns `None`.
    //
    // Self should implement FusedIterator introduced in rust 1.26.0.
    fn get_unique(mut self) -> Option<Self::Item> where Self: Sized, Self::Item: Eq {
        let first_opt = self.next();
        first_opt.and_then(|first| {
            if self.all(|item| item == first) { Some(first) } else { None }
        })
    }

    // TODO, If possible, avoid name collision to Iterator::flatten introduced in Rust 1.29.0
    /// Returns an iterator concatenating its inner `IntoIterator`s.
    ///
    /// # Example
    ///
    /// ```ignore
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::iter::*;
    /// let seq = vec![Some(1), Some(2), None, Some(3), None, None];
    /// assert_eq!(seq.into_iter().flatten().collect(), vec![1, 2, 3]);
    /// ```
    fn flatten(mut self) -> Flatten<Self> where Self: Sized, Self::Item: IntoIterator {
        let inner_opt = self.next();
        Flatten {
            outer_iter: self,
            inner_iter: inner_opt.map(|inner| inner.into_iter())
        }
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

    /// Concatenates items into a string with interleaving separators.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::iter::*;
    /// assert_eq!(&vec![1, 2, 3].into_iter().join(", "), "1, 2, 3");
    /// ```
    fn join(mut self, sep: &str) -> String where Self: Sized, Self::Item: std::fmt::Display {
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

#[snippet = "iter"]
impl<I: Iterator> IteratorExt for I {}

/// An iterator created by [`unfold`](fn.unfold.html) function.
#[snippet = "iter"]
pub struct Unfold<T, F> where F: FnMut(&T) -> Option<T> {
    state: Option<T>,
    f: F
}

#[snippet = "iter"]
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
#[snippet = "iter"]
pub fn unfold<T, F>(init: T, f: F) -> Unfold<T, F> where F: FnMut(&T) -> Option<T> {
    Unfold { state: Some(init), f: f }
}

/// An iterator created by [`iterate`](fn.iterate.html) function.
#[snippet = "iter"]
pub struct Iterate<T, F> where F: FnMut(&T) -> T {
    state: T,
    f: F
}

#[snippet = "iter"]
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
#[snippet = "iter"]
pub fn iterate<T, F>(init: T, f: F) -> Iterate<T, F>
where
    F: FnMut(&T) -> T,
{
    Iterate { state: init, f: f }
}


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

#[cfg(test)]
mod test {
    use super::*;
    use std::iter;

    #[test]
    fn test_step_by() {
        let ns: Vec<_> = (1..10).step_by_(3).collect();
        assert_eq!(ns, vec![1, 4, 7]);
    }

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

    /*
    // Rename IteratorExt::flatten to flatten_ for testing
    #[test]
    fn test_flatten() {
        assert_eq!(iter::empty::<Vec<i32>>().flatten_().collect::<Vec<i32>>(), vec![]);
        assert_eq!(iter::once(vec![1]).flatten_().collect::<Vec<i32>>(), vec![1]);
        assert_eq!(iter::once(vec![1, 2, 3]).flatten_().collect::<Vec<i32>>(), vec![1, 2, 3]);
        let v = vec![vec![], vec![1], vec![], vec![2, 3, 4], vec![5, 6], vec![]];
        assert_eq!(v.into_iter().flatten_().collect::<Vec<i32>>(), vec![1, 2, 3, 4, 5, 6]);
    }
    */

    #[test]
    fn test_join() {
        assert_eq!(iter::empty::<i32>().join(" "), "");
        assert_eq!(iter::once(1).join(" "), "1");
        assert_eq!([1,2,3].iter().join(" "), "1 2 3");
    }
}

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
