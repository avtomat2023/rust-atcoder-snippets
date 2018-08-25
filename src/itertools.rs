/// StepBy: Copyright 2013-2016 The Rust Project Developers.
#[snippet = "richiter"]
#[derive(Clone)]
pub struct StepBy<I> {
    iter: I,
    step: usize,
    first_take: bool
}

#[snippet = "richiter"]
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

#[snippet = "richiter"]
trait RichIterator: Iterator {
    fn step_by_(self, step: usize) -> StepBy<Self> where Self: Sized {
        assert_ne!(step, 0);
        StepBy {
            iter: self,
            step: step - 1,
            first_take: true
        }
    }

    fn for_each<F: FnMut(Self::Item)>(self, mut f: F) where Self: Sized {
        for item in self {
            f(item);
        }
    }
}

#[snippet = "richiter"]
impl<I: Iterator> RichIterator for I {}

#[snippet(product)]
#[derive(Clone)]
pub struct Product2<I, J>
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
pub struct Product3<I, J, K>
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
#[allow(unused_macros)]
macro_rules! product {
    ($i:expr, $j:expr) => ( Product2::new($i, $j) );
    ($i:expr, $j:expr, $k:expr) => ( Product3::new($i, $j, $k) );
}

#[snippet = "combinations"]
pub struct Combinations<I: Iterator + Clone>
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
#[allow(unused_macros)]
macro_rules! combinations {
    ($iter:expr, 2) => {
        Combinations::new($iter, 2, false).map(|v| (v[0], v[1]))
    };
    ($iter:expr, 3) => {
        Combinations::new($iter, 3, false).map(|v| (v[0], v[1], v[2]))
    };
    ($iter:expr, 4) => {
        Combinations::new($iter, 4, false).map(|v| (v[0], v[1], v[2], v[4]))
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
        Combinations::new($iter, 4, true).map(|v| (v[0], v[1], v[2], v[4]))
    };
}

#[snippet = "join"]
trait JoinIntoString {
    fn push_to_string(self, s: &mut String);
}

#[snippet = "join"]
impl JoinIntoString for char {
    fn push_to_string(self, s: &mut String) {
        s.push(self);
    }
}

#[snippet = "join"]
impl<'a> JoinIntoString for &'a str {
    fn push_to_string(self, s: &mut String) {
        s.push_str(self);
    }
}

#[snippet = "join"]
impl JoinIntoString for String {
    fn push_to_string(self, s: &mut String) {
        s.push_str(&self);
    }
}

#[snippet = "join"]
trait StringJoinIterator {
    fn join(self, sep: &str) -> String;
}

#[snippet = "join"]
impl<T: JoinIntoString, I: Iterator<Item=T>> StringJoinIterator for I {
    fn join(mut self, sep: &str) -> String {
        let mut result = String::new();
        if let Some(first) = self.next() {
            first.push_to_string(&mut result);
            for item in self {
                result.push_str(sep);
                item.push_to_string(&mut result);
            }
        }
        result
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_step_by() {
        let ns: Vec<_> = (1..10).step_by_(3).collect();
        assert_eq!(ns, vec![1, 4, 7]);
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
