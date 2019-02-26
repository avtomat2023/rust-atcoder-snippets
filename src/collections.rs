/// Data structures.

#[snippet = "collections"]
use std::rc::Rc;
#[snippet = "collections"]
use std::ops::Deref;
#[snippet = "collections"]
use std::fmt;
#[snippet = "collections"]
use std::cmp::Ordering;
#[snippet = "collections"]
use std::borrow::Borrow;
// use std::iter::FromIterator;

/// For pattern match.
#[snippet = "collections"]
#[derive(Clone, PartialEq, Eq)]
pub enum ListInner<T: Clone> {
    Nil,
    Cons(T, List<T>)
}

#[snippet = "collections"]
pub use self::ListInner::{Nil, Cons};

// The example is ignored because `flatten` method by `iter` snippet collide
// `flatten` of `std::iter::Iterator` in Rust >= 1.29.0

/// Immutable and persistent list heavily used in functional languages.
///
/// https://docs.rs/immutable/0.1.1/immutable/list/enum.List.html
///
/// 要素型にCloneを要求しているのは、コンスセルがRcを用いて参照されており、
/// headへの参照がうまく取り出せないためである。
/// To create a list of values not `Clone` or costly to `Clone`,
/// create `List<Rc<T>>` instead of `List<T>`.
///
/// # Example
///
/// Solves [ABC118 D: Match Matching](https://atcoder.jp/contests/abc118/tasks/abc118_d) by memoized depth-first search.
///
/// ```ignore
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::{read::*, itertools::*, collections::*};
/// use std::cmp::Ordering;
/// use std::collections::HashMap;
///
/// /// `MATCHSTICKS_FOR[digit]` means how many matchsticks are needed
/// /// to form `digit`.
/// const MATCHSTICKS_FOR: [u32; 10] = [0, 2, 5, 5, 4, 5, 6, 3, 7, 6];
///
/// fn cmp_numbers(n1: &List<usize>, n2: &List<usize>) -> Ordering {
///     if n1.len() > n2.len() {
///         Ordering::Greater
///     } else if n1.len() < n2.len() {
///         Ordering::Less
///     } else {
///         n1.cmp(n2)
///     }
/// }
///
/// /// Returns maximum number composed by `n` matchsticks.
/// ///
/// /// The number is represented as a big-endian list of usize.
/// /// Each usize value represents a decimal digit.
/// ///
/// /// If it is impossible to create any number by `n` matchsticks, returns `None`.
/// fn dfs(n: u32, digits: &[usize], memo: &mut HashMap<u32, Option<List<usize>>>)
///        -> Option<List<usize>>
/// {
///     if n == 0 {
///         Some(List::nil())
///     } else {
///         let ans = memo.get(&n).cloned();
///         // If the answer for `n` is already memoized, returns it.
///         ans.unwrap_or_else(|| {
///             let new_ans = digits.iter().map(|&digit| {
///                 n.checked_sub(MATCHSTICKS_FOR[digit]).and_then(|next_n| {
///                     dfs(next_n, digits, memo).map(|tail| digit.cons(tail))
///                 })
///             }).flatten() // Uses `iter` snippet.
///               .max_by(cmp_numbers);
///             // Memowise the answer for `n`.
///             memo.insert(n, new_ans.clone());
///             new_ans
///         })
///     }
/// }
///
/// fn main() {
///     // Uses `read` snippet.
///     read!(n = u32, _ = ());
///     read!(digits = Vec<usize>);
///     // Uses `iter` snippet for `cat`.
///     println!("{}", dfs(n, &digits, &mut HashMap::new()).unwrap().cat());
/// }
/// ```
#[snippet = "collections"]
#[derive(Clone, PartialEq, Eq)]
pub struct List<T: Clone> {
    inner: Rc<ListInner<T>>,
    len: usize
}

#[snippet = "collections"]
impl<T: Clone> List<T> {
    pub fn nil() -> List<T> { List { inner: Rc::new(Nil), len: 0 } }

    pub fn is_empty(&self) -> bool {
        match **self {
            Nil => true,
            Cons(_, _) => false
        }
    }

    /// Length of the list.
    ///
    /// `len()` is O(1) time because each sublist holds its length.
    pub fn len(&self) -> usize { self.len }

    pub fn iter(&self) -> List<T> {
        self.clone()
    }

    #[cfg(test)]
    fn take(self) -> Rc<ListInner<T>> {
        self.inner
    }
}

#[snippet = "collections"]
impl<T: Clone> AsRef<ListInner<T>> for List<T> {
    fn as_ref(&self) -> &ListInner<T> {
        self.inner.as_ref()
    }
}

#[snippet = "collections"]
impl<T: Clone> Deref for List<T> {
    type Target = ListInner<T>;

    fn deref(&self) -> &ListInner<T> {
        self.inner.deref()
    }
}

#[snippet = "collections"]
impl<T: Clone + fmt::Debug> fmt::Debug for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner.as_ref() {
            &Nil => write!(f, "[]"),
            &Cons(ref head, ref tail) => write!(f, "{:?}:{:?}", head, tail)
        }
    }
}

#[snippet = "collections"]
impl<T: Clone + PartialOrd> PartialOrd for List<T> {
    fn partial_cmp(&self, other: &List<T>) -> Option<Ordering> {
        match (self.as_ref(), other.as_ref()) {
            (&Nil, &Nil) => Some(Ordering::Equal),
            (&Nil, &Cons(_, _)) => Some(Ordering::Less),
            (&Cons(_, _), &Nil) => Some(Ordering::Greater),
            (&Cons(ref head1, ref tail1), &Cons(ref head2, ref tail2)) => {
                head1.partial_cmp(&head2).and_then(|ordering| {
                    match ordering {
                        Ordering::Equal => tail1.partial_cmp(tail2),
                        _ => Some(ordering)
                    }
                })
            }
        }
    }
}

// Needed in ABC118 D
#[snippet = "collections"]
impl<T: Clone + Ord> Ord for List<T> {
    fn cmp(&self, other: &List<T>) -> Ordering {
        match (self.as_ref(), other.as_ref()) {
            (&Nil, &Nil) => Ordering::Equal,
            (&Nil, &Cons(_, _)) => Ordering::Less,
            (&Cons(_, _), &Nil) => Ordering::Greater,
            (&Cons(ref head1, ref tail1), &Cons(ref head2, ref tail2)) => {
                match head1.cmp(&head2) {
                    Ordering::Equal => tail1.cmp(tail2),
                    determined => determined
                }
            }
        }
    }
}

#[snippet = "collections"]
impl<T: Clone> Iterator for List<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let cons;
        match **self {
            Nil => return None,
            Cons(ref head, ref tail) => cons = (head.clone(), tail.clone())
        }
        *self = cons.1;
        Some(cons.0)
    }
}


#[snippet = "collections"]
impl<'a, T: Clone> IntoIterator for &'a List<T> {
    type Item = T;
    type IntoIter = List<T>;

    fn into_iter(self) -> List<T> {
        self.iter()
    }
}

#[snippet = "collections"]
pub trait IntoCons<T: Clone, L: Borrow<List<T>>> {
    fn cons(self, tail: L) -> List<T>;
}

#[snippet = "collections"]
impl<T: Clone, L: Borrow<List<T>>> IntoCons<T, L> for T {
    fn cons(self, tail: L) -> List<T> {
        let tail_cloned: List<T> = tail.borrow().clone().into();
        let tail_len = tail_cloned.len;
        List {
            inner: Rc::new(Cons(self, tail_cloned)),
            len: tail_len + 1
        }
    }
}

// TODO: Take a bench comparing with IntoCons
pub trait IntoConsByMove<T: Clone> {
    fn cons_move(self, tail: List<T>) -> List<T>;
}

impl<T: Clone> IntoConsByMove<T> for T {
    fn cons_move(self, tail: List<T>) -> List<T> {
        let tail_len = tail.len;
        List {
            inner: Rc::new(Cons(self, tail)),
            len: tail_len + 1
        }
    }
}

/*
impl<T: Clone> FromIterator for List<T> {

}
*/

#[snippet = "collections"]
#[macro_export]
macro_rules! list {
    [] => { List::nil() };
    [$head:expr] => { $head.cons(List::nil()) };
    [$head:expr, $($tail:expr),*] => { $head.cons(list![$($tail),*]) };
    [$head:expr, $($tail:expr),+ ,] => { list![$head, $($tail),*] };
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering::*;
    use std::f64;

    #[test]
    fn test_list_macro() {
        assert_eq!(list![], List::<i32>::nil());
        assert_eq!(list![1], 1.cons(List::nil()));
        assert_eq!(list![1, 2], 1.cons(2.cons(List::nil())));
        assert_eq!(list![1, 2, 3], 1.cons(2.cons(3.cons(List::nil()))));
        assert_eq!(list![1, 2, 3,], 1.cons(2.cons(3.cons(List::nil()))));
    }

    #[test]
    fn test_cons() {
        let list = list![2, 3];
        assert_eq!(1.cons(list.clone()), list![1, 2, 3]);
        assert_eq!(1.cons(list), list![1, 2, 3]);
    }

    #[test]
    fn test_cons_reference_count() {
        let list_a_nil = List::nil();
        let list_a_3 = 3.cons(list_a_nil.clone());
        let list_a_2 = 2.cons(list_a_3.clone());
        let list_a_1 = 1.cons(list_a_2.clone());

        let list_b_2 = 2.cons(list_a_3.clone());
        let _list_b_1 = 1.cons(list_b_2);

        /*
         *   a: 1 - 2
         *           \
         *            3 - nil
         *           /
         *   b: 1 - 2
         */
        assert_eq!(Rc::strong_count(&list_a_1.take()), 1);
        /*
         *       a: 2
         *           \
         *            3 - nil
         *           /
         *   b: 1 - 2
         */
        assert_eq!(Rc::strong_count(&list_a_2.take()), 1);
        /*
         *         a: 3 - nil
         *           /
         *   b: 1 - 2
         */
        assert_eq!(Rc::strong_count(&list_a_3.take()), 2);
        /*
         *             a: nil
         *               /
         *   b: 1 - 2 - 3
         */
        assert_eq!(Rc::strong_count(&list_a_nil.take()), 2);
    }

    #[test]
    fn test_len() {
        assert_eq!(List::<i32>::nil().len(), 0);
        assert_eq!(list![1].len(), 1);
        assert_eq!(list![1, 2].len(), 2);
    }

    #[test]
    fn test_pattern_match() {
        let nil = List::<i32>::nil();
        match nil.as_ref() {
            &Nil => (),
            &Cons(_, _) => panic!()
        }

        let list = list![1];
        match list.as_ref() {
            &Nil => panic!(),
            &Cons(head, _) => assert_eq!(head, 1)
        }

        match *list {
            Nil => panic!(),
            Cons(head, _) => assert_eq!(head, 1)
        }
    }

    #[test]
    fn test_format() {
        assert_eq!(format!("{:?}", list!["a", "b"]), r#""a":"b":[]"#);
    }

    #[test]
    fn test_partial_ord() {
        assert_eq!(List::<f64>::nil().partial_cmp(List::nil()), Some(Equal));
        assert_eq!(list![1.0].partial_cmp(&List::nil()), Some(Greater));
        assert_eq!(List::<f64>::nil().partial_cmp(&list![1.0]), Some(Less));
        assert_eq!(list![1.0].partial_cmp(&list![1.0]), Some(Equal));

        assert_eq!(list![1.0, 1.0].partial_cmp(&list![1.0]), Some(Greater));
        assert_eq!(list![1.0].partial_cmp(&list![1.0, 1.0]), Some(Less));
        assert_eq!(list![2.0, 1.0].partial_cmp(&list![1.0, 1.0]), Some(Greater));
        assert_eq!(list![1.0, 1.0].partial_cmp(&list![2.0, 1.0]), Some(Less));
        assert_eq!(list![1.0, 2.0].partial_cmp(&list![1.0, 1.0]), Some(Greater));
        assert_eq!(list![1.0, 1.0].partial_cmp(&list![1.0, 2.0]), Some(Less));
        assert_eq!(list![1.0, 1.0].partial_cmp(&list![1.0, 1.0]), Some(Equal));

        assert_eq!(list![1.0].partial_cmp(&list![f64::NAN]), None);
        assert_eq!(list![1.0].partial_cmp(&list![1.0, f64::NAN]), Some(Less));
    }

    #[test]
    fn test_ord() {
        assert!(List::<i32>::nil() == List::nil());
        assert!(list![1] > List::nil());
        assert!(List::nil() < list![1]);
        assert!(list![1] == list![1]);

        assert!(list![1, 1] > list![1]);
        assert!(list![1] < list![1, 1]);
        assert!(list![1, 2] > list![1, 1]);
        assert!(list![1, 1] < list![1, 2]);
        assert!(list![2, 1] > list![1, 1]);
        assert!(list![1, 1] < list![2, 1]);
        assert!(list![1, 1] == list![1, 1]);
    }

    #[test]
    fn test_iter() {
        let vec: Vec<i32> = list![1, 2, 3].iter().collect();
        assert_eq!(vec, vec![1, 2, 3]);
    }

    #[test]
    fn test_into_iter_of_ref() {
        let mut cur = 1;
        let list = list![1, 2, 3];
        for n in &list {
            assert_eq!(n, cur);
            cur += 1;
        }
        assert_eq!(list.into_iter().collect::<Vec<_>>(), vec![1, 2, 3]);
    }

    #[test]
    fn test_eq() {
        assert_eq!(List::<i32>::nil(), list![]);

        let sub = list![2, 3];
        assert_eq!(1.cons(sub.clone()), 1.cons(sub));
    }
}
