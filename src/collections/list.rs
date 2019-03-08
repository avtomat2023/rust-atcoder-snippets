//! Functional list.

/// For pattern match.
///
/// It is not necessary to use this enum directly.
/// See [Example section of `List`](struct.List.html#example)
/// for usage in pattern matching.
#[snippet = "list"]
#[derive(Clone, PartialEq, Eq)]
pub enum ListInner<T: Clone> {
    Nil,
    Cons(T, List<T>)
}

#[snippet = "list"]
pub use self::ListInner::{Nil, Cons};

// The example is ignored because `flatten` method by `iter` snippet collide
// `flatten` of `std::iter::Iterator` in Rust >= 1.29.0

/// Immutable and persistent list heavily used in functional languages.
///
/// The item type must be `Clone` because it is impossible to borrow the head of a cons cell
/// referenced by `Rc`.
/// To create a list of values not `Clone` or costly to `Clone`,
/// create `List<Rc<T>>` instead of `List<T>`.
///
/// Each list contains its length, so the length can be obtained in constant time,
/// although it takes O(n) time almost all functional languages.
///
/// The implementation is based on [`List`](https://docs.rs/immutable/0.1.1/immutable/list/enum.List.html) in `immutable` crate,
/// but the interface and implementation details are modified a lot.
///
/// # Example
///
/// To make a list, use [`List::nil`](#method.nil), [`IntoCons`](trait.IntoCons.html) trait
/// or [`list`](../macro.list.html) macro.
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::collections::list::*;
/// assert_eq!(List::<i32>::nil(), list![]);
/// let sublist = 2.cons(List::nil());
/// assert_eq!(1.cons(sublist), list![1, 2]);
/// ```
///
/// By `as_ref` method of `AsRef` trait impl-ed by `List`, you can use pattern matching.
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::collections::list::*;
/// fn power_set<T: Clone>(set: &List<T>) -> List<List<T>> {
///     match set.as_ref() {
///         &Nil => list![list![]],
///         &Cons(ref head, ref tail) => {
///             let subsets = power_set(&tail);
///             subsets.iter().map(|list| head.clone().cons(list))
///                 .collect::<List<_>>()
///                 .append(&subsets)
///         }
///     }
/// }
///
/// assert_eq!(
///     power_set(&list![1, 2, 3]),
///     list![list![1, 2, 3], list![1, 2], list![1, 3], list![1],
///           list![2, 3], list![2], list![3], list![]]
/// );
/// ```
///
/// However, it is not possible to use deeper patterns such as `Cons(a, Cons(b, _))`.
///
/// Finally, solves [ABC118 D: Match Matching](https://atcoder.jp/contests/abc118/tasks/abc118_d) by memoized depth-first search.
/// The solution takes advantage of constant time `len()`.
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
#[snippet = "list"]
#[derive(Clone, PartialEq, Eq)]
pub struct List<T: Clone> {
    inner: std::rc::Rc<ListInner<T>>,
    len: usize
}

#[snippet = "list"]
impl<T: Clone> List<T> {
    pub fn nil() -> List<T> { List { inner: std::rc::Rc::new(Nil), len: 0 } }

    /// Whether the list is nil.
    pub fn is_nil(&self) -> bool {
        match self.as_ref() {
            &Nil => true,
            &Cons(_, _) => false
        }
    }

    /// Length of the list.
    ///
    /// `len()` is O(1) time because each sublist holds its length.
    pub fn len(&self) -> usize { self.len }

    /// Extract head of non-empty list.
    ///
    /// # Panic
    ///
    /// Panics if `self` is nil.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::list::*;
    /// assert_eq!(list![1, 2, 3].head(), 1);
    /// ```
    pub fn head(&self) -> T {
        match self.as_ref() {
            &Nil => panic!("cannot find head of nil"),
            &Cons(ref head, _) => head.clone()
        }
    }

    /// Extract tail of non-empty list.
    ///
    /// # Panic
    ///
    /// Panics if `self` is nil.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::list::*;
    /// assert_eq!(list![1, 2, 3].tail(), list![2, 3]);
    /// ```
    pub fn tail(&self) -> List<T> {
        match self.as_ref() {
            &Nil => panic!("cannot find head of nil"),
            &Cons(_, ref tail) => tail.clone()
        }
    }

    /// Gets an iterator without moving `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::collections::list::*;
    /// let mut iter = list![1, 2, 3].iter();
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> ListIter<T> {
        ListIter { iter: self.clone() }
    }

    /// Concatenates two lists.
    pub fn append(&self, other: &List<T>) -> List<T> {
        append_tailrec(self, other, List::nil())
    }

    /// Reverses `self`, then concatenates two lists.
    pub fn rev_append(&self, other: &List<T>) -> List<T> {
        match self.as_ref() {
            &Nil => other.clone(),
            &Cons(ref head, ref tail) =>
                tail.rev_append(&head.clone().cons(other))
        }
    }

    #[cfg(test)]
    fn take(self) -> std::rc::Rc<ListInner<T>> {
        self.inner
    }
}

#[snippet = "list"]
fn append_tailrec<T: Clone>(
    list1: &List<T>,
    list2: &List<T>,
    list1_rev: List<T>
) -> List<T> {
    match list1.as_ref() {
        &Nil => list1_rev.rev_append(list2),
        &Cons(ref head, ref tail) =>
            append_tailrec(tail, list2, head.clone().cons(list1_rev))
    }
}

/// For pattern matching.
///
/// # Example
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::collections::list::*;
/// let list = list![1, 2, 3];
/// match list.as_ref() {
///     // The patterns can be writtern `Nil` and `Cons(head, tail)`
///     // by match ergonomics in Rust >=1.26.0
///     &Nil => println!("The list is nil."),
///     &Cons(ref head, ref tail) =>
///         println!("head = {}, length of tail = {}", head, tail.len())
/// }
///
/// // `list` is not moved, still usable.
/// println!("length of list = {}", list.len());
/// ```
#[snippet = "list"]
impl<T: Clone> AsRef<ListInner<T>> for List<T> {
    fn as_ref(&self) -> &ListInner<T> {
        self.inner.as_ref()
    }
}

/*
 * If the given list is singleton `Rc`, `list.into()` may be slightly efficient.
 * However, it is too complecated for users to think about whether the list is singleton,
 * so I don't provide this impl until a usecase is found.
 *
 * /// For pattern matching.
 * ///
 * /// The content of the list (nil or cons cell) referenced by `Rc` may be cloned.
 * ///
 * /// # Example
 * ///
 * /// ```
 * /// # #[macro_use] extern crate atcoder_snippets;
 * /// # use atcoder_snippets::collections::list::*;
 * /// let list = list![1, 2, 3];
 * ///
 * /// match list.into() {
 * ///     Nil => println!("The list is nil."),
 * ///     Cons(head, tail) =>
 * ///         println!("head = {}, length of tail = {}", head, tail.len())
 * /// }
 * ///
 * /// // `list` is moved, cannot use it anymore.
 * /// ```
 * #[snippet = "list"]
 * impl<T: Clone> From<List<T>> for ListInner<T> {
 *     fn from(list: List<T>) -> ListInner<T> {
 *         match std::rc::Rc::try_unwrap(list.inner) {
 *             Ok(list_inner) => list_inner,
 *             Err(list) => list.as_ref().clone()
 *         }
 *     }
 * }
 */

/// Formatting for debug.
///
/// # Example:
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::collections::list::*;
/// assert_eq!(format!("{:?}", list!["a", "b"]), r#""a" :: "b" :: nil"#);
/// ```
#[snippet = "list"]
impl<T: Clone + std::fmt::Debug> std::fmt::Debug for List<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.inner.as_ref() {
            &Nil => write!(f, "nil"),
            &Cons(ref head, ref tail) => write!(f, "{:?} :: {:?}", head, tail)
        }
    }
}

/// Comparation by dictionary order.
#[snippet = "list"]
impl<T: Clone + PartialOrd> PartialOrd for List<T> {
    fn partial_cmp(&self, other: &List<T>) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering::*;
        match (self.as_ref(), other.as_ref()) {
            (&Nil, &Nil) => Some(Equal),
            (&Nil, &Cons(_, _)) => Some(Less),
            (&Cons(_, _), &Nil) => Some(Greater),
            (&Cons(ref head1, ref tail1), &Cons(ref head2, ref tail2)) => {
                head1.partial_cmp(&head2).and_then(|ordering| {
                    match ordering {
                        Equal => tail1.partial_cmp(tail2),
                        _ => Some(ordering)
                    }
                })
            }
        }
    }
}

/// Comparation by dictionary order.
#[snippet = "list"]
impl<T: Clone + Ord> Ord for List<T> {
    fn cmp(&self, other: &List<T>) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;
        match (self.as_ref(), other.as_ref()) {
            (&Nil, &Nil) => Equal,
            (&Nil, &Cons(_, _)) => Less,
            (&Cons(_, _), &Nil) => Greater,
            (&Cons(ref head1, ref tail1), &Cons(ref head2, ref tail2)) => {
                match head1.cmp(&head2) {
                    Equal => tail1.cmp(tail2),
                    determined => determined
                }
            }
        }
    }
}

/// An iterator over the items of a `List`.
#[snippet = "list"]
pub struct ListIter<T: Clone> {
    iter: List<T>
}

#[snippet = "list"]
impl<T: Clone> Iterator for ListIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let cons;
        match self.iter.as_ref() {
            &Nil => return None,
            &Cons(ref head, ref tail) => cons = (head.clone(), tail.clone())
        }
        self.iter = cons.1;
        Some(cons.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.iter.len(), Some(self.iter.len()))
    }

    fn count(self) -> usize {
        self.iter.len()
    }
}

#[snippet = "list"]
impl<T: Clone> ExactSizeIterator for ListIter<T> {}

#[snippet = "list"]
impl<T: Clone> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = ListIter<T>;

    fn into_iter(self) -> ListIter<T> {
        ListIter { iter: self }
    }
}

#[snippet = "list"]
impl<'a, T: Clone> IntoIterator for &'a List<T> {
    type Item = T;
    type IntoIter = ListIter<T>;

    fn into_iter(self) -> ListIter<T> {
        self.iter()
    }
}

// TODO: Bench
// TODO: Specialize the implementation when IntoIter is DoubleEndedIterator
/// Collects into `List`.
///
/// # Example
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::collections::list::*;
/// assert_eq!(vec![1, 2, 3].into_iter().collect::<List<_>>(), list![1, 2, 3]);
/// ```
#[snippet = "list"]
impl<T: Clone> std::iter::FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> List<T> {
        let xs: Vec<T> = iter.into_iter().collect();
        let mut list = List::nil();
        for x in xs.into_iter().rev() {
            list = x.cons(list);
        }
        list
    }
}

/// A trait for making a cons cell in intuitive way.
///
/// # Example
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::collections::list::*;
/// assert_eq!(1.cons(2.cons(List::nil())), list![1, 2]);
/// ```
#[snippet = "list"]
pub trait IntoCons<T: Clone, L: std::borrow::Borrow<List<T>>> {
    fn cons(self, tail: L) -> List<T>;
}

#[snippet = "list"]
impl<T: Clone, L: std::borrow::Borrow<List<T>>> IntoCons<T, L> for T {
    fn cons(self, tail: L) -> List<T> {
        let tail_cloned: List<T> = tail.borrow().clone().into();
        let tail_len = tail_cloned.len;
        List {
            inner: std::rc::Rc::new(Cons(self, tail_cloned)),
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
            inner: std::rc::Rc::new(Cons(self, tail)),
            len: tail_len + 1
        }
    }
}

/// Makes a list by enumerating its contents.
///
/// See [Example section of `List`](collections/struct.List.html#example) for usage.
#[snippet = "list"]
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
    use std::rc::Rc;
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
    }

    #[test]
    fn test_partial_ord() {
        assert_eq!(List::<f64>::nil().partial_cmp(&List::nil()), Some(Equal));
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
