/// Data structures.

#[snippet = "collections"]
use std::rc::Rc;
#[snippet = "collections"]
use std::ops::Deref;
#[snippet = "collections"]
use std::fmt;
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

/// Immutable and persistent list heavily used in functional languages.
///
/// https://docs.rs/immutable/0.1.1/immutable/list/enum.List.html
///
/// 要素型にCloneを要求しているのは、コンスセルがRcを用いて参照されており、
/// headへの参照がうまく取り出せないためである。
/// To create a list of values not `Clone` or costly to `Clone`,
/// create `List<Rc<T>>` instead of `List<T>`.
#[snippet = "collections"]
#[derive(Clone, PartialEq, Eq)]
pub struct List<T: Clone> {
    inner: Rc<ListInner<T>>
}

#[snippet = "collections"]
impl<T: Clone> List<T> {
    pub fn nil() -> List<T> { List { inner: Rc::new(Nil) } }

    pub fn is_empty(&self) -> bool {
        match **self {
            Nil => true,
            Cons(_, _) => false
        }
    }

    pub fn len(&self) -> usize { self.iter().count() }

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
trait IntoCons<T: Clone, L: Borrow<List<T>>> {
    fn cons(self, tail: L) -> List<T>;
}

#[snippet = "collections"]
impl<T: Clone, L: Borrow<List<T>>> IntoCons<T, L> for T {
    fn cons(self, tail: L) -> List<T> {
        List { inner: Rc::new(Cons(self, tail.borrow().clone().into())) }
    }
}

// TODO: Take a bench comparing with IntoCons
trait IntoConsByMove<T: Clone> {
    fn cons_move(self, tail: List<T>) -> List<T>;
}

impl<T: Clone> IntoConsByMove<T> for T {
    fn cons_move(self, tail: List<T>) -> List<T> {
        List { inner: Rc::new(Cons(self, tail)) }
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
