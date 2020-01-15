//! Enriches `bool` for getting `Option` value.

// BEGIN SNIPPET option

pub trait BoolExt {
    fn then<T>(self, value: T) -> Option<T>;
    fn then_with<T, F>(self, f: F) -> Option<T> where F: FnOnce() -> T;
    fn and<T>(self, option: Option<T>) -> Option<T>;
    fn and_then<T, F>(self, f: F) -> Option<T> where F: FnOnce() -> Option<T>;
}

impl BoolExt for bool {
    fn then<T>(self, value: T) -> Option<T> {
        if self { Some(value) } else { None }
    }

    fn then_with<T, F>(self, f: F) -> Option<T> where F: FnOnce() -> T {
        if self { Some(f()) } else { None }
    }

    fn and<T>(self, option: Option<T>) -> Option<T> {
        if self { option } else { None }
    }

    fn and_then<T, F>(self, f: F) -> Option<T> where F: FnOnce() -> Option<T> {
        if self { f() } else { None }
    }
}

// END SNIPPET

/*
trait OptionExt<T> {
    fn get_or_insert_with<F: FnOnce() -> T>(&mut self, f: F) -> &mut T;
}

impl<T> OptionExt<T> for Option<T> {
    fn get_or_insert_with<F: FnOnce() -> T>(&mut self, f: F) -> &mut T {
        match *self {
            None => *self = Some(f()),
            _ => ()
        }

        self.as_mut().unwrap()
    }
}
*/
