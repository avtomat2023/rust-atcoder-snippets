//! Enriches `bool` and `Option`.

// BEGIN SNIPPET option

pub trait BoolExt {
    /// Gets `Some(value)` if `self` is true, otherwise `None`.
    fn then<T>(self, value: T) -> Option<T>;
    /// Gets `Some(f())` if `self` is true, otherwise `None`.
    fn then_with<T, F>(self, f: F) -> Option<T> where F: FnOnce() -> T;
    /// Gets `option` if `self` is true, otherwise `None`.
    fn and<T>(self, option: Option<T>) -> Option<T>;
    /// Gets `f()` if `self` is true, otherwise `None`.
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

trait OptionExt<T> {
    /// Convert to string or get default.
    ///
    /// Useful for printing the `u32` answer if it exists, otherwise `"-1"`.
    fn to_string_or<U: std::fmt::Display>(&self, default: U) -> String
    where
        T: std::fmt::Display;
    // fn get_or_insert_with<F: FnOnce() -> T>(&mut self, f: F) -> &mut T;
}

impl<T> OptionExt<T> for Option<T> {
    fn to_string_or<U: std::fmt::Display>(&self, default: U) -> String
    where
        T: std::fmt::Display
    {
        self.as_ref().map(|x| x.to_string()).unwrap_or(default.to_string())
    }

    /*
    fn get_or_insert_with<F: FnOnce() -> T>(&mut self, f: F) -> &mut T {
        match *self {
            None => *self = Some(f()),
            _ => ()
        }

        self.as_mut().unwrap()
    }
    */
}

/// Enrich all types by adding `guard` method
trait Guard: Sized {
    /// `Some(self)` if `pred(&self)` holds, otherwise `None`.
    fn guard(self, pred: impl FnOnce(&Self) -> bool) -> Option<Self>;
}

impl<T> Guard for T {
    fn guard(self, pred: impl FnOnce(&T) -> bool) -> Option<T> {
        if pred(&self) { Some(self) } else { None }
    }
}

// END SNIPPET
