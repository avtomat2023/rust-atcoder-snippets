#[snippet = "option"]
trait RichOption<T> {
    fn get_or_insert_with<F: FnOnce() -> T>(&mut self, f: F) -> &mut T;
}

#[snippet = "option"]
impl<T> RichOption<T> for Option<T> {
    fn get_or_insert_with<F: FnOnce() -> T>(&mut self, f: F) -> &mut T {
        match *self {
            None => *self = Some(f()),
            _ => ()
        }

        self.as_mut().unwrap()
    }
}
