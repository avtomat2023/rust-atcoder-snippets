//! Cumulative sum.

#[snippet = "cumulative"]
use std::ops::AddAssign;

#[snippet = "cumulative"]
pub trait Cumulative<T: AddAssign + Clone> {
    fn cumulate(&mut self);
}

#[snippet = "cumulative"]
impl<T: AddAssign + Clone> Cumulative<T> for [T] {
    fn cumulate(&mut self) {
        if let Some((first, rest)) = self.split_first_mut() {
            let mut acc = first.clone();
            for x in rest {
                *x += acc;
                acc = x.clone();
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_cumulate() {
        let mut test: [i32; 0] = [];
        test.cumulate();
        assert_eq!(test, []);

        let mut test = [1, 3, 5, 7];
        test.cumulate();
        assert_eq!(test, [1, 4, 9, 16]);

        let mut test = vec![1, 3, 5, 7];
        test.cumulate();
        assert_eq!(test, vec![1, 4, 9, 16]);
    }
}
