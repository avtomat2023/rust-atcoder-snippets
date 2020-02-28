//! 2-dimentional array.

use crate::read::{Readable, readx, readn};
use crate::option::BoolExt;

// BEGIN SNIPPET table DEPENDS ON read option

/// 2-dimentional array.
///
/// In competitive programming, a lot of problems require handling 2-dimentional tables.
/// This struct provides utility methods for a table.
///
/// All rows in a table must have the same length.
///
/// Table can have 0-length rows, but it's impossible to have 0-length columns.
pub struct Table<T> {
    inner: Vec<Vec<T>>
}

/// An iterator created by [`Table::rows`](struct.Table.html#method.rows).
pub struct TableRows<'a, T: 'a> {
    table: &'a Table<T>,
    index: usize
}

impl<'a, T: 'a> Iterator for TableRows<'a, T> {
    type Item = &'a [T];

    fn next(&mut self) -> Option<&'a [T]> {
        if self.index < self.table.height() {
            let i = self.index;
            self.index += 1;
            Some(&self.table.inner[i])
        } else {
            None
        }
    }
}

// ABC005 D
/// A table created by [`Table::accumulate`](struct.Table.html#method.accumulate).
pub struct CumulativeTable<T, F1, F2> {
    op: F1,
    op_inv: F2,
    inner: Table<T>
}

impl<T> Table<T> {
    /// Creates a new table from rows represented as `Vec<Vec<T>>`.
    ///
    /// All rows must have the same length. Otherwise, returns `None`.
    pub fn from_rows(rows: Vec<Vec<T>>) -> Option<Table<T>> {
        rows.windows(2).all(|window| window[0].len() == window[1].len())
            .then_with(|| Table { inner: rows })
    }

    pub fn height(&self) -> usize {
        self.inner.len()
    }

    pub fn width(&self) -> usize {
        self.inner.first().map_or(0, |row| row.len())
    }

    /// Checks the index is in range.
    ///
    /// # Example
    ///
    /// ```edition2018
    /// # use atcoder_snippets::table::*;
    /// let table = table![5,5];
    /// assert_eq!(table.in_range((4, 4)), true);
    /// assert_eq!(table.in_range((4, 5)), false);
    /// ```
    pub fn in_range(&self, (y, x): (usize, usize)) -> bool {
        y < self.height() && x < self.width()
    }

    pub fn rows(&self) -> TableRows<T> {
        TableRows { table: self, index: 0 }
    }

    // Ant Book p. 35
    // TODO: Maybe out-of-range should not be treated as an error.
    /// Indices of enclosing 8 cells in the dictionary order.p
    ///
    /// Useful for traversing a grid graph.
    ///
    /// If the given index is out of range, returns `None`.
    ///
    /// # Example
    ///
    /// ```edition2018
    /// # use atcoder_snippets::table::*;
    /// let table = table![5,5];
    /// assert_eq!(table.adjacent_8_indices((3,2)),
    ///            Some(vec![(2,1), (2,2), (2,3), (3,1), (3,3), (4,1), (4,2), (4,3)]));
    /// assert_eq!(table.adjacent_8_indices((4,3)),
    ///            Some(vec![(3,2), (3,3), (3,4), (4,2), (4,4)]));
    /// ```
    pub fn adjacent_8_indices(&self, (y, x): (usize, usize)) -> Option<Vec<(usize, usize)>> {
        self.in_range((y, x)).then_with(|| {
            let mut result = Vec::new();
            let xs = x.saturating_sub(1) ..= std::cmp::min(x+1, self.width()-1);

            if y > 0 {
                for x in xs.clone() {
                    result.push((y-1, x));
                }
            }

            if x > 0 {
                result.push((y, x-1));
            }
            if x < self.width()-1 {
                result.push((y, x+1));
            }

            if y < self.height()-1 {
                for x in xs {
                    result.push((y+1, x));
                }
            }

            result
        })
    }

    // ABC005 D
    pub fn accumulate<F1, F2>(&self, identity: T, op: F1, op_inv: F2)
                              -> CumulativeTable<T, F1, F2>
    where
        T: Clone,
        F1: Fn(&T, &T) -> T,
        F2: Fn(&T, &T) -> T
    {
        let mut inner = vec![vec![identity.clone(); self.width() + 1]];
        for table_row in self.rows() {
            let mut new_row = vec![identity.clone()];
            {
                let last_row = inner.last().unwrap();
                for (x, acc1) in table_row.iter().zip(last_row.windows(2)) {
                    // Do op before op_inv in order to avoid overflow when op is addtion
                    let result = {
                        let acc2 = new_row.last().unwrap();
                        let tmp1 = op(x, &acc1[1]);
                        let tmp2 = op(&tmp1, acc2);
                        op_inv(&tmp2, &acc1[0])
                    };
                    new_row.push(result);
                }
            }
            inner.push(new_row);
        }
        CumulativeTable { op: op, op_inv: op_inv, inner: Table { inner: inner } }
    }
}

impl<T, F1: Fn(&T, &T) -> T, F2: Fn(&T, &T) -> T> CumulativeTable<T, F1, F2> {
    pub fn query(&self, y: std::ops::Range<usize>, x: std::ops::Range<usize>) -> Option<T> {
        if y.start > y.end || y.end > self.inner.height() - 1 {
            return None;
        }
        if x.start > x.end || x.end > self.inner.width() - 1 {
            return None;
        }

        let val1 = &self.inner.inner[y.end][x.end];
        let val2 = &self.inner.inner[y.end][x.start];
        let val3 = &self.inner.inner[y.start][x.end];
        let val4 = &self.inner.inner[y.start][x.start];
        // Do op before op_inv in order to avoid overflow when op is addtion
        let tmp1 = (self.op)(val1, val4);
        let tmp2 = (self.op)(val2, val3);
        let result = (self.op_inv)(&tmp1, &tmp2);
        Some(result)
    }
}

// TODO: Handle N x 0 tables.
/// Creates a table in a simlar way to `vec!` macro.
///
/// # Example
///
/// ```edition2018
/// # use atcoder_snippets::table::*;
/// // Makes a table with 3 rows and 2 columns, filled by 0.
/// let table1 = table![0; 3,2];
/// assert_eq!(table1.rows_count(), 3);
/// assert_eq!(table1.cols_count(), 2);
/// // Makes an empty table.
/// let table2 = table![];
/// assert_eq!(table2.rows_count(), 0);
/// assert_eq!(table2.cols_count(), 0);
/// ```
#[macro_export]
macro_rules! table {
    () => {
        Table { inner: Vec::new() }
    };

    ($element:expr ; $rows:expr , $cols:expr) => {
        Table { inner: vec![vec![$element; $cols]; $rows] }
    };
}

pub fn read_table<T: Readable>() -> Table<T::Output> {
    let res = readx::<Vec<T>>();
    Table::from_rows(res).unwrap()
}

pub fn read_table_rows<T: Readable>(height: usize) -> Table<T::Output> {
    let res = readn::<Vec<T>>(height);
    Table::from_rows(res).unwrap()
}

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_rows() {
        let empty_table: Vec<Vec<i32>> = Vec::new();
        assert!(Table::from_rows(empty_table).is_some());

        let row0: Vec<i32> = Vec::new();
        assert!(Table::from_rows(vec![row0.clone()]).is_some());
        assert!(Table::from_rows(vec![row0.clone(), row0.clone()]).is_some());

        let row1 = vec![1];
        assert!(Table::from_rows(vec![row1.clone()]).is_some());
        assert!(Table::from_rows(vec![row1.clone(), row1.clone()]).is_some());
        assert!(Table::from_rows(vec![row0.clone(), row1.clone()]).is_none());
    }

    #[test]
    fn test_size() {
        let table1: Table<i32> = table![];
        assert_eq!(table1.height(), 0);
        assert_eq!(table1.width(), 0);

        let table2 = table![0; 3,0];
        assert_eq!(table2.height(), 3);
        assert_eq!(table2.width(), 0);

        let table3 = table![0; 3,2];
        assert_eq!(table3.height(), 3);
        assert_eq!(table3.width(), 2);
    }

    #[test]
    fn test_adjacent_8_indices_trivial() {
        let empty_table: Table<i32> = table![];
        assert_eq!(empty_table.adjacent_8_indices((0,0)), None);
        let singleton_table = table![0; 1,1];
        assert_eq!(singleton_table.adjacent_8_indices((0,0)), Some(vec![]));
    }

    #[test]
    fn test_adjacent_8_indices_row() {
        let table = table![0; 1,3];
        assert_eq!(table.adjacent_8_indices((0,0)), Some(vec![(0,1)]));
        assert_eq!(table.adjacent_8_indices((0,1)), Some(vec![(0,0), (0,2)]));
        assert_eq!(table.adjacent_8_indices((0,2)), Some(vec![(0,1)]));
        assert_eq!(table.adjacent_8_indices((0,3)), None);
        assert_eq!(table.adjacent_8_indices((1,0)), None);
    }

    #[test]
    fn test_adjacent_8_indices_column() {
        let table = table![0; 3,1];
        assert_eq!(table.adjacent_8_indices((0,0)), Some(vec![(1,0)]));
        assert_eq!(table.adjacent_8_indices((1,0)), Some(vec![(0,0), (2,0)]));
        assert_eq!(table.adjacent_8_indices((2,0)), Some(vec![(1,0)]));
        assert_eq!(table.adjacent_8_indices((3,0)), None);
        assert_eq!(table.adjacent_8_indices((0,1)), None);
    }

    #[test]
    fn test_adjacent_8_indices_2x2() {
        let table = table![0; 2,2];
        assert_eq!(table.adjacent_8_indices((0,0)), Some(vec![(0,1), (1,0), (1,1)]));
        assert_eq!(table.adjacent_8_indices((0,1)), Some(vec![(0,0), (1,0), (1,1)]));
        assert_eq!(table.adjacent_8_indices((1,0)), Some(vec![(0,0), (0,1), (1,1)]));
        assert_eq!(table.adjacent_8_indices((1,1)), Some(vec![(0,0), (0,1), (1,0)]));
    }

    #[test]
    fn test_adjacent_8_indices_3x3() {
        let table = table![0; 3,3];
        let check = |y: usize, x: usize| {
            table.adjacent_8_indices((y, x)).unwrap()
        };
        assert_eq!(check(0,0), vec![(0,1), (1,0), (1,1)]);
        assert_eq!(check(0,1), vec![(0,0), (0,2), (1,0), (1,1), (1,2)]);
        assert_eq!(check(0,2), vec![(0,1), (1,1), (1,2)]);
        assert_eq!(check(1,0), vec![(0,0), (0,1), (1,1), (2,0), (2,1)]);
        assert_eq!(check(1,1), vec![(0,0), (0,1), (0,2), (1,0), (1,2), (2,0), (2,1), (2,2)]);
        assert_eq!(check(1,2), vec![(0,1), (0,2), (1,1), (2,1), (2,2)]);
        assert_eq!(check(2,0), vec![(1,0), (1,1), (2,1)]);
        assert_eq!(check(2,1), vec![(1,0), (1,1), (1,2), (2,0), (2,2)]);
        assert_eq!(check(2,2), vec![(1,1), (1,2), (2,1)]);
    }
}
