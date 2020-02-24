//! 2-dimentional array.

use crate::read::{Readable, readx, readn};
use crate::option::BoolExt;
use crate::range::UsizeRangeBoundsExt;

// BEGIN SNIPPET table DEPENDS ON read option range

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
pub struct TableRows<'a, T> {
    table: &'a Table<T>,
    index: usize
}

impl<'a, T> Iterator for TableRows<'a, T> {
    type Item = &'a [T];

    fn next(&mut self) -> Option<&'a [T]> {
        if self.index < self.table.row_count() {
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

    pub fn row_count(&self) -> usize {
        self.inner.len()
    }

    pub fn col_count(&self) -> usize {
        self.inner.first().map_or(0, |row| row.len())
    }

    pub fn rows(&self) -> TableRows<T> {
        TableRows { table: self, index: 0 }
    }

    // ABC005 D
    pub fn accumulate<F1, F2>(&self, identity: T, op: F1, op_inv: F2)
                              -> CumulativeTable<T, F1, F2>
    where
        T: Clone,
        F1: Fn(&T, &T) -> T,
        F2: Fn(&T, &T) -> T
    {
        let mut inner = vec![vec![identity.clone(); self.col_count() + 1]];
        for table_row in self.rows() {
            let mut new_row = vec![identity.clone()];
            let last_row = inner.last().unwrap();
            for (x, acc1) in table_row.iter().zip(last_row.windows(2)) {
                // Do op before op_inv in order to avoid overflow when op is addtion
                let acc2 = new_row.last().unwrap();
                let tmp1 = op(x, &acc1[1]);
                let tmp2 = op(&tmp1, acc2);
                new_row.push(op_inv(&tmp2, &acc1[0]));
            }
            inner.push(new_row);
        }
        CumulativeTable { op, op_inv, inner: Table { inner } }
    }
}

impl<T, F1: Fn(&T, &T) -> T, F2: Fn(&T, &T) -> T> CumulativeTable<T, F1, F2> {
    pub fn query(&self, yrange: impl std::ops::RangeBounds<usize>, xrange: impl std::ops::RangeBounds<usize>) -> Option<T> {
        let y = yrange.to_range(self.inner.row_count() - 1)?;
        let x = xrange.to_range(self.inner.col_count() - 1)?;

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

pub fn read_table_rows<T: Readable>(row_count: usize) -> Table<T::Output> {
    let res = readn::<Vec<T>>(row_count);
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
    fn test_count() {
        let table1: Table<i32> = table![];
        assert_eq!(table1.row_count(), 0);
        assert_eq!(table1.col_count(), 0);

        let table2 = table![0; 3,0];
        assert_eq!(table2.row_count(), 3);
        assert_eq!(table2.col_count(), 0);

        let table3 = table![0; 3,2];
        assert_eq!(table3.row_count(), 3);
        assert_eq!(table3.col_count(), 2);
    }
}
