//! 2-dimentional array.

use crate::read::{Readable, Chars, read_lines};
use crate::option::BoolExt;
use crate::range::{UsizeRangeBoundsExt, BoundExt};

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

pub struct TableIndicesIterator {
    height: usize,
    width: usize,
    y: usize,
    x: usize
}

impl Iterator for TableIndicesIterator {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<(usize, usize)> {
        if self.x < self.width {
            self.x += 1;
            return Some((self.y, self.x-1))
        }

        if self.y+1 < self.height {
            self.y += 1;
            self.x = 1;
            return Some((self.y, 0))
        }

        None
    }
}

/// An iterator created by [`Table::rows`](struct.Table.html#method.rows).
pub struct TableRows<'a, T> {
    table: &'a Table<T>,
    index: usize
}

impl<'a, T> Iterator for TableRows<'a, T> {
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

pub trait TableRangeBounds {
    fn y_bounds(&self) -> (std::ops::Bound<usize>, std::ops::Bound<usize>);
    fn x_bounds(&self) -> (std::ops::Bound<usize>, std::ops::Bound<usize>);
}

// conflicting implementation
/*
impl<T1: std::ops::RangeBounds<usize>, T2: std::ops::RangeBounds<usize>> TableRangeBounds for (T1, T2) {
    fn y_bounds(&self) -> (std::ops::Bound<usize>, std::ops::Bound<usize>) {
        (self.0.start_bound().cloned(), self.0.end_bound().cloned())
    }

    fn x_bounds(&self) -> (std::ops::Bound<usize>, std::ops::Bound<usize>) {
        (self.1.start_bound().cloned(), self.1.end_bound().cloned())
    }
}
*/

impl<T: std::ops::RangeBounds<(usize, usize)>> TableRangeBounds for T {
    fn y_bounds(&self) -> (std::ops::Bound<usize>, std::ops::Bound<usize>) {
        (self.start_bound().map(|&(y, _)| y), self.end_bound().map(|&(y, _)| y))
    }

    fn x_bounds(&self) -> (std::ops::Bound<usize>, std::ops::Bound<usize>) {
        (self.start_bound().map(|&(_, x)| x), self.end_bound().map(|&(_, x)| x))
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

    /// Create a new table from rows without shape checking.
    pub unsafe fn from_rows_unchecked(rows: Vec<Vec<T>>) -> Table<T> {
        Table { inner: rows }
    }

    /// Number of rows.
    pub fn height(&self) -> usize {
        self.inner.len()
    }

    /// Number of columns.
    pub fn width(&self) -> usize {
        self.inner.first().map_or(0, |row| row.len())
    }

    /// `(height, column)`.
    pub fn shape(&self) -> (usize, usize) {
        (self.height(), self.width())
    }

    /// Creates an iterator yielding table indices as `(y, x)` in the dictionary order.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::table::*;
    /// let table = table![0; 2,3];
    /// let indices: Vec<(usize, usize)> = table.indices().collect();
    /// assert_eq!(indices, vec![
    ///     (0, 0), (0, 1), (0, 2),
    ///     (1, 0), (1, 1), (1, 2)
    /// ]);
    /// ```
    pub fn indices(&self) -> impl Iterator<Item=(usize, usize)> {
        TableIndicesIterator {
            height: self.height(),
            width: self.width(),
            y: if self.width() == 0 { self.height() } else { 0 },
            x: 0
        }
    }

    /// Checks the index is in range.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::table::*;
    /// let table = table![0; 5,5];
    /// assert_eq!(table.inside((4, 4)), true);
    /// assert_eq!(table.inside((4, 5)), false);
    /// ```
    pub fn inside(&self, (y, x): (usize, usize)) -> bool {
        y < self.height() && x < self.width()
    }

    pub fn get(&self, (y, x): (usize, usize)) -> Option<&T> {
        self.inner.get(y).and_then(|row| row.get(x))
    }

    pub fn get_mut(&mut self, (y, x): (usize, usize)) -> Option<&mut T> {
        self.inner.get_mut(y).and_then(|row| row.get_mut(x))
    }

    pub fn rows(&self) -> TableRows<T> {
        TableRows { table: self, index: 0 }
    }

    // Ant Book p. 37
    // TODO: Maybe out-of-range should not be treated as an error.
    /// Indices of vertically and horizontlly adjacent cells in the dictionary order.
    ///
    /// Useful for traversing a grid graph.
    ///
    /// If the given index is out of range, returns `None`.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::table::*;
    /// let table = table![0; 5,5];
    /// assert_eq!(table.adjacent4_indices((3,2)),
    ///            Some(vec![(2,2), (3,1), (3,3), (4,2)]));
    /// assert_eq!(table.adjacent4_indices((4,3)),
    ///            Some(vec![(3,3), (4,2), (4,4)]));
    /// ```
    pub fn adjacent4_indices(&self, (y, x): (usize, usize)) -> Option<Vec<(usize, usize)>> {
        self.inside((y, x)).then_with(|| {
            let mut result = Vec::with_capacity(4);
            if y > 0 {
                result.push((y-1, x));
            }
            if x > 0 {
                result.push((y, x-1));
            }
            if x < self.width()-1 {
                result.push((y, x+1));
            }
            if y < self.height()-1 {
                result.push((y+1, x));
            }
            result
        })
    }

    // Ant Book p. 35
    // TODO: Maybe out-of-range should not be treated as an error.
    /// Indices of 8 enclosing cells in the dictionary order.
    ///
    /// Useful for traversing a grid graph.
    ///
    /// If the given index is out of range, returns `None`.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::table::*;
    /// let table = table![0; 5,5];
    /// assert_eq!(table.adjacent8_indices((3,2)),
    ///            Some(vec![(2,1), (2,2), (2,3), (3,1), (3,3), (4,1), (4,2), (4,3)]));
    /// assert_eq!(table.adjacent8_indices((4,3)),
    ///            Some(vec![(3,2), (3,3), (3,4), (4,2), (4,4)]));
    /// ```
    pub fn adjacent8_indices(&self, (y, x): (usize, usize)) -> Option<Vec<(usize, usize)>> {
        self.inside((y, x)).then_with(|| {
            let mut result = Vec::with_capacity(8);
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
    /// Creates a cumulative table that can handle 2-dimentional range sum queries, etc.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::table::*;
    /// let rows = vec![
    ///     vec![0,    1,    2,    3,    4],
    ///     vec![0,   10,   20,   30,   40],
    ///     vec![0,  100,  200,  300,  400],
    ///     vec![0, 1000, 2000, 3000, 4000],
    /// ];
    /// let table = Table::from_rows(rows).unwrap();
    /// let cumulative = table.accumulate(0, |&a,&b| a+b, |&a,&b| a-b);
    /// // Calculates the sum of this subtable:
    /// // [[ 20,  30,  40],
    /// //  [200, 300, 400]]
    /// assert_eq!(cumulative.query_yx(1..=2, 2..).unwrap(), 990)
    /// ```
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

impl<T> std::ops::Index<(usize, usize)> for Table<T> {
    type Output = T;

    fn index(&self, index: (usize, usize)) -> &T {
        match self.get(index) {
            Some(result) => result,
            None => panic!(
                "index out of bounds: the table shape is {:?} but the index is {:?}",
                self.shape(), index
            )
        }
    }
}

impl<T> std::ops::IndexMut<(usize, usize)> for Table<T> {
    fn index_mut(&mut self, index: (usize, usize)) -> &mut T {
        // TODO: It may have a serious overhead to get the shape every time.
        let shape = self.shape();
        match self.get_mut(index) {
            Some(result) => result,
            None => panic!(
                "index out of bounds: the table shape is {:?} but the index is {:?}",
                shape, index
            )
        }
    }
}

impl<T, F1: Fn(&T, &T) -> T, F2: Fn(&T, &T) -> T> CumulativeTable<T, F1, F2> {
    pub fn query(&self, range: impl TableRangeBounds) -> Option<T> {
        self.query_yx(range.y_bounds(), range.x_bounds())
    }

    pub fn query_yx(&self, yrange: impl std::ops::RangeBounds<usize>, xrange: impl std::ops::RangeBounds<usize>) -> Option<T> {
        let y = yrange.to_range(self.inner.height() - 1)?;
        let x = xrange.to_range(self.inner.width() - 1)?;

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

pub fn backward2_indices((y, x): (usize, usize)) -> Vec<(usize, usize)> {
    let mut res = Vec::with_capacity(2);
    if y > 0 {
        res.push((y-1, x));
    }
    if x > 0 {
        res.push((y, x-1));
    }
    res
}

// TODO: Handle N x 0 tables.
/// Creates a table in a simlar way to `vec!` macro.
///
/// # Example
///
/// ```
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::table::*;
/// // Makes a table with 3 rows and 2 columns, filled by 0.
/// let table1 = table![0; 3,2];
/// assert_eq!(table1.height(), 3);
/// assert_eq!(table1.width(), 2);
///
/// // Makes an empty table.
/// let table2: Table<i32> = table![];
/// assert_eq!(table2.height(), 0);
/// assert_eq!(table2.width(), 0);
/// ```
#[macro_export]
macro_rules! table {
    () => {
        unsafe { Table::from_rows_unchecked(Vec::new()) }
    };

    ($element:expr ; $rows:expr , $cols:expr) => {
        unsafe { Table::from_rows_unchecked(vec![vec![$element; $cols]; $rows]) }
    };
}

pub fn read_table<T: Readable>() -> Table<T::Output> {
    let res: Vec<Vec<T::Output>> = read_lines::<Vec<T>>().collect();
    Table::from_rows(res).unwrap()
}

pub fn read_table_rows<T: Readable>(height: usize) -> Table<T::Output> {
    let res: Vec<Vec<T::Output>> = read_lines::<Vec<T>>().take(height).collect();
    if res.len() < height {
        panic!(
            "tried reading {} rows for table, but stdin has only {} lines",
            height, res.len()
        );
    }
    Table::from_rows(res).unwrap()
}

pub fn read_char_table() -> Table<char> {
    let res: Vec<Vec<char>> = read_lines::<Chars>().collect();
    Table::from_rows(res).unwrap()
}

pub fn read_char_table_rows(height: usize) -> Table<char> {
    let res: Vec<Vec<char>> = read_lines::<Chars>().take(height).collect();
    if res.len() < height {
        panic!(
            "tried reading {} rows for table, but stdin has only {} lines",
            height, res.len()
        );
    }
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
    fn test_indices() {
        fn indices(table: &Table<i32>) -> Vec<(usize, usize)> {
            table.indices().collect()
        }

        let table1: Table<i32> = table![];
        assert_eq!(indices(&table1), vec![]);
        let table2 = table![0; 3,0];
        assert_eq!(indices(&table2), vec![]);
        let table3 = table![0; 3,2];
        assert_eq!(indices(&table3), vec![(0,0), (0,1), (1,0), (1,1), (2,0), (2,1)]);
    }

    #[test]
    fn test_indices_exhausted() {
        let mut indices = table![0; 2,2].indices();
        assert_eq!(indices.next(), Some((0, 0)));
        assert_eq!(indices.next(), Some((0, 1)));
        assert_eq!(indices.next(), Some((1, 0)));
        assert_eq!(indices.next(), Some((1, 1)));
        assert_eq!(indices.next(), None);
        assert_eq!(indices.next(), None);
    }

    #[test]
    fn test_adjacent8_indices_trivial() {
        let empty_table: Table<i32> = table![];
        assert_eq!(empty_table.adjacent8_indices((0,0)), None);
        let singleton_table = table![0; 1,1];
        assert_eq!(singleton_table.adjacent8_indices((0,0)), Some(vec![]));
    }

    #[test]
    fn test_adjacent8_indices_row() {
        let table = table![0; 1,3];
        assert_eq!(table.adjacent8_indices((0,0)), Some(vec![(0,1)]));
        assert_eq!(table.adjacent8_indices((0,1)), Some(vec![(0,0), (0,2)]));
        assert_eq!(table.adjacent8_indices((0,2)), Some(vec![(0,1)]));
        assert_eq!(table.adjacent8_indices((0,3)), None);
        assert_eq!(table.adjacent8_indices((1,0)), None);
    }

    #[test]
    fn test_adjacent8_indices_column() {
        let table = table![0; 3,1];
        assert_eq!(table.adjacent8_indices((0,0)), Some(vec![(1,0)]));
        assert_eq!(table.adjacent8_indices((1,0)), Some(vec![(0,0), (2,0)]));
        assert_eq!(table.adjacent8_indices((2,0)), Some(vec![(1,0)]));
        assert_eq!(table.adjacent8_indices((3,0)), None);
        assert_eq!(table.adjacent8_indices((0,1)), None);
    }

    #[test]
    fn test_adjacent8_indices_2x2() {
        let table = table![0; 2,2];
        assert_eq!(table.adjacent8_indices((0,0)), Some(vec![(0,1), (1,0), (1,1)]));
        assert_eq!(table.adjacent8_indices((0,1)), Some(vec![(0,0), (1,0), (1,1)]));
        assert_eq!(table.adjacent8_indices((1,0)), Some(vec![(0,0), (0,1), (1,1)]));
        assert_eq!(table.adjacent8_indices((1,1)), Some(vec![(0,0), (0,1), (1,0)]));
    }

    #[test]
    fn test_adjacent8_indices_3x3() {
        let table = table![0; 3,3];
        let check = |y: usize, x: usize| {
            table.adjacent8_indices((y, x)).unwrap()
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

    #[test]
    fn test_backward2_indices() {
        assert_eq!(backward2_indices((0, 0)), vec![]);
        assert_eq!(backward2_indices((0, 1)), vec![(0, 0)]);
        assert_eq!(backward2_indices((1, 0)), vec![(0, 0)]);
        assert_eq!(backward2_indices((1, 1)), vec![(0, 1), (1, 0)]);

        assert_eq!(backward2_indices((5, 0)), vec![(4, 0)]);
        assert_eq!(backward2_indices((0, 5)), vec![(0, 4)]);
        assert_eq!(backward2_indices((5, 5)), vec![(4, 5), (5, 4)]);
    }
}
