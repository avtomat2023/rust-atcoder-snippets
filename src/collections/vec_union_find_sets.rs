//! Disjoint-set data structure, known as union-find.

use std;

// BEGIN SNIPPET vec_union_find_sets

// TODO: Show solution of ABC120 D, ABC126 E and ABC157 D as examples
/// Disjoint-set data structure, known as union-find, for integers `0..n`.
///
/// Thanks to union-by-size and path-compression strategy,
/// average cost of each operation is so much low that
/// it can be regarded as constant time, although theoretically it is not constant.
pub struct VecUnionFindSets {
    // Maintaining `set_count` can be an unnecessary cost,
    // but that frees users from maintaining it
    // by checking the returned values for all `add` and `unite` operations.
    set_count: usize,  items: Vec<VecUnionFindNode>
}

#[derive(Clone)]
struct VecUnionFindNode {
    parent: std::cell::Cell<usize>,
    len: usize
}

impl VecUnionFindNode {
    fn new(item: usize) -> VecUnionFindNode {
        VecUnionFindNode {
            parent: std::cell::Cell::new(item),
            len: 1
        }
    }
}

impl VecUnionFindSets {
    /// Creates empty sets.
    pub fn new() -> VecUnionFindSets {
        VecUnionFindSets {
            set_count: 0,
            items: Vec::new()
        }
    }

    /// Creates `count` singleton sets.
    pub fn with_items(items_count: usize) -> VecUnionFindSets {
        let mut sets = VecUnionFindSets::new();
        sets.add_items(items_count);
        sets
    }

    fn error_msg(items: &[usize]) -> String {
        assert!(items.len() == 1 || items.len() == 2);
        if items.len() == 1 {
            format!("no set contains {}", items[0])
        } else {
            format!("no set contains {} and no set contains {}", items[0], items[1])
        }
    }

    /// Adds `count` items labeled `n..n+count`, where `n` is how many items the sets currently have.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::collections::vec_union_find_sets::*;
    /// let mut sets = VecUnionFindSets::new();
    /// sets.add_items(3);
    /// assert_eq!(sets.count(), 3);
    /// ```
    pub fn add_items(&mut self, count: usize) {
        self.set_count += count;
        let new_items = (self.items_len()..self.items_len()+count)
            .map(|i| VecUnionFindNode::new(i));
        self.items.extend(new_items);
    }

    /// Returns how many items are contained by all the sets.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::collections::vec_union_find_sets::*;
    /// let mut sets = VecUnionFindSets::with_items(2);
    /// assert_eq!(sets.items_len(), 2);
    /// sets.unite(0, 1).unwrap();
    /// assert_eq!(sets.items_len(), 2);
    /// ```
    pub fn items_len(&self) -> usize {
        self.items.len()
    }

    fn find(&self, item: usize) -> Option<usize> {
        if item >= self.items_len() {
            return None;
        }

        fn go(sets: &VecUnionFindSets, item: usize) -> usize {
            let node = &sets.items[item];
            if node.parent.get() == item {
                return item;
            }

            let root = go(sets, node.parent.get());
            sets.items[root].parent.set(root);
            root
        }
        Some(go(self, item))
    }

    /// Returns how many sets `self` contains.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::collections::vec_union_find_sets::*;
    /// let mut sets = VecUnionFindSets::with_items(2);
    /// assert_eq!(sets.count(), 2);
    /// sets.unite(0, 1).unwrap();
    /// assert_eq!(sets.count(), 1);
    /// ```
    pub fn count(&self) -> usize {
        self.set_count
    }

    /// Returns how many items `self` contains by the set which has `item`.
    ///
    /// If no set contains `item`, returns `Err` with an error message.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::collections::vec_union_find_sets::*;
    /// let mut sets = VecUnionFindSets::with_items(2);
    ///
    /// assert_eq!(sets.len_of(0), Ok(1));
    /// sets.unite(0, 1).unwrap();
    /// assert_eq!(sets.len_of(0), Ok(2));
    ///
    /// assert!(sets.len_of(2).is_err());
    /// ```
    pub fn len_of(&self, item: usize) -> Result<usize, String> {
        self.find(item).map(|root| self.items[root].len).ok_or_else(|| {
            VecUnionFindSets::error_msg(&[item])
        })
    }

    /// Returns if two sets containing `item1` and `item2` are the same one.
    ///
    /// If no set contains `item1` or `item2`, returns `Err` with an error message.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::collections::vec_union_find_sets::*;
    /// let mut sets = VecUnionFindSets::with_items(2);
    ///
    /// assert_eq!(sets.set_eq(0, 1), Ok(false));
    /// sets.unite(0, 1);
    /// assert_eq!(sets.set_eq(0, 1), Ok(true));
    ///
    /// assert!(sets.set_eq(0, 2).is_err());
    /// assert!(sets.set_eq(2, 3).is_err());
    /// ```
    pub fn set_eq(&self, item1: usize, item2: usize) -> Result<bool, String> {
        match (self.find(item1), self.find(item2)) {
            (Some(root1), Some(root2)) => Ok(root1 == root2),
            (Some(_), None) => Err(VecUnionFindSets::error_msg(&[item2])),
            (None, Some(_)) => Err(VecUnionFindSets::error_msg(&[item1])),
            (None, None) => Err(VecUnionFindSets::error_msg(&[item1, item2])),
        }
    }

    /// Merges two sets, set containing `item1` and set containing `item2`.
    ///
    /// If the two sets are same (already merged ones), do nothing and returns `Ok(false)`.
    ///
    /// If no set contains `item1` or `item2`, returns `Err` with an error message.
    pub fn unite(&mut self, item1: usize, item2: usize) -> Result<bool, String> {
        match (self.find(item1), self.find(item2)) {
            (Some(root1), Some(root2)) => {
                if root1 == root2 {
                    return Ok(false);
                }

                self.set_count -= 1;
                let (new_root, new_child) = if self.items[root1].len < self.items[root2].len {
                    (root2, root1)
                } else {
                    (root1, root2)
                };
                let new_len = self.items[root1].len + self.items[root2].len;
                self.items[new_root] = VecUnionFindNode {
                    parent: std::cell::Cell::new(new_root),
                    len: new_len
                };
                self.items[new_child] = VecUnionFindNode {
                    parent: std::cell::Cell::new(new_root),
                    len: 0
                };
                Ok(true)
            },
            (Some(_), None) => Err(VecUnionFindSets::error_msg(&[item2])),
            (None, Some(_)) => Err(VecUnionFindSets::error_msg(&[item1])),
            (None, None) => Err(VecUnionFindSets::error_msg(&[item1, item2]))
        }
    }

    /// All sets as an iterator yielding `Vec<usize>`.
    ///
    /// Each set is sorted, but the order of sets is unspecified.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::collections::vec_union_find_sets::*;
    /// use std::collections::HashSet;
    ///
    /// let mut sets = VecUnionFindSets::with_items(6);
    /// sets.unite(0, 1).unwrap();
    /// sets.unite(2, 3).unwrap();
    /// sets.unite(3, 4).unwrap();
    ///
    /// let sets: HashSet<Vec<usize>> = sets.iter_cloned().collect();
    /// assert_eq!(sets.len(), 3);
    /// assert!(sets.contains(&vec![0, 1]));
    /// assert!(sets.contains(&vec![2, 3, 4]));
    /// assert!(sets.contains(&vec![5]));
    /// ```
    pub fn iter_cloned(&self) -> VecUnionFindSetsIter {
        let mut sets = vec![Vec::new(); self.items_len()];
        for i in 0..self.items_len() {
            let repr = self.find(i).unwrap();
            sets[repr].push(i);
        }
        sets.reverse();
        VecUnionFindSetsIter {
            sets: sets
        }
    }
}

pub struct VecUnionFindSetsIter {
    sets: Vec<Vec<usize>>,
}

impl Iterator for VecUnionFindSetsIter {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Vec<usize>> {
        while let Some(set) = self.sets.pop() {
            if !set.is_empty() {
                return Some(set)
            }
        }
        None
    }
}

impl std::fmt::Debug for VecUnionFindSets {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for set in self.iter_cloned() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", set)?;
            first = false;
        }
        write!(f, "}}")
    }
}

/*
impl<T: Eq + std::hash::Hash + std::fmt::Debug> IntoIterator for HashUnionFindSets<T> {
    type Item = HashSet<T>;
    type IntoIter = std::collections::hash_map::Values<>;

    fn into_iter(self) -> Self::IntoIter {
    }
}
*/

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_eq() {
        let mut sets = VecUnionFindSets::with_items(20);

        // unite in sequential order
        for i in 0..9 {
            sets.unite(i, i+1).unwrap();
        }

        for i in 0..10 {
            for j in 0..10 {
                assert!(sets.set_eq(i, j).unwrap());
            }
        }
        for i in 0..10 {
            for j in 10..20 {
                assert!(!sets.set_eq(i, j).unwrap());
            }
        }

        // unite in random order
        sets.unite(10, 11).unwrap();
        sets.unite(12, 13).unwrap();
        sets.unite(10, 12).unwrap();

        sets.unite(14, 15).unwrap();
        sets.unite(16, 17).unwrap();
        sets.unite(17, 18).unwrap();
        sets.unite(14, 17).unwrap();

        sets.unite(10, 14).unwrap();
        sets.unite(10, 19).unwrap();

        for i in 10..20 {
            for j in 10..20 {
                assert!(sets.set_eq(i, j).unwrap());
            }
        }
        for i in 0..10 {
            for j in 10..20 {
                assert!(!sets.set_eq(i, j).unwrap());
            }
        }
    }

    #[test]
    fn test_count() {
        let mut sets = VecUnionFindSets::new();
        assert_eq!(sets.count(), 0);

        sets.add_items(6);
        assert_eq!(sets.count(), 6);

        sets.unite(0, 1).unwrap();
        assert_eq!(sets.count(), 5);
        sets.unite(2, 3).unwrap();
        assert_eq!(sets.count(), 4);
        sets.unite(3, 4).unwrap();
        assert_eq!(sets.count(), 3);
        sets.unite(0, 2).unwrap();
        assert_eq!(sets.count(), 2);

        sets.unite(1, 3).unwrap();
        assert_eq!(sets.count(), 2);

        sets.add_items(3);
        assert_eq!(sets.count(), 5);
    }

    #[test]
    fn test_len_of() {
        let mut sets = VecUnionFindSets::with_items(6);
        assert_eq!(sets.len_of(0).unwrap(), 1);

        sets.unite(0, 1).unwrap();
        assert_eq!(sets.len_of(0).unwrap(), 2);

        sets.unite(2, 5).unwrap();
        sets.unite(3, 4).unwrap();
        sets.unite(2, 4).unwrap();
        assert_eq!(sets.len_of(3).unwrap(), 4);

        sets.unite(0, 5).unwrap();
        assert_eq!(sets.len_of(4).unwrap(), 6);
    }

    #[test]
    fn test_iter_cloned() {
        use std::collections::HashSet;
        fn get(sets: &VecUnionFindSets) -> HashSet<Vec<usize>> {
            sets.iter_cloned().collect()
        }

        let mut sets = VecUnionFindSets::with_items(10);
        sets.unite(0, 1).unwrap();
        sets.unite(3, 2).unwrap();
        sets.unite(3, 4).unwrap();
        sets.unite(5, 6).unwrap();
        sets.unite(6, 7).unwrap();
        sets.unite(7, 8).unwrap();
        let expected: HashSet<Vec<usize>> = vec![
            vec![0, 1],
            vec![2, 3, 4],
            vec![5, 6, 7, 8],
            vec![9]
        ].into_iter().collect();
        assert_eq!(get(&sets), expected);
    }
}
