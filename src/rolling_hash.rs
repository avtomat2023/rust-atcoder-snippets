/// Rolling hash for efficient string matching.
// Example: ABC135 F

use crate::iter::IteratorExt;

// BEGIN SNIPPET rolling_hash DEPENDS ON iter

/// Unsigned integer type for rolling hash.
pub type RollingHashBase = u64;

mod rolling_hash_internal {
    use super::RollingHashBase;

    // Prime numbers less than 2^32
    pub const ROLL: RollingHashBase = 1154491469;
    pub const MOD: RollingHashBase = 4290357497;

    pub fn pow(base: RollingHashBase, exp: RollingHashBase) -> RollingHashBase {
        if exp == 0 { 1 } else {
            let pow_half = pow(base, exp/2);
            if exp % 2 == 0 {
                (pow_half * pow_half) % MOD
            } else {
                (base * pow_half % MOD) * pow_half % MOD
            }
        }
    }
}

/// A rolling-hashable sequence.
pub trait RollingHash {
    fn rolling_hash(&self) -> RollingHashValue<Self>;
    fn prefix_rolling_hash(&self) -> PrefixRollingHash<Self>;
}

impl RollingHash for [u8] {
    fn rolling_hash(&self) -> RollingHashValue<[u8]> {
        use self::rolling_hash_internal::*;

        let value = self.iter().fold(0u64, |acc, &next| {
            (acc * ROLL + next as RollingHashBase) % MOD
        });
        RollingHashValue {
            len: self.len(),
            value: value,
            seq_type: std::marker::PhantomData
        }
    }

    fn prefix_rolling_hash(&self) -> PrefixRollingHash<[u8]> {
        use self::rolling_hash_internal::*;

        let prefix_hash = self.iter().lscan(0 as RollingHashBase, |&acc, &next| {
            (acc * ROLL + next as RollingHashBase) % MOD
        }).collect() ;
        PrefixRollingHash {
            prefix_hash: prefix_hash,
            seq_type: std::marker::PhantomData
        }
    }
}

/// A rolling hash of a sequence.
pub struct RollingHashValue<T: ?Sized + RollingHash> {
    len: usize,
    value: RollingHashBase,
    seq_type: std::marker::PhantomData<T>
}

// Cannot derive for unsized `T`.
impl<T: ?Sized + RollingHash> Clone for RollingHashValue<T> {
    fn clone(&self) -> Self {
        RollingHashValue {
            len: self.len,
            value: self.value,
            seq_type: self.seq_type.clone()
        }
    }
}

// Cannot derive for unsized `T`.
impl<T: ?Sized + RollingHash> Copy for RollingHashValue<T> {}

impl<T: ?Sized + RollingHash> RollingHashValue<T> {
    /// Length of the original sequence.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Rolling hash value.
    pub fn value(&self) -> RollingHashBase {
        self.value
    }
}

/// Sliding rolling hashes of a sequence.
pub struct PrefixRollingHash<T: ?Sized + RollingHash> {
    prefix_hash: Vec<RollingHashBase>,
    seq_type: std::marker::PhantomData<T>
}

impl<T: ?Sized + RollingHash> PrefixRollingHash<T> {
    /// Length of original sequence.
    pub fn len(&self) -> usize {
        self.prefix_hash.len() - 1
    }

    /// Checks if the subsequence starting from `index` matches `pattern`.
    ///
    /// If the subsequence starting from `index` with the same length of `pattern`
    /// exceeds the range of the original sequence, returns `None`.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::rolling_hash::*;
    /// let haystack = [0, 1, 2].prefix_rolling_hash();
    /// let needle = [1, 2].rolling_hash();
    /// assert_eq!(haystack.matches_at(needle, 0), Some(false));
    /// assert_eq!(haystack.matches_at(needle, 1), Some(true));
    /// assert_eq!(haystack.matches_at(needle, 2), None);
    /// ```
    pub fn matches_at(&self, pattern: RollingHashValue<T>, index: usize) -> Option<bool> {
        use self::rolling_hash_internal::*;

        let hash_right = match self.prefix_hash.get(index + pattern.len()) {
            Some(&hash) => hash,
            None => return None
        };
        // Length of `self.prefix_hash` is longer than `index + pattern.len()`,
        // so the indexing never panics.
        let hash_left = self.prefix_hash[index];

        let m = pow(ROLL, pattern.len() as RollingHashBase);
        Some((hash_right + MOD - (hash_left * m % MOD)) % MOD == pattern.value())
    }

    /// Returns an iterator yielding all indices matching `pattern`.
    ///
    /// Matching is performed from left to right,
    /// so yielded indices are strictly increasing.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate atcoder_snippets;
    /// # use atcoder_snippets::rolling_hash::*;
    /// let haystack = [1, 2, 3, 1, 2].prefix_rolling_hash();
    /// let needle = [1, 2].rolling_hash();
    /// let matches: Vec<usize> = haystack.matches(needle).collect();
    /// assert_eq!(matches, vec![0, 3]);
    /// ```
    // `pattern`を`&T`型にするインターフェースも考えられるが、
    // ローリングハッシュを計算するθ(n)のコストをユーザーに意識させたいので、
    // `RollingHashValue<T>`を取るようにした。
    pub fn matches<'a>(&'a self, pattern: RollingHashValue<T>) ->
        RollingHashMatches<'a, T>
    {
        use self::rolling_hash_internal::*;

        RollingHashMatches {
            prefix_hash: self,
            pattern: pattern,
            m: pow(ROLL, pattern.len() as RollingHashBase),
            index: 0
        }
    }
}

pub struct RollingHashMatches<'a, T: 'a + ?Sized + RollingHash> {
    prefix_hash: &'a PrefixRollingHash<T>,
    pattern: RollingHashValue<T>,
    m: RollingHashBase,
    index: usize,
}

impl<'a, T: ?Sized + RollingHash> Iterator for RollingHashMatches<'a, T> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        use self::rolling_hash_internal::*;

        let prefix = &self.prefix_hash.prefix_hash;

        while let Some(hash_right) = prefix.get(self.index + self.pattern.len()) {
            let old_index = self.index;
            self.index += 1;

            let hash_left = prefix[old_index];
            let hash = (hash_right + MOD - (hash_left * self.m % MOD)) % MOD;
            if hash == self.pattern.value() {
                return Some(old_index)
            }
        }

        None
    }
}

// END SNIPPET

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_matches_at() {
        let haystack = [1, 1, 2, 1, 1, 1, 2, 1, 2].prefix_rolling_hash();
        let needle = [1, 1].rolling_hash();
        let results: Vec<Option<bool>> = (0..haystack.len())
            .map(|i| haystack.matches_at(needle, i))
            .collect();
        let t = Some(true);
        let f = Some(false);
        assert_eq!(results, vec![t, f, f, t, t, f, f, f, None]);
    }

    #[test]
    fn test_matches() {
        let haystack = [1, 1, 2, 1, 1, 1, 2, 1, 2].prefix_rolling_hash();
        let needle = [1, 1].rolling_hash();
        let matches: Vec<usize> = haystack.matches(needle).collect();
        assert_eq!(matches, vec![0, 3, 4]);
    }
}
