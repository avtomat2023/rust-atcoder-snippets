//! Efficient boolean vector.
//!
//! Implementation is based on [hatoo's BitSet](https://github.com/hatoo/competitive-rust-snippets/blob/master/src/bitset.rs).

// MIT License
//
// Copyright (c) 2018 hatoo
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use crate::num::PrimitiveUnsigned;

// BEGIN SNIPPET bitset DEPENDS ON int

const BITSET_TRUE: &'static bool = &true;
const BITSET_FALSE: &'static bool = &false;

/// Efficient boolean vector
#[derive(Clone)]
pub struct BitSet {
    // 64-bit chunks ordered lowest chunk first and high chunk last
    buf: Vec<u64>,
    bit_len: usize
}

impl BitSet {
    /// Creates a bitset of the specified bit length.
    pub fn new(bit_len: usize) -> BitSet {
        BitSet {
            buf: vec![0; bit_len.ceil_div(64)],
            bit_len,
        }
    }

    /// Gets bit length.
    pub fn len(&self) -> usize {
        self.bit_len
    }

    /// Gets `i`-th bit.
    ///
    /// If `i` is out of range, returns `None`.
    pub fn get(&self, i: usize) -> Option<bool> {
        if i <= self.len() {
            Some(unsafe { self.get_unchecked(i) })
        } else {
            None
        }
    }

    /// Gets `i`-th bit without bound checking.
    ///
    /// Maybe causes undefined behavior if `i` is out of range,
    pub unsafe fn get_unchecked(&self, i: usize) -> bool {
        *self.buf.get_unchecked(i / 64) & (1 << (i % 64)) != 0
    }

    /// Gets `i`-th bit as a mutable boolean.
    ///
    /// If `i` is out of range, returns `None`.
    pub fn get_mut(&mut self, i: usize) -> Option<BitSetRef> {
        self.get(i).map(move |b| BitSetRef {
            bitset: self,
            value: b,
            index: i
        })
    }

    /// Panicking `get_mut`.
    ///
    /// # Panic
    ///
    /// If `i` is out of range, it panics.
    pub fn at(&mut self, i: usize) -> BitSetRef {
        let len = self.len();
        self.get_mut(i).unwrap_or_else(|| {
            panic!("index out of bounds: the bit-length is {} but index is {}",
                   len, i)
        })
    }

    /// Counts how many bits are sets.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::collections::bitset::*;
    /// let mut set = BitSet::new(256);
    /// *set.at(0) = true;
    /// *set.at(128) = true;
    /// assert_eq!(set.count_ones(), 2)
    /// ```
    pub fn count_ones(&self) -> u32 {
        self.buf.iter().map(|x| x.count_ones()).sum()
    }

    /// Gets an iterator from the lowest bit to the highest, yielding `bool`s.
    ///
    /// # Example
    ///
    /// ```
    /// # use atcoder_snippets::collections::bitset::*;
    /// let mut set = BitSet::new(4);
    /// *set.at(0) = true;
    ///
    /// let bits: Vec<bool> = set.iter().collect();
    /// assert_eq!(bits, vec![true, false, false, false]);
    ///
    /// // The iterator is reversible.
    /// let rev_bits: Vec<bool> = set.iter().rev().collect();
    /// assert_eq!(rev_bits, vec![false, false, false, true]);
    /// ```
    pub fn iter(&self) -> BitSetIter {
        BitSetIter {
            bitset: self,
            range: 0..self.len()
        }
    }

    fn chomp(&mut self) {
        let r = self.len() % 64;
        if r != 0 {
            if let Some(x) = self.buf.last_mut() {
                let d = 64 - r;
                *x = (*x << d) >> d;
            }
        }
    }
}

impl std::fmt::Debug for BitSet {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for i in 0 .. self.len().ceil_div(64) {
            let bits_msb_to_lsb = format!("{:064b}", self.buf[i]);
            let mut bits_lsb_to_msb: Vec<char> = bits_msb_to_lsb.chars().collect();
            bits_lsb_to_msb.reverse();
            if i == self.len() / 64 {
                bits_lsb_to_msb.truncate(self.len() % 64);
            }
            for ch in bits_lsb_to_msb {
                write!(f, "{}", ch)?;
            }
        }
        Ok(())
    }
}

impl std::ops::Index<usize> for BitSet {
    type Output = bool;
    fn index(&self, index: usize) -> &bool {
        [BITSET_FALSE, BITSET_TRUE][(self.buf[index >> 6] >> (index & 63)) as usize & 1]
    }
}

pub struct BitSetRef<'a> {
    bitset: &'a mut BitSet,
    value: bool,
    index: usize
}

impl std::ops::Deref for BitSetRef<'_> {
    type Target = bool;

    fn deref(&self) -> &bool {
        &self.value
    }
}

impl std::ops::DerefMut for BitSetRef<'_> {
    fn deref_mut(&mut self) -> &mut bool {
        &mut self.value
    }
}

impl Drop for BitSetRef<'_> {
    fn drop(&mut self) {
        if self.value {
            self.bitset.buf[self.index >> 6] |= 1 << (self.index & 63);
        } else {
            self.bitset.buf[self.index >> 6] &= !(1 << (self.index & 63));
        }
    }
}

pub struct BitSetIter<'a> {
    bitset: &'a BitSet,
    range: std::ops::Range<usize>
}

impl Iterator for BitSetIter<'_> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        self.range.next().map(|i| unsafe { self.bitset.get_unchecked(i) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }

    fn count(self) -> usize {
        self.range.count()
    }

    fn last(mut self) -> Option<bool> {
        self.range.next_back().map(|i| unsafe { self.bitset.get_unchecked(i) })
    }

    fn nth(&mut self, n: usize) -> Option<bool> {
        self.range.nth(n).map(|i| unsafe { self.bitset.get_unchecked(i) })
    }
}

impl DoubleEndedIterator for BitSetIter<'_> {
    fn next_back(&mut self) -> Option<bool> {
        self.range.next_back().map(|i| unsafe { self.bitset.get_unchecked(i) } )
    }

    fn nth_back(&mut self, n: usize) -> Option<bool> {
        self.range.nth_back(n).map(|i| unsafe { self.bitset.get_unchecked(i) } )
    }
}

impl ExactSizeIterator for BitSetIter<'_> {}

impl std::iter::FusedIterator for BitSetIter<'_> {}

impl<'a> IntoIterator for &'a BitSet {
    type Item = bool;
    type IntoIter = BitSetIter<'a>;

    fn into_iter(self) -> BitSetIter<'a> {
        self.iter()
    }
}

impl std::ops::ShlAssign<usize> for BitSet {
    fn shl_assign(&mut self, x: usize) {
        let q = x >> 6;
        let r = x & 63;

        if q >= self.buf.len() {
            for x in &mut self.buf {
                *x = 0;
            }
            return;
        }

        if r == 0 {
            for i in (q..self.buf.len()).rev() {
                self.buf[i] = self.buf[i - q];
            }
        } else {
            for i in (q + 1..self.buf.len()).rev() {
                self.buf[i] = (self.buf[i - q] << r) | (self.buf[i - q - 1] >> (64 - r));
            }
            self.buf[q] = self.buf[0] << r;
        }

        for x in &mut self.buf[..q] {
            *x = 0;
        }

        self.chomp();
    }
}

impl std::ops::Shl<usize> for BitSet {
    type Output = Self;

    fn shl(mut self, x: usize) -> Self {
        self <<= x;
        self
    }
}

impl std::ops::ShrAssign<usize> for BitSet {
    fn shr_assign(&mut self, x: usize) {
        let q = x >> 6;
        let r = x & 63;

        if q >= self.buf.len() {
            for x in &mut self.buf {
                *x = 0;
            }
            return;
        }

        if r == 0 {
            for i in 0..self.buf.len() - q {
                self.buf[i] = self.buf[i + q];
            }
        } else {
            for i in 0..self.buf.len() - q - 1 {
                self.buf[i] = (self.buf[i + q] >> r) | (self.buf[i + q + 1] << (64 - r));
            }
            let len = self.buf.len();
            self.buf[len - q - 1] = self.buf[len - 1] >> r;
        }

        let len = self.buf.len();
        for x in &mut self.buf[len - q..] {
            *x = 0;
        }
    }
}

impl std::ops::Shr<usize> for BitSet {
    type Output = Self;

    fn shr(mut self, x: usize) -> Self {
        self >>= x;
        self
    }
}

impl<'a> std::ops::BitAndAssign<&'a BitSet> for BitSet {
    fn bitand_assign(&mut self, rhs: &'a Self) {
        for (a, b) in self.buf.iter_mut().zip(rhs.buf.iter()) {
            *a &= *b;
        }
    }
}

impl<'a> std::ops::BitAnd<&'a BitSet> for BitSet {
    type Output = Self;
    fn bitand(mut self, rhs: &'a Self) -> Self {
        self &= rhs;
        self
    }
}

impl<'a> std::ops::BitOrAssign<&'a BitSet> for BitSet {
    fn bitor_assign(&mut self, rhs: &'a Self) {
        for (a, b) in self.buf.iter_mut().zip(rhs.buf.iter()) {
            *a |= *b;
        }
        self.chomp();
    }
}

impl<'a> std::ops::BitOr<&'a BitSet> for BitSet {
    type Output = Self;
    fn bitor(mut self, rhs: &'a Self) -> Self {
        self |= rhs;
        self
    }
}

impl<'a> std::ops::BitXorAssign<&'a BitSet> for BitSet {
    fn bitxor_assign(&mut self, rhs: &'a Self) {
        for (a, b) in self.buf.iter_mut().zip(rhs.buf.iter()) {
            *a ^= *b;
        }
        self.chomp();
    }
}

impl<'a> std::ops::BitXor<&'a BitSet> for BitSet {
    type Output = Self;
    fn bitxor(mut self, rhs: &'a Self) -> Self {
        self ^= rhs;
        self
    }
}

// END SNIPPET

#[cfg(test)]
mod tests {
    extern crate rand;
    use self::rand::prelude::*;
    use super::*;

    #[test]
    fn test_bitset_set_read() {
        let size = 6400;
        let mut set = BitSet::new(size);
        let mut v = vec![false; size];

        for i in 0..size {
            let b = random::<u32>() % 2 == 0;
            *set.at(i) = b;
            v[i] = b;
        }

        for i in 0..size {
            assert_eq!(set[i], v[i]);
        }
    }

    #[test]
    fn test_bitset_shl() {
        let do_test = |size, shift| {
            let mut set = BitSet::new(size);
            let mut v = vec![false; size];

            for i in 0..size {
                let b = random::<u32>() % 2 == 0;
                *set.at(i) = b;
                v[i] = b;
            }
            for i in (shift..v.len()).rev() {
                v[i] = v[i - shift];
            }
            for i in 0..std::cmp::min(size, shift) {
                v[i] = false;
            }

            set <<= shift;
            for i in 0..size {
                assert_eq!(set[i], v[i]);
            }
        };

        do_test(6400, 640);
        do_test(6400, 114);
        do_test(6400, 514);
        do_test(6400, 6400);
        do_test(6400, 16400);

        let mut t = BitSet::new(310);

        for i in 0..31000 {
            t <<= i;
        }
    }

    #[test]
    fn test_bitset_shr() {
        let do_test = |size, shift| {
            let mut set = BitSet::new(size);
            let mut v = vec![false; size];

            for i in 0..size {
                let b = random::<u32>() % 2 == 0;
                *set.at(i) = b;
                v[i] = b;
            }

            let s = if size >= shift { size - shift } else { 0 };

            for i in 0..s {
                v[i] = v[i + shift];
            }

            for i in s..size {
                v[i] = false;
            }

            set >>= shift;
            for i in 0..size {
                assert_eq!(set[i], v[i]);
            }
        };

        do_test(6400, 640);
        do_test(6400, 114);
        do_test(6400, 514);
        do_test(63, 65);
        do_test(6400, 6400);
        do_test(6400, 16400);

        let mut t = BitSet::new(310);

        for i in 0..31000 {
            t >>= i;
        }
    }

    #[test]
    fn test_bitset_chomp() {
        let mut set1 = BitSet::new(4);
        let mut set2 = BitSet::new(8);

        for i in 0..4 {
            *set1.at(i) = true;
            *set2.at(i) = true;
        }

        for i in 4..8 {
            *set2.at(i) = true;
        }

        set1 <<= 2;
        assert_eq!(set1.count_ones(), 2);
        assert_eq!((set1.clone() | &set2).count_ones(), 4);
        assert_eq!((set1.clone() & &set2).count_ones(), 2);
        assert_eq!((set1.clone() ^ &set2).count_ones(), 2);
    }

    #[test]
    fn test_bits_len() {
        let set = BitSet::new(0);
        assert_eq!(set.iter().len(), 0);

        let set = BitSet::new(1);
        assert_eq!(set.iter().len(), 1);

        let set = BitSet::new(100);
        assert_eq!(set.iter().len(), 100);
    }
}
