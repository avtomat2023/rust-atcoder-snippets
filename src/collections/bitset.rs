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

use std;

// BEGIN SNIPPET bitset

const BITSET_TRUE: &'static bool = &true;
const BITSET_FALSE: &'static bool = &false;

/// Efficient boolean vector
#[derive(Clone, Debug)]
pub struct BitSet {
    buf: Vec<u64>,
    size: usize,
}

impl BitSet {
    pub fn new(size: usize) -> BitSet {
        BitSet {
            buf: vec![0; (size + 63) / 64],
            size: size,
        }
    }

    pub fn get(&mut self, i: usize) -> Option<bool> {
        if i <= self.size {
            Some(self.buf[i >> 6] & 1 << (i & 63) != 0)
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, i: usize) -> Option<BitSetRef> {
        self.get(i).map(move |b| BitSetRef {
            bitset: self,
            value: b,
            index: i
        })
    }

    pub fn at(&mut self, i: usize) -> BitSetRef {
        self.get_mut(i).unwrap()
    }

    pub fn count_ones(&self) -> u32 {
        self.buf.iter().map(|x| x.count_ones()).sum()
    }

    fn chomp(&mut self) {
        let r = self.size & 63;
        if r != 0 {
            if let Some(x) = self.buf.last_mut() {
                let d = 64 - r;
                *x = (*x << d) >> d;
            }
        }
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
}
