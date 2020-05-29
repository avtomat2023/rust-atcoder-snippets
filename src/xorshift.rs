//! Xorshift random number generator.

// BEGIN SNIPPET xorshift

/// Random number generator by xorshift.
///
/// # Example
///
/// ```
/// # use atcoder_snippets::xorshift::*;
/// let mut rng = Xorshift::new();
/// let random_i32: i32 = rng.next();
/// let random_f64: f64 = rng.next();
/// assert!(0.0 <= random_f64 && random_f64 < 1.0);
/// ```
pub struct Xorshift {
    state: u64
}

impl Xorshift {
    /// Random number generator seeded by system clock.
    pub fn new() -> Xorshift {
        use std::time::SystemTime;
        let now = SystemTime::now();
        let epoch = now.duration_since(SystemTime::UNIX_EPOCH).unwrap();
        Xorshift { state: epoch.as_secs() ^ epoch.subsec_nanos() as u64 }
    }

    /// Random number generator with seed.
    pub fn with_seed(seed: u64) -> Xorshift {
        let seed = if seed == 0 { 1 } else { seed };
        Xorshift { state: seed }
    }

    /// Gets a random number.
    pub fn next<T: RngOutput>(&mut self) -> T {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 7;
        self.state ^= self.state << 17;
        T::from_u64(self.state)
    }

    /// Shuffles the slice.
    pub fn shuffle<T>(&mut self, slice: &mut [T]) {
        for i in 1..slice.len() {
            let j = self.next::<usize>() % (i+1);
            slice.swap(i, j);
        }
    }
}

pub trait RngOutput {
    fn from_u64(x: u64) -> Self;
}

impl RngOutput for i8 {
    fn from_u64(x: u64) -> i8 {
        x as i8
    }
}

impl RngOutput for u8 {
    fn from_u64(x: u64) -> u8 {
        x as u8
    }
}

impl RngOutput for i16 {
    fn from_u64(x: u64) -> i16 {
        x as i16
    }
}

impl RngOutput for u16 {
    fn from_u64(x: u64) -> u16 {
        x as u16
    }
}

impl RngOutput for i32 {
    fn from_u64(x: u64) -> i32 {
        x as i32
    }
}

impl RngOutput for u32 {
    fn from_u64(x: u64) -> u32 {
        x as u32
    }
}

impl RngOutput for i64 {
    fn from_u64(x: u64) -> i64 {
        x as i64
    }
}

impl RngOutput for u64 {
    fn from_u64(x: u64) -> u64 {
        x
    }
}

impl RngOutput for isize {
    fn from_u64(x: u64) -> isize {
        x as isize
    }
}

impl RngOutput for usize {
    fn from_u64(x: u64) -> usize {
        x as usize
    }
}

impl RngOutput for f32 {
    fn from_u64(x: u64) -> f32 {
        (unsafe { std::mem::transmute::<u32, f32>(x as u32 & 0x007FFFFF | 0x3F800000) }) - 1.0
    }
}

impl RngOutput for f64 {
    fn from_u64(x: u64) -> f64 {
        (unsafe { std::mem::transmute::<u64, f64>(x & 0x000FFFFFFFFFFFFF | 0x3FF0000000000000) }) - 1.0
    }
}

// END SNIPPET
