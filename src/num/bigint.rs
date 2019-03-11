// https://docs.rs/num-bigint/0.2.0/src/num_bigint/biguint.rs.html#43-45

use crate::num::BigDigit;
use crate::num::primitives::PrimitiveUnsigned;

pub struct BigUInt {
    data: Vec<BigDigit>
}

impl BigUInt {
    /// Creates a `BigUInt`.
    ///
    /// The digits are in little-endian base 2<sup>32</sup>.
    pub fn new<T: PrimitiveUnsigned>(num: T) -> BigUInt {
        BigUInt { data: num.to_le_big_digits() }
    }
}
