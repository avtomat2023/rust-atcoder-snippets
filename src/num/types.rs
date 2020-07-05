// BEGIN SNIPPET num_types

/// Having identity element for addition.
pub trait WithZero: Sized +
    // Higher Ranked Trait Bound
    // https://stackoverflow.com/questions/34630695
    for<'a> std::ops::Add<&'a Self, Output=Self> +
    for<'a> std::ops::AddAssign<&'a Self>
{
    fn zero() -> Self;
}

/// Having identity element for multiplication.
pub trait WithOne: Sized +
    for<'a> std::ops::Mul<&'a Self, Output=Self> +
    for<'a> std::ops::MulAssign<&'a Self>
{
    fn one() -> Self;
}

/// Equipped with basic integer operations.
pub trait Integer: Eq + Ord + WithZero + WithOne +
    for<'a> std::ops::Sub<&'a Self, Output=Self> +
    for<'a> std::ops::SubAssign<&'a Self> +
    for<'a> std::ops::Div<&'a Self, Output=Self> +
    for<'a> std::ops::DivAssign<&'a Self> +
    for<'a> std::ops::Rem<&'a Self, Output=Self> +
    for<'a> std::ops::RemAssign<&'a Self>
{}

/// Convertible to the signed type.
pub trait ToSigned {
    /// Signed counterpart of the implementing type.
    type Signed: Integer;

    /// Converts to signed type.
    ///
    /// If the converted value is out of range of the signed type, returns `None`.
    fn to_signed(&self) -> Option<Self::Signed>;

    /// Converts to signed type without bound check.
    unsafe fn to_signed_unchecked(&self) -> Self::Signed {
        self.to_signed().unwrap()
    }
}

/// Convertible to the unsgined type.
pub trait ToUnsigned {
    /// Unsigned counterpart of the implementing type.
    type Unsigned: Integer;

    /// Converts to unsigned type.
    ///
    /// If the converted value is out of range of the unsigned type, returns `None`.
    fn to_unsigned(&self) -> Option<Self::Unsigned>;

    /// Converts to unsigned type without bound check.
    unsafe fn to_unsigned_unchecked(&self) -> Self::Unsigned {
        self.to_unsigned().unwrap()
    }
}

// END SNIPPET
