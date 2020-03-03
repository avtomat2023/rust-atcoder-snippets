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

/// Number supporting basic operations and constants.
pub trait Numeric: WithZero + WithOne + PartialEq<Self> +
    for<'a> std::ops::Sub<&'a Self, Output=Self> +
    for<'a> std::ops::SubAssign<&'a Self> +
    for<'a> std::ops::Div<&'a Self, Output=Self> +
    for<'a> std::ops::DivAssign<&'a Self>
{}

/// Integer.
pub trait Integer: Numeric + Eq + Ord {}

/// Floating point number.
pub trait Float: Numeric {}

// END SNIPPET
