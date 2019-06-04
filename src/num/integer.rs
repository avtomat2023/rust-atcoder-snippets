/// Having identity element for addition.
#[snippet = "num"]
pub trait WithZero: Sized + Eq +
    // Higher Ranked Trait Bound
    // https://stackoverflow.com/questions/34630695
    for<'a> std::ops::Add<&'a Self, Output=Self> +
    for<'a> std::ops::AddAssign<&'a Self>
{
    fn zero() -> Self;
}

/// Having identity element for multiplication.
#[snippet = "num"]
pub trait WithOne: Sized + Eq +
    for<'a> std::ops::Mul<&'a Self, Output=Self> +
    for<'a> std::ops::MulAssign<&'a Self>
{
    fn one() -> Self;
}

/// Integer supporting basic operations and constants.
#[snippet = "num"]
pub trait Integer: WithZero + WithOne + Ord +
    for<'a> std::ops::Sub<&'a Self, Output=Self> +
    for<'a> std::ops::SubAssign<&'a Self> +
    for<'a> std::ops::Div<&'a Self, Output=Self> +
    for<'a> std::ops::DivAssign<&'a Self>
{}
