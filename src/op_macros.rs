// BEGIN SNIPPET op_macros

/// Implements the unary operator "op &T"
/// based on "op T" where T is expected to be `Copy`able.
///
/// Based on [https://doc.rust-lang.org/src/core/internal_macros.rs.html].
macro_rules! forward_ref_unop {
    (impl $op:ident, $method:ident for $t:ty) => {
        impl std::ops::$op for &$t {
            type Output = <$t as std::ops::$op>::Output;

            fn $method(self) -> <$t as std::ops::$op>::Output {
                std::ops::$op::$method(*self)
            }
        }
    }
}

/// Implements binary operators "&T op U", "T op &U", "&T op &U"
/// based on "T op U" where T and U are expected to be `Copy`able.
///
/// Based on [https://doc.rust-lang.org/src/core/internal_macros.rs.html].
macro_rules! forward_ref_binop {
    (impl $op:ident, $method:ident for $t:ty, $u:ty) => {
        impl<'a> std::ops::$op<$u> for &'a $t {
            type Output = <$t as std::ops::$op<$u>>::Output;

            fn $method(self, other: $u) -> <$t as std::ops::$op<$u>>::Output {
                std::ops::$op::$method(*self, other)
            }
        }

        impl std::ops::$op<&$u> for $t {
            type Output = <$t as std::ops::$op<$u>>::Output;

            fn $method(self, other: &$u) -> <$t as std::ops::$op<$u>>::Output {
                std::ops::$op::$method(self, *other)
            }
        }

        impl std::ops::$op<&$u> for &$t {
            type Output = <$t as std::ops::$op<$u>>::Output;

            fn $method(self, other: &$u) -> <$t as std::ops::$op<$u>>::Output {
                std::ops::$op::$method(*self, *other)
            }
        }
    }
}

/// Implements "T op= &U", based on "T op= U" where U is expected to be `Copy`able.
///
/// Based on [https://doc.rust-lang.org/src/core/internal_macros.rs.html].
macro_rules! forward_ref_op_assign {
    (impl $op:ident, $method:ident for $t:ty, $u:ty) => {
        impl std::ops::$op<&$u> for $t {
            fn $method(&mut self, other: &$u) {
                std::ops::$op::$method(self, *other);
            }
        }
    }
}

// END SNIPPET
