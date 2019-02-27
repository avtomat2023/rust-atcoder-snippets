//! Utilities.

/// Prints "Yes" or "No" according to `result`.
#[snippet = "yn"]
pub fn yn(result: bool) {
    if result {
        println!("Yes");
    } else {
        println!("No");
    }
}

// ABC038 A, ABC038 B, ABC114 A
/// Prints "YES" or "NO" according to `result`.
#[snippet = "yn"]
#[allow(non_snake_case)]
pub fn YN(result: bool) {
    if result {
        println!("YES");
    } else {
        println!("NO");
    }
}

/// Make a debug output of the given expression to stderr.
///
/// Similar to `dbg` macro in Rust 1.32.0.
#[snippet = "dbg"]
#[macro_export]
macro_rules! dbg {
    ($e: expr) => {
        {
            use std::io::{self, Write};
            let result = $e;
            writeln!(io::stderr(), "{}: {} = {:?}",
                     line!(), stringify!($e), result)
                .unwrap();
            result
        }
    }
}
