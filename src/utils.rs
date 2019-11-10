//! Utilities.

// BEGIN SNIPPET yn

/// Prints "Yes" or "No" according to `result`.
pub fn yn(result: bool) {
    if result {
        println!("Yes");
    } else {
        println!("No");
    }
}

// ABC038 A, ABC038 B, ABC114 A
/// Prints "YES" or "NO" according to `result`.
#[allow(non_snake_case)]
pub fn YN(result: bool) {
    if result {
        println!("YES");
    } else {
        println!("NO");
    }
}

// END SNIPPET

// BEGIN SNIPPET dbg

/// Make a debug output of the given expression to stderr.
///
/// The output is made only in the local machine, not in the judge server.
///
/// Similar to `dbg` macro in Rust 1.32.0.
#[macro_export]
#[cfg(local)]
macro_rules! dbg {
    () => {
        {
            use std::io::{self, Write};
            writeln!(io::stderr(), "{}: dbg", line!()).unwrap();
        }
    };

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

/// Make a debug output of the given expression to stderr.
///
/// The output is made only in the local machine, not in the judge server.
///
/// Similar to `dbg` macro in Rust 1.32.0.
#[macro_export]
#[cfg(not(local))]
macro_rules! dbg {
    () => {};
    ($e: expr) => { $e }
}

// END SNIPPET
