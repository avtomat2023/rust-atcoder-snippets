//! Utilities.

/// Converts `result` into "Yes" or "No".
#[snippet = "yn"]
pub fn yn(result: bool) {
    if result {
        println!("Yes");
    } else {
        println!("No");
    }
}

// ABC038 A, ABC038 B, ABC114 A
/// Converts `result` into "YES" or "NO".
#[snippet = "yn"]
#[allow(non_snake_case)]
pub fn YN(result: bool) {
    if result {
        println!("YES");
    } else {
        println!("NO");
    }
}

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
