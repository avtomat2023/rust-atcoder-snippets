//! Output to stdout.

#[snippet = "write"]
#[allow(unused_imports)]
use std::io::{self, Write, BufWriter, StdoutLock};

// TODO: Add a real example (maybe in marathon match)
/// Make tons of output to stdout much faster.
///
/// See [Qiita article by hatoo](https://qiita.com/hatoo@github/items/fa14ad36a1b568d14f3e#%E3%81%8A%E3%81%BE%E3%81%91).
#[snippet = "write"]
pub fn with_stdout<F: FnOnce(BufWriter<StdoutLock>)>(f: F) {
    let stdout = io::stdout();
    let writer = BufWriter::new(stdout.lock());
    f(writer);
}
