#[snippet = "write"]
#[allow(unused_imports)]
use std::io::{self, Write, BufWriter, StdoutLock};

#[snippet = "write"]
pub fn with_stdout<F: FnOnce(BufWriter<StdoutLock>)>(f: F) {
    let stdout = io::stdout();
    let writer = BufWriter::new(stdout.lock());
    f(writer);
}
