#[snippet = "read"]
trait FromFragment: Sized {
    fn from_fragment(s: &str) -> Result<Self, String>;
}

#[snippet = "read"]
impl FromFragment for String {
    fn from_fragment(s: &str) -> Result<String, String> { Ok(s.to_owned()) }
}

// impl FromFragment for bool

#[snippet = "read"]
#[allow(unused_macros)]
macro_rules! impl_from_fragment {
    ( $( $t:ty )* ) => { $(
        impl FromFragment for $t {
            fn from_fragment(s: &str) -> Result<$t, String> {
                use std::str::FromStr;
                <$t>::from_str(s).map_err(|_| {
                    format!("cannot parse \"{}\" as {}", s, stringify!($t))
                })
            }
        }
    )* };
}

#[snippet = "read"]
impl_from_fragment!(isize usize i8 u8 i16 u16 i32 u32 i64 u64 f64);

#[test]
fn test_from_fragemnt() {
    assert_eq!(i32::from_fragment("42"), Ok(42));
    assert_eq!(String::from_fragment("string"), Ok("string".to_owned()));
}

#[snippet = "read"]
trait FromLine: Sized {
    fn from_line(line: &str) -> Result<Self, String>;
}

#[snippet = "read"]
impl<T: FromFragment> FromLine for T {
    fn from_line(line: &str) -> Result<T, String> {
        T::from_fragment(line.trim_right_matches('\n'))
    }
}

#[snippet = "read"]
impl<T: FromFragment> FromLine for Vec<T> {
    fn from_line(line: &str) -> Result<Vec<T>, String> {
        let mut result = Vec::new();
        for fragment in line.trim_right_matches('\n').split_whitespace() {
            match T::from_fragment(fragment) {
                Ok(v) => result.push(v),
                Err(msg) => {
                    return Err(format!(
                        "fragment {} of line \"{}\": {}",
                        result.len() + 1, line, msg
                    ))
                }
            }
        }
        Ok(result)
    }
}

#[snippet = "read"]
#[allow(unused_macros)]
macro_rules! impl_from_line_for_tuples {
    ($t:ident $var:ident $count:expr) => ();
    ($t:ident $var:ident $count:expr; $($inner_t:ident $inner_var:ident $inner_count:expr);*) => {
        impl <$t: FromFragment, $($inner_t: FromFragment),*> FromLine for ($t, $($inner_t),*) {
            #[allow(unused_assignments)]
            fn from_line(line: &str) -> Result<( $t, $($inner_t),*), String> {
                let fragments: Vec<&str> =
                    line.trim_right_matches('\n').split_whitespace().collect();
                if fragments.len() != $count {
                    return Err(format!(
                        "line \"{}\" has {} fragments, expected {}",
                        line, fragments.len(), $count
                    ));
                }

                let mut iter = fragments.iter();
                let mut n = 1;
                let $var = <$t>::from_fragment(iter.next().unwrap())
                    .map_err(|msg| {
                        format!("fragment {} of line \"{}\": {}", n, line, msg)
                    })?;
                n += 1;
                $(
                    let $inner_var =
                        <$inner_t>::from_fragment(iter.next().unwrap())
                        .map_err(|msg| {
                            format!("fragment {} of line \"{}\": {}",
                                    n, line, msg)
                        })?;
                    n += 1;
                )*
                Ok(( $var, $($inner_var),* ))
            }
        }
        impl_from_line_for_tuples!($($inner_t $inner_var $inner_count);*);
    }
}

#[snippet = "read"]
impl_from_line_for_tuples!(T4 x4 4; T3 x3 3; T2 x2 2; T1 x1 1);

#[snippet = "read"]
#[allow(unused_macros)]
macro_rules! read {
    // Discard a line
    () => {
        let mut line = String::new();
        std::io::stdin().read_line(&mut line).unwrap();
    };

    // Get a FromLine
    ( $pat:pat = $t:ty ) => {
        let mut line = String::new();
        std::io::stdin().read_line(&mut line).unwrap();
        let $pat = <$t>::from_line(&line).unwrap();
    };

    // Get FromFragment's
    ( $( $pat:pat = $t:ty ),+ ) => {
        read!(($($pat),*) = ($($t),*));
    };
}

#[snippet = "read"]
#[allow(unused_macros)]
macro_rules! read_n {
    // Get FromLine's
    ( $( $pat:pat = $t:ty ),+ ) => {
        $(
            read!($pat = $t);
        )*
    }
}

/*
struct ReadIter<'a> {
    lock: StdinLock<'a>,
    f: FnMut
}

impl<T> Iterator<T> for


fn<T> read_iter() ->
*/

#[allow(unused_macros)]
macro_rules! read_iter {
    ( $pat:pat = $t:ty ) => {
        use std::io::BufRead;
        let stdin = std::io::stdin();
        stdin.lock().lines().map(|line| {
            let line = line.expect("read from stdin failed");
            let $pat = <$t>::from_line(&line).unwrap();
        })
    };
}

#[snippet = "read"]
#[allow(unused_macros)]
macro_rules! read_loop {
    ( $pat:pat = $t:ty; $block:block ) => {
        use std::io::BufRead;
        let stdin = std::io::stdin();
        for line in stdin.lock().lines() {
            let line = line.expect("read from stdin failed");
            let $pat = <$t>::from_line(&line).unwrap();
            $block
        }
    };

    ( $($pat:pat = $t:ty),* ; $block:block ) => {
        read_loop!(($($pat),*) = ($($t),*); $block);
    }
}

#[snippet = "read"]
#[allow(unused_macros)]
macro_rules! read_times_loop {
    ( $n:expr ; $pat:pat = $t:ty; $block:block ) => {
        use std::io::BufRead;
        let stdin = std::io::stdin();
        {
            let lock = stdin.lock();
            for _ in 0..$n {
                let line = String::new();
                lock.read_line(&mut line).expect("read from stdin failed");
                let $pat = <$t>::from_line(&line).unwrap();
                $block
            }
        }
    };

    ( $n:expr ; $($pat:pat = $t:ty),* ; $block:block ) => {
        read_times_loop!($n; ($($pat),*) = ($($t),*); $block);
    }
}
