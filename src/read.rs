//! スペース区切りの入力を簡単に読み込むためのマクロを提供する。
//!
//! Rustで競技プログラミングを戦うための最初の関門が、入力の読み込みである。
//! 標準入力から数値を読み込むには、以下のコードを書く必要がある。
//!
//! ```no_run
//! use std::io;
//!
//! let mut line = String::new();
//! io::stdin().read_line(&mut line).unwrap();
//! // 末尾の改行文字を除去する
//! let line = line.trim_right();
//! let n = line.parse::<i32>();
//! ```
//!
//! 空白で区切られた複数の数値を読み込む処理はさらに複雑である。
//! このようなボイラープレートを問題ごとに記述するのは現実的でないため、
//! このモジュールの提供するマクロを用いて入力読み込みを省力化するのが賢明である。
//!
//! # Examples
//!
//! 上に挙げた処理は、以下のように記述できる。
//!
//! ```no_run
//! # #[macro_use] extern crate atcoder_snippets;
//! # use atcoder_snippets::read::*;
//! #
//! read!(n = i32);
//! ```
//!
//! この記述により、読み込んだ`i32`型の数値が、immutable変数`n`に束縛される。
//!
//! 複数の数値を読み込むこともできる。
//!
//! ```no_run
//! # #[macro_use] extern crate atcoder_snippets;
//! # use atcoder_snippets::read::*;
//! #
//! read!(n = usize, k = u64);
//! ```
//!
//! 変数をmutableにすることもできる。
//!
//! ```no_run
//! # #[macro_use] extern crate atcoder_snippets;
//! # use atcoder_snippets::read::*;
//! #
//! read!(mut n = usize);
//! ```
//!
//! `=`記号の右に書くことで読み込むことのできる型は、以下の通りである。
//!
//! - `f32`を除く数値型(`isize`, `usize`, `i8`, `u8`, `i16`, `u16`, `i32`, `u32`, `i64`, `u64`, `f64`)
//! - `String`
//!
//! また、`read!`の中の「*変数* `=` *型*」の並びがひとつだけの場合、上記の型のタプルや`Vec`を読み込むことができる。
//!
//! ```no_run
//! # #[macro_use] extern crate atcoder_snippets;
//! # use atcoder_snippets::read::*;
//! #
//! // 入力例："Alice Bob 1"
//! read!(pair_and_cost = (String, String, u32));
//! ```
//!
//! ```no_run
//! # #[macro_use] extern crate atcoder_snippets;
//! # use atcoder_snippets::read::*;
//! #
//! // 入力例："1 17 8 3 2 6"
//! read!(mut ns = Vec<usize>);
//! ```
//!
//! 読み込みに失敗した場合、エラーメッセージが表示されてpanicする。
//!
//! ```no_run
//! # #[macro_use] extern crate atcoder_snippets;
//! # use atcoder_snippets::read::*;
//! #
//! // 入力例："1 2 3.45"
//! read!(a = i32, b = i32, x = i32);
//! // thread 'main' panicked at 'called `Result::unwrap()` on an `Err` value: "fragment 3 of line \"1 2 3.45\n\": cannot parse \"3.45\" as i32"'
//! ```
//!
//! # Examples
//!
//! Solves [PracticeA - Welcome to AtCoder](https://abs.contest.atcoder.jp/tasks/practice_1).
//!
//! ```no_run
//! # #[macro_use] extern crate atcoder_snippets;
//! # use atcoder_snippets::read::*;
//! #
//! fn main() {
//!     read!(a = u16);
//!     read!(b = u16, c = u16);
//!     read!(s = String);
//!     println!("{} {}", a+b+c, s);
//! }
//! ```

#[snippet = "read"]
pub trait FromFragments: Sized {
    fn fragments_count() -> usize;
    fn from_fragments(fragments: &[&str]) -> Result<Self, String>;
}

#[snippet = "read"]
impl FromFragments for String {
    fn fragments_count() -> usize { 1 }
    fn from_fragments(fragments: &[&str]) -> Result<String, String> {
        Ok(fragments[0].to_string())
    }
}

// impl FromFragment for bool

#[snippet = "read"]
macro_rules! impl_from_fragments {
    ( $( $t:ty )* ) => { $(
        impl FromFragments for $t {
            fn fragments_count() -> usize { 1 }
            fn from_fragments(fragments: &[&str]) -> Result<$t, String> {
                use std::str::FromStr;
                <$t>::from_str(fragments[0]).map_err(|_| {
                    format!("cannot parse \"{}\" as {}", fragments[0], stringify!($t))
                })
            }
        }
    )* };
}

#[snippet = "read"]
impl_from_fragments!(isize usize i8 u8 i16 u16 i32 u32 i64 u64 f32 f64);

#[snippet = "read"]
pub trait FromLine: Sized {
    fn from_line(line: &str) -> Result<Self, String>;
}

#[snippet = "read"]
fn split_into_fragments(line: &str) -> Vec<&str> {
    line.trim_right_matches('\n').split_whitespace().collect()
}

#[snippet = "read"]
impl<T: FromFragments> FromLine for T {
    fn from_line(line: &str) -> Result<T, String> {
        let fragments = split_into_fragments(line);
        if fragments.len() != T::fragments_count() {
            return Err(format!("line \"{}\" has {} fragments, expected {}",
                               line, fragments.len(), T::fragments_count()));
        }

        T::from_fragments(&fragments)
    }
}

/// Reads arbitrary number of `T`s.
#[snippet = "read"]
impl<T: FromFragments> FromLine for Vec<T> {
    fn from_line(line: &str) -> Result<Vec<T>, String> {
        let n = T::fragments_count();
        let fragments = split_into_fragments(line);
        if fragments.len() % n != 0 {
            return Err(format!("line \"{}\" has {} fragments, expected multiple of {}",
                               line, fragments.len(), n));
        }

        let mut result = Vec::new();
        for chunk in fragments.chunks(n) {
            match T::from_fragments(chunk) {
                Ok(v) => result.push(v),
                Err(msg) => {
                    let flagment_msg = if n == 1 {
                        format!("fragment {}", result.len())
                    } else {
                        let l = result.len();
                        format!("fragments {}-{}", n*l + 1, (n+1) * l)
                    };
                    return Err(format!(
                        "{} of line \"{}\": {}", flagment_msg, line, msg
                    ));
                }
            }
        }

        Ok(result)
    }
}

#[snippet = "read"]
macro_rules! impl_from_fragments_for_tuples {
    ($t:ident $var:ident $count:expr) => ();
    ($t:ident $var:ident $count:expr;
     $($inner_t:ident $inner_var:ident $inner_count:expr);*) => {
        impl_from_fragments_for_tuples!($($inner_t $inner_var $inner_count);*);

        impl <$t: FromFragments, $($inner_t: FromFragments),*> FromFragments
            for ($t, $($inner_t),*)
        {
            fn fragments_count() -> usize {
                let mut n = <$t>::fragments_count();
                $(
                    n += <$inner_t>::fragments_count();
                )*
                n
            }

            #[allow(unused_assignments)]
            fn from_fragments(fragments: &[&str]) ->
                Result<( $t, $($inner_t),*), String>
            {
                let mut start = 0;
                let $var = <$t>::from_fragments(
                    &fragments[start .. start+<$t>::fragments_count()]
                )?;
                start += <$t>::fragments_count();
                $(
                    let $inner_var =
                        <$inner_t>::from_fragments(
                            &fragments[start .. start+<$inner_t>::fragments_count()]
                        )?;
                    start += <$inner_t>::fragments_count();
                )*
                Ok(( $var, $($inner_var),* ))
            }
        }
    }
}

#[snippet = "read"]
impl_from_fragments_for_tuples!(T4 x4 4; T3 x3 3; T2 x2 2; T1 x1 1);

#[macro_export]
#[snippet = "read"]
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

#[macro_export]
#[snippet = "read"]
macro_rules! readls {
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

#[macro_export]
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

#[macro_export]
#[snippet = "read"]
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

#[macro_export]
#[snippet = "read"]
macro_rules! readn_loop {
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

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Debug, PartialEq)]
    struct Pair(i32, i32);

    impl FromFragments for Pair {
        fn fragments_count() -> usize { 2 }
        fn from_fragments(fragments: &[&str]) -> Result<Pair, String> {
            let x1 = i32::from_fragments(&fragments[0..1])?;
            let x2 = i32::from_fragments(&fragments[1..2])?;
            Ok(Pair(x1, x2))
        }
    }

    #[test]
    fn test_from_fragemnts_primitives() {
        assert_eq!(i32::from_fragments(&["42"]), Ok(42));
        assert!(i32::from_fragments(&["a"]).is_err());
        assert_eq!(String::from_fragments(&["string"]), Ok("string".to_string()));
    }

    #[test]
    fn test_from_fragments_custom() {
        assert_eq!(Pair::from_fragments(&["1", "2"]), Ok(Pair(1, 2)));
    }

    #[test]
    fn test_from_fratments_nested_tuple() {
        assert_eq!(<(i32, (i32, i32), i32)>::from_fragments(&["1", "2", "3", "4"]),
                   Ok((1, (2, 3), 4)));
    }

    #[test]
    fn test_from_line_vector() {
        assert_eq!(Vec::<i32>::from_line("1 2 3\n"), Ok(vec![1, 2, 3]));
    }

    #[test]
    fn test_from_line_cardinarity_mismatch() {
        assert!(Vec::<Pair>::from_line("1 2 3\n").is_err());
    }
}
