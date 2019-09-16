// # Add Document
//
// - custom readable type
// - custom readable collection
// - VecとHashSetがreadable collectionであること
//
// # Add Implementation
//
// - scan関数
// - readマクロに!があったら、そのwordを捨てる
//
// # Problems
//
// - readって関数を定義したい時があるかも inputのほうがよい？
// - Output typeの導入で、read関数の型パラメータ指定が必須になってしまった
//
// # scanのドキュメント
//
// 万が一、行単位でない入力読み込みが必要になった場合、
// `scan`関数で一つの値だけを読み込むことができる。
// scanの呼び出しに続けて行指向の読み込みを行うと、
// 入力行のうちの読み残した部分を読み込む。

//! スペース区切りの入力を簡単に読み込むための関数・マクロを提供する。
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
//! このようなボイラープレートを問題ごとに記述するのは現実的でないため、
//! このモジュールの提供する関数・マクロを用いて、
//! 入力読み込みを省力化するのが賢明である。
//!
//! 入力は行単位で読むよう設計されており、一回の関数呼び出しまたはマクロ展開で、
//! 標準入力の1行または複数行を読み込む。
//!
//! - 標準入力の1行を読むには、[`read`](fn.read.html)関数、[`read`](../macro.read.html)マクロを用いる。
//! - 標準入力の複数行を読むには、[`readls`](../macro.readls.html)マクロを用いる。
//! - 標準入力の一様な行をすべて読むには、[`readx`](fn.readx.html)関数、[`readx_loop`](../macro.readx_loop.html)マクロを用いる。
//! - 標準入力の一様な行を指定行数読むには、[`readn`](fn.readn.html)関数、[`readn_loop`](../macro.readn_loop.html)マクロを用いる。
//!

/// Readable from stdin.
///
/// Types implementing this trait can be converted from a specific number of *word*s.
/// A word is a fragment of an input line splitted by whiltespaces.
///
/// 以下の型は、`Readable`をimplしている。
///
/// - ユニット型 `()`
/// - `char`
/// - `String`
/// - すべての数値型(`isize`, `usize`, `i8`, `u8`, `i16`, `u16`, `i32`, `u32`, `i64`, `u64`, `f32`, `f64`)
///
/// `Readable`のみからなるタプルは常に`Readable`である。
///
/// `read`モジュールは、1-origin整数を読み込んで0-origin整数にする操作を、
/// 特殊な`Readable`型を提供することによって可能としている。
/// cf. [`usize_`](struct.usize_.html)
///
/// To make a custom readable type, use `readable` macro instead of implementing
/// this trait in most cases.
///
/// # Example
///
/// See implementation of [`Vec2`](../vec2/struct.Vec2.html).
#[snippet = "read"]
pub trait Readable {
    /// Output type.
    ///
    /// In most cases, `Output` should be `Self`.
    /// This type field exists for implementing 1-origin to 0-origin conversion
    /// by `usize_` etc.
    type Output;

    /// Returns how many words are read.
    fn words_count() -> usize;

    /// Converts words into `Output`s.
    ///
    /// If the conversion fails, returns `Err` with error message.
    ///
    /// # Panics
    ///
    /// If `words.len()` differs from `words_count()`,
    /// the method may panic.
    fn read_words(words: &[&str]) -> Result<Self::Output, String>;
}

// TODO: ABC113 C
// TODO: proc_macroでderive(Readable)したい
/// Makes a type readable from stdin.
///
/// Instead of write `impl Readable` manually, use this handy macro.
///
/// # Example
///
/// `String` implements `Readable` by the following way:
///
/// ```ignore
/// readable!(String, |ss| ss[0].to_string());
/// ```
///
/// This is OK because reading a `String` from a word never fails.
#[macro_export]
#[snippet = "read"]
macro_rules! readable {
    ( $t:ty, $words_count:expr, |$words:ident| $read_words:expr ) => {
        impl Readable for $t {
            type Output = $t;

            fn words_count() -> usize { $words_count }
            fn read_words($words: &[&str]) -> Result<$t, String> {
                Ok($read_words)
            }
        }
    };
}

#[snippet = "read"]
readable!((), 1, |_ss| ());

#[snippet = "read"]
readable!(String, 1, |ss| ss[0].to_string());

// Is `impl Readable for bool` necessary?

#[snippet = "read"]
impl Readable for char {
    type Output = char;

    fn words_count() -> usize { 1 }
    fn read_words(words: &[&str]) -> Result<char, String> {
        let chars: Vec<char> = words[0].chars().collect();
        if chars.len() == 1 {
            Ok(chars[0])
        } else {
            Err(format!("cannot parse `{}` as a char", words[0]))
        }
    }
}

/// For reading a string as `Vec<char>`.
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "CHARACTERS"
/// read!(s = Chars);
/// assert_eq!(s, vec!['C', 'H', 'A', 'R', 'A', 'C', 'T', 'E', 'R', 'S']);
/// ```
#[snippet = "read"]
pub struct Chars();

#[snippet = "read"]
impl Readable for Chars {
    type Output = Vec<char>;

    fn words_count() -> usize { 1 }
    fn read_words(words: &[&str]) -> Result<Vec<char>, String> {
        Ok(words[0].chars().collect())
    }
}

#[snippet = "read"]
macro_rules! impl_readable_for_ints {
    ( $( $t:ty )* ) => { $(
        impl Readable for $t {
            type Output = Self;

            fn words_count() -> usize { 1 }
            fn read_words(words: &[&str]) -> Result<$t, String> {
                use std::str::FromStr;
                <$t>::from_str(words[0]).map_err(|_| {
                    format!("cannot parse `{}` as {}", words[0], stringify!($t))
                })
            }
        }
    )* };
}

#[snippet = "read"]
impl_readable_for_ints!(i8 u8 i16 u16 i32 u32 i64 u64 isize usize f32 f64);

#[snippet = "read"]
macro_rules! define_one_origin_int_types {
    ( $new_t:ident $int_t:ty ) => {
        // TODO: 実際の問題を使った例にする
        /// Converts 1-origin integer into 0-origin when read from stdin.
        ///
        /// # Example
        ///
        /// ```no_run
        /// # #[macro_use] extern crate atcoder_snippets;
        /// # use atcoder_snippets::read::*;
        /// // Stdin: "1"
        /// read!(a = usize_);
        /// assert_eq!(a, 0);
        /// ```
        #[allow(non_camel_case_types)]
        pub struct $new_t;

        impl Readable for $new_t {
            type Output = $int_t;

            fn words_count() -> usize { 1 }
            fn read_words(words: &[&str]) -> Result<Self::Output, String> {
                <$int_t>::read_words(words).map(|n| n-1)
            }
        }
    };

    ( $new_t:ident $int_t:ty; $( $inner_new_t:ident $inner_int_t:ty );* ) => {
        define_one_origin_int_types!($new_t $int_t);
        define_one_origin_int_types!($($inner_new_t $inner_int_t);*);
    };
}

#[snippet = "read"]
define_one_origin_int_types!(u8_ u8; u16_ u16; u32_ u32; u64_ u64; usize_ usize);

#[snippet = "read"]
macro_rules! impl_readable_for_tuples {
    ( $t:ident $var:ident ) => ();
    ( $t:ident $var:ident; $( $inner_t:ident $inner_var:ident );* ) => {
        impl_readable_for_tuples!($($inner_t $inner_var);*);

        impl<$t: Readable, $($inner_t: Readable),*> Readable
            for ($t, $($inner_t),*)
        {
            type Output = ( <$t>::Output, $(<$inner_t>::Output),* );

            fn words_count() -> usize {
                let mut n = <$t>::words_count();
                $(
                    n += <$inner_t>::words_count();
                )*
                n
            }

            #[allow(unused_assignments)]
            fn read_words(words: &[&str]) ->
                Result<Self::Output, String>
            {
                let mut start = 0;
                let $var = <$t>::read_words(
                    &words[start .. start+<$t>::words_count()]
                )?;
                start += <$t>::words_count();
                $(
                    let $inner_var =
                        <$inner_t>::read_words(
                            &words[start .. start+<$inner_t>::words_count()]
                        )?;
                    start += <$inner_t>::words_count();
                )*
                Ok(( $var, $($inner_var),* ))
            }
        }
    };
}

#[snippet = "read"]
impl_readable_for_tuples!(T8 x8; T7 x7; T6 x6; T5 x5; T4 x4; T3 x3; T2 x2; T1 x1);

/// Readable by `read` function.
#[snippet = "read"]
pub trait ReadableFromLine {
    type Output;

    fn read_line(line: &str) -> Result<Self::Output, String>;
}

#[snippet = "read"]
fn split_into_words(line: &str) -> Vec<&str> {
    #[allow(deprecated)]
    line.trim_right_matches('\n').split_whitespace().collect()
}

#[snippet = "read"]
impl<T: Readable> ReadableFromLine for T {
    type Output = T::Output;

    fn read_line(line: &str) -> Result<T::Output, String> {
        let words = split_into_words(line);
        if words.len() != T::words_count() {
            return Err(format!("line `{}` has {} words, expected {}",
                               line, words.len(), T::words_count()));
        }

        T::read_words(&words)
    }
}

#[snippet = "read"]
macro_rules! impl_readable_from_line_for_tuples_with_from_iterator {
    ( $u:ident : $( + $bound:path )* => $seq_in:ty, $seq_out:ty; $t:ident $var:ident ) => {
        impl<$u: Readable> ReadableFromLine for $seq_in
        where
            <$u as Readable>::Output: Sized $(+ $bound)*
        {
            type Output = $seq_out;

            fn read_line(line: &str) -> Result<$seq_out, String> {
                let n = $u::words_count();
                let words = split_into_words(line);
                if words.len() % n != 0 {
                    return Err(format!("line `{}` has {} words, expected multiple of {}",
                                       line, words.len(), n));
                }

                let mut result = Vec::new();
                for chunk in words.chunks(n) {
                    match $u::read_words(chunk) {
                        Ok(v) => result.push(v),
                        Err(msg) => {
                            let flagment_msg = if n == 1 {
                                format!("word {}", result.len())
                            } else {
                                let l = result.len();
                                format!("words {}-{}", n*l + 1, (n+1) * l)
                            };
                            return Err(format!(
                                "{} of line `{}`: {}", flagment_msg, line, msg
                            ));
                        }
                    }
                }

                Ok(result.into_iter().collect())
            }
        }

        impl<T: Readable, $u: Readable> ReadableFromLine for (T, $seq_in)
        where
            <$u as Readable>::Output: Sized $(+ $bound)*
        {
            type Output = (T::Output, $seq_out);

            fn read_line(line: &str) -> Result<Self::Output, String> {
                let n = T::words_count();
                #[allow(deprecated)]
                let trimmed = line.trim_right_matches('\n');
                let words_and_rest: Vec<&str> = trimmed.splitn(n + 1, ' ').collect();

                if words_and_rest.len() < n {
                    return Err(format!("line `{}` has {} words, expected at least {}",
                                       line, words_and_rest.len(), n));
                }

                let words = &words_and_rest[..n];
                let empty_str = "";
                let rest = words_and_rest.get(n).unwrap_or(&empty_str);
                Ok((T::read_words(words)?, <$seq_in>::read_line(rest)?))
            }
        }

    };

    ( $u:ident : $( + $bound:path )* => $seq_in:ty, $seq_out:ty;
      $t:ident $var:ident, $( $inner_t:ident $inner_var:ident ),+ ) => {
        impl_readable_from_line_for_tuples_with_from_iterator!(
            $u: $(+ $bound)* => $seq_in, $seq_out; $($inner_t $inner_var),+
        );

        impl<$t: Readable, $($inner_t: Readable),+ , $u: Readable> ReadableFromLine
            for ($t, $($inner_t),+ , $seq_in)
        where
            <$u as Readable>::Output: Sized $(+ $bound)*
        {
            type Output = ($t::Output, $($inner_t::Output),+ , $seq_out);

            fn read_line(line: &str) -> Result<Self::Output, String> {
                let mut n = $t::words_count();
                $(
                    n += $inner_t::words_count();
                )+
                #[allow(deprecated)]
                let trimmed = line.trim_right_matches('\n');
                let words_and_rest: Vec<&str> = trimmed.splitn(n + 1, ' ')
                    .collect();

                if words_and_rest.len() < n {
                    return Err(
                        format!("line `{}` has {} words, expected at least {}",
                                line, words_and_rest.len(), n)
                    );
                }

                let words = &words_and_rest[..n];
                let empty_str = "";
                let rest = words_and_rest.get(n).unwrap_or(&empty_str);
                let ($var, $($inner_var),*) =
                    <($t, $($inner_t),+)>::read_words(words)?;
                Ok(($var, $($inner_var),* , <$seq_in>::read_line(rest)?))
            }
        }
    };
}

/// Make collection type readable from input line.
///
/// The collection type must implement `FromIterator`.
///
/// For example, `Vec` and `HashSet` are readable from input line by these declaration:
///
/// ```ignore
/// readable_collection!(U => Vec<U>, Vec<U::Output>);
/// readable_collection!(U: Eq, Hash => HashSet<U>, HashSet<U::Output>);
/// ```
///
/// The content of this macro should be either of the followings:
///
/// - `U` `=>` collection type for `U` `,` collection type for `U::Output`
/// - `U` `:` type bounds of the item type `=>` collection type for `U` `,` collection type for `U::Output`
///
/// The first identifier must be `U`, or the compilation may fail.
///
/// Be careful that the separator of type bounds is `,` not `+`.
/// This is because of a restriction of Rust's macro system.
#[snippet = "read"]
#[macro_export]
macro_rules! readable_collection {
    ($u:ident => $collection_in:ty, $collection_out:ty) => {
        impl_readable_from_line_for_tuples_with_from_iterator!(
            $u: => $collection_in, $collection_out;
            T8 x8, T7 x7, T6 x6, T5 x5, T4 x4, T3 x3, T2 x2, T1 x1
        );
    };

    ($u:ident : $( $bound:path ),* => $collection_in:ty, $collection_out:ty) => {
        impl_readable_from_line_for_tuples_with_from_iterator!(
            $u: $(+ $bound)* => $collection_in, $collection_out;
            T8 x8, T7 x7, T6 x6, T5 x5, T4 x4, T3 x3, T2 x2, T1 x1
        );
    }
}

#[snippet = "read"]
readable_collection!(U => Vec<U>, Vec<U::Output>);

#[snippet = "read"]
readable_collection!(
    U: Eq, std::hash::Hash => std::collections::HashSet<U>, std::collections::HashSet<U::Output>
);


/// Returns `Readable`s read from a line of stdin.
///
/// 読み込むことのできる型は、以下の通りである。
///
/// - [`Readable`](trait.Readable.html)をimplした型
/// - [`Readable`](trait.Readable.html)を要素型とする`Vec`
/// - タプルで、<code>Vec&lt;<i>Readable</i>&gt;</code>が最後の要素型になっているもの (eg. `(i32, Vec<i32>)`)
///
/// # Example
///
/// Solves [ABC086 B - Shift only](https://atcoder.jp/contests/abc081/tasks/abc081_b)
/// (4th problem of [AtCoder Beginners Selection](https://atcoder.jp/contests/abs).)
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// #
/// fn main() {
///     read!();
///     let ans = read::<Vec<u32>>()
///         .into_iter()
///         .map(|n| n.trailing_zeros())
///         .min()
///         .unwrap();
///     println!("{}", ans);
/// }
/// ```
///
/// この関数は型パラメータの指定が必須である。
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Instead of `let n: i32 = read()`, write as following:
/// let n = read::<i32>();
/// ```
/// 読み込みに失敗した場合、エラーメッセージが表示されてpanicする。
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "1 2 3.45"
/// read!(a = i32, b = i32, x = i32);
/// // thread 'main' panicked at 'called `Result::unwrap()` on an `Err` value: "word 3 of line `1 2 3.45\n`: cannot parse `3.45` as i32"'
/// ```

#[snippet = "read"]
pub fn read<T: ReadableFromLine>() -> T::Output {
    let mut line = String::new();
    // Can be faster by removing UTF-8 validation,
    // but enables validation in case of feeding a wrong test case manually.
    std::io::stdin().read_line(&mut line).unwrap();
    T::read_line(&line).unwrap()
}

// TODO: 実際の問題の例だけを使う
/// 標準入力から一行を読み込み、結果を変数に代入する。
///
/// # Examples
///
/// Solves [ABC086 A - Product](https://atcoder.jp/contests/abc086/tasks/abc086_a)
/// (2nd problem of [AtCoder Beginners Selection](https://atcoder.jp/contests/abs).)
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// #
/// fn main() {
///     read!(a = u32, b = u32);
///     println!("{}", if a*b % 2 == 0 { "Even" } else { "Odd" });
/// }
/// ```
///
/// `read!(a = u32, b = u32);`によって、
/// 入力の1行から、スペースで区切られたふたつの`i32`数値が読み込まれる。
/// その結果は、immutable変数`a`, `b`に代入される。
///
/// `=`記号の右側には、[`read`](read/fn.read)関数で読み込むことができる
/// 任意の型を置くことができる。
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "1 17 8 3 2 6"
/// read!(mut ns = Vec<usize>);
/// assert_eq!(ns, vec![1usize, 17, 8, 3, 2, 6]);
/// ```
///
/// `=`記号の左側には、`let`で変数を宣言する際の左辺に書くことのできる
/// 任意のパターンを置くことができる。
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "30"
/// read!(mut n = i32);
/// n *= 2;
/// assert_eq!(n, 60);
/// ```
///
/// 単に`read!()`と書くと、入力の1行を捨てる。
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "5\n10 20 30 40 50"
/// read!();
/// read!(xs = Vec<i32>);
/// assert_eq!(xs, vec![10, 20, 30, 40, 50]);
/// ```
#[macro_export]
#[snippet = "read"]
macro_rules! read {
    // Discards a line
    () => {
        let mut line = String::new();
        // Can be faster by removing UTF-8 validation,
        // but enables validation in case of feeding a wrong test case manually.
        std::io::stdin().read_line(&mut line).unwrap();
    };

    // Gets a ReadableFromLine
    ( $pat:pat = $t:ty ) => {
        let $pat = read::<$t>();
    };

    // Gets Readable's
    ( $( $pat:pat = $t:ty ),+ ) => {
        read!(($($pat),*) = ($($t),*));
    };
}

// ABC112 A
/// Reads multiple lines from stdin and create let bindings.
///
/// The usage is very similar to [`read`](macro.read.html) macro,
/// but each binding corresponds to a line, instead of some words.
///
/// # Example
///
/// Solves [AtCoder Beginners Selection Practice A - Welcome to AtCoder](https://abs.contest.atcoder.jp/tasks/practice_1).
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// #
/// fn main() {
///     readls!(a = u16, (b, c) = (u16, u16), s = String);
///     println!("{} {}", a+b+c, s);
/// }
/// ```
///
/// The solution can be written using `read` macro:
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// #
/// fn main() {
///     read!(a = u16);
///     read!(b = u16, c = u16);
///     read!(s = String);
///     println!("{} {}", a+b+c, s);
/// }
/// ```
///
/// but using `readls` makes the code a bit shorter.
#[macro_export]
#[snippet = "read"]
macro_rules! readls {
    // Gets ReadableFromLine's
    ( $( $pat:pat = $t:ty ),+ ) => {
        $(
            // Can be faster by locking stdin only once.
            read!($pat = $t);
        )*
    };
}

// TODO: Solve ABC118 B
/// 標準入力の残りの行をすべて読み込み、`Vec`を返す。
///
/// # Example
///
/// Solves [AtCoder Beginner Contest 109: Problem B - Shiritori](https://abc109.contest.atcoder.jp/tasks/abc109_b).
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// # use atcoder_snippets::utils::yn;
/// use std::collections::HashSet;
///
/// // Checks whther the given sequence of words satisfies the constraint.
/// fn check(words: &[String]) -> bool {
///     let mut occurred = HashSet::new();
///     let first = &words[0];
///     occurred.insert(first);
///     let mut last_char = first.chars().last().unwrap();
///
///     for word in &words[1..] {
///         if !word.starts_with(last_char) {
///             return false;
///         }
///         if !occurred.insert(word) {
///             return false;
///         }
///         last_char = word.chars().last().unwrap();
///     }
///
///     return true;
/// }
///
/// fn main() {
///     read!();
///     // Uses `yn` snippet.
///     yn(check(&readx::<String>()));
/// }
/// ```
#[snippet = "read"]
pub fn readx<T: ReadableFromLine>() -> Vec<T::Output> {
    use std::io::{self, BufRead};
    let stdin = io::stdin();
    // Can be faster by removing UTF-8 validation,
    // but enables validation in case of feeding a wrong test case manually.
    let result = stdin.lock().lines().map(|line_result| {
        let line = line_result.expect("read from stdin failed");
        T::read_line(&line).unwrap()
    }).collect();
    result
}

// TODO: Improve documentation
/// 標準入力の残りの行をすべて読み、一行ずつ処理する。
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "5 1 2 3 4 5\n1 10\n2 100 200"
/// readx_loop!(|num_count = usize, nums = Vec<u8>| println!("{:?}", nums));
/// // Stdout:
/// // [1, 2, 3, 4, 5]
/// // [10]
/// // [100, 200]
/// ```
#[macro_export]
#[snippet = "read"]
macro_rules! readx_loop {
    ( |$pat:pat = $t:ty| $body:expr ) => {
        {
            use std::io::BufRead;
            let stdin = std::io::stdin();
            // Can be faster by removing UTF-8 validation,
            // but enables validation in case of feeding a wrong test case manually.
            for line in stdin.lock().lines() {
                let line = line.expect("read from stdin failed");
                let $pat = <$t>::read_line(&line).unwrap();
                $body
            }
        }
    };

    ( |$($pat:pat = $t:ty),*| $body:expr ) => {
        readx_loop!(|($($pat),*) = ($($t),*)| $body);
    };
}

// TODO: Solve ABC119 D
/// 標準入力の残りの行を`n`行読み込み、`Vec`を返す。
///
/// # Panic
///
/// 標準入力の残りの行が`n`行未満だった場合、panicする。
///
/// # Example
///
/// Reads the input of [ABC119 D: Lazy Faith](https://atcoder.jp/contests/abc119/tasks/abc119_d).
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "2 3 4\n100\n600\n400\n900\n1000\n150\n2000\n899\n799"
/// read!(shrine_count = usize, temple_count = usize, _ = ());
/// let shrines = readn::<i64>(shrine_count);
/// let temples = readn::<i64>(temple_count);
/// let queries = readx::<i64>();
///
/// assert_eq!(shrines, vec![100, 600]);
/// assert_eq!(temples, vec![400, 900, 1000]);
/// ```
#[snippet = "read"]
pub fn readn<T: ReadableFromLine>(n: usize) -> Vec<T::Output> {
    use std::io::{self, BufRead};
    let stdin = io::stdin();
    // Can be faster by removing UTF-8 validation,
    // but enables validation in case of feeding a wrong test case manually.
    let result: Vec<T::Output> = stdin.lock().lines().take(n).map(|line_result| {
        let line = line_result.expect("read from stdin failed");
        T::read_line(&line).unwrap()
    }).collect();
    if result.len() < n {
        panic!("expected reading {} lines, but only {} lines are read",
               n, result.len());
    }
    result
}

// TODO: Improve documentation
// TODO: Avoid multiple use of std::io::BufRead
/// 標準入力の残りの行をn行読み、一行ずつ処理する。
///
/// # Panic
///
/// 標準入力の残りの行がn行未満だった場合、panicする。
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "5 1 2 3 4 5\n1 10\n2 100 200"
/// readn_loop!(2, |num_count = usize, nums = Vec<u8>| println!("{:?}", nums));
/// // Stdout:
/// // [1, 2, 3, 4, 5]
/// // [10]
/// ```
#[macro_export]
#[snippet = "read"]
macro_rules! readn_loop {
    ( $n:expr, |$pat:pat = $t:ty| $body:expr ) => {
        {
            use std::io::BufRead;
            let stdin = std::io::stdin();
            let mut lock = stdin.lock();
            for _ in 0..$n {
                let mut line = String::new();
                // Can be faster by removing UTF-8 validation,
                // but enables validation in case of feeding a wrong test case manually.
                lock.read_line(&mut line).expect("read from stdin failed");
                let $pat = <$t>::read_line(&line).unwrap();
                $body
            }
        }
    };

    ( $n:expr, |$($pat:pat = $t:ty),*| $body:expr ) => {
        readn_loop!($n, |($($pat),*) = ($($t),*)| $body);
    };
}

// TODO: parse().unwrap()ではうまくいかない例を示す
/// `Readable`を読み出すことができる型。
///
/// このトレイトにより、`Readable`の実装が簡単になる場合がある。
#[snippet = "read"]
pub trait Words {
    fn read<T: Readable>(&self) -> T::Output;
}

#[snippet = "read"]
impl<'a> Words for [&'a str] {
    fn read<T: Readable>(&self) -> T::Output {
        T::read_words(self).unwrap()
    }
}

#[snippet = "read"]
impl<'a> Words for &'a str {
    fn read<T: Readable>(&self) -> T::Output {
        T::read_words(&[self]).unwrap()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashSet;

    #[derive(Debug, PartialEq, Eq)]
    struct Pair(i32, i32);

    impl Readable for Pair {
        type Output = Self;

        fn words_count() -> usize { 2 }
        fn read_words(words: &[&str]) -> Result<Pair, String> {
            let x1 = i32::read_words(&words[0..1])?;
            let x2 = i32::read_words(&words[1..2])?;
            Ok(Pair(x1, x2))
        }
    }

    #[test]
    fn test_read_words_primitives() {
        assert_eq!(<()>::read_words(&["input"]), Ok(()));
        assert_eq!(String::read_words(&["input"]), Ok("input".to_string()));
        assert_eq!(char::read_words(&["a"]), Ok('a'));
        assert!(char::read_words(&["input"]).is_err());
        assert_eq!(i32::read_words(&["42"]), Ok(42));
        assert!(i32::read_words(&["a"]).is_err());
    }

    #[test]
    fn test_read_chars() {
        let s = Chars::read_words(&["CHARACTERS"]);
        assert_eq!(s, Ok(vec!['C', 'H', 'A', 'R', 'A', 'C', 'T', 'E', 'R', 'S']));
    }

    #[test]
    fn test_read_words_one_origin_integer() {
        assert_eq!(u64_::read_words(&["1"]), Ok(0));
    }

    #[test]
    fn test_read_words_custom() {
        assert_eq!(Pair::read_words(&["1", "2"]), Ok(Pair(1, 2)));
    }

    #[test]
    fn test_from_fratments_nested_tuple() {
        assert_eq!(<(i32, (i32, i32), i32)>::read_words(&["1", "2", "3", "4"]),
                   Ok((1, (2, 3), 4)));
    }

    #[test]
    fn test_read_line_vector() {
        assert_eq!(Vec::<i32>::read_line("1 2 3\n"), Ok(vec![1, 2, 3]));
    }

    #[test]
    fn test_read_line_readable_and_vector() {
        assert_eq!(<((i32, i32), Vec<i32>)>::read_line("1 2 3 4 5"),
                   Ok(((1, 2), vec![3, 4, 5])));
        assert_eq!(<((i32, i32), Vec<i32>)>::read_line("1 2 3"),
                   Ok(((1, 2), vec![3])));
        assert_eq!(<((i32, i32), Vec<i32>)>::read_line("1 2"),
                   Ok(((1, 2), vec![])));
        assert!(<((i32, i32), Vec<i32>)>::read_line("1").is_err());
    }

    #[test]
    fn test_read_line_multiple_readables_and_vector() {
        assert_eq!(<(i32, i32, Vec<i32>)>::read_line("1 2 3 4 5"),
                   Ok((1, 2, vec![3, 4, 5])));
        assert_eq!(<(i32, i32, i32, Vec<i32>)>::read_line("1 2 3 4 5"),
                   Ok((1, 2, 3, vec![4, 5])));
        assert_eq!(<(i32, i32, i32, Vec<i32>)>::read_line("1 2 3"),
                   Ok((1, 2, 3, vec![])));
        assert!(<(i32, i32, i32, Vec<i32>)>::read_line("1 2").is_err());
    }

    #[test]
    fn test_read_line_vector_of_one_origin_integers() {
        assert_eq!(Vec::<usize_>::read_line("1 2 3\n"), Ok(vec![0, 1, 2]));
    }

    #[test]
    fn test_read_line_hash_set() {
        let expected: HashSet<u32> = (1..=3).collect();
        assert_eq!(HashSet::<u32>::read_line("1 2 1 3"), Ok(expected));
    }

    #[test]
    fn test_read_line_cardinarity_mismatch() {
        assert!(Vec::<Pair>::read_line("1 2 3\n").is_err());
    }

    #[test]
    fn test_words() {
        let words: Vec<&str> = "1 2".split_whitespace().collect();
        let pair: Pair = words.read::<Pair>();
        assert_eq!(pair, Pair(1, 2));
    }
}
