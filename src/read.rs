// # Add Document
//
// - custom readable type
// - custom readable collection
// - VecとHashSetがreadable collectionであること
//
// # Add Implementation
//
// - scan関数
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

//! Macros and functions for reading problem input.
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
//! - 標準入力の1行を読むには、[`read`](../macro.read.html)マクロを用いる。
//! - 標準入力の複数行を読むには、[`read_chunk`](../macro.read_chunk.html)マクロを用いる。
//! - 標準入力の一様な行を一定行数、あるいはすべて読むには、[`read_lines`](fn.read_lines.html)関数を用いる。
//! - 標準入力の複数行に渡る入力を繰り返し読むには、[`read_chunks`](fn.read_chunks.html)関数を用いる。
//!   Typically useful for reading queries in Codeforces.

// BEGIN SNIPPET read

/// Readable from a constant number of words.
///
/// A word is a fragment of an input line splitted by whiltespaces.
///
/// The following types are readable from one word:
///
/// - Unit type `()`
/// - `char`
/// - `String`
/// - All primitibe numeric types (`isize`, `usize`, `i8`, `u8`, `i16`, `u16`, `i32`, `u32`, `i64`, `u64`, `f32`, `f64`)
///
/// A tuple of an arbitrary number of `Readable`s is `Readable`.
///
/// `read`モジュールは、1-origin整数を読み込んで0-origin整数にする操作を、
/// 特殊な`Readable`型を提供することによって可能としている。
/// cf. [`usize_`](struct.usize_.html)
///
/// To make a custom readable type, use `readable` macro instead of implementing
/// this trait directly.
///
/// # Example
///
/// See implementation of [`Vec2`](../vec2/struct.Vec2.html).
pub trait Readable {
    /// Output type.
    ///
    /// Usually `Output` should be `Self`, but there are some exceptions:
    ///
    /// - 1-origin to 0-origin conversion by `usize_`[struct.usize_.html] etc.
    /// - [`Chars`](struct.Chars.html)
    type Output;

    /// Returns how many words are read.
    const WORDS_COUNT: usize;

    /// Converts words into `Output`s.
    ///
    /// If the conversion fails, returns `Err` with error message.
    ///
    /// # Panics
    ///
    /// If `words.len()` differs from `WORDS_COUNT`,
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
macro_rules! readable {
    ( $t:ty, $words_count:expr, |$words:ident| $read_words:expr ) => {
        impl Readable for $t {
            type Output = $t;
            const WORDS_COUNT: usize = $words_count;

            fn read_words($words: &[&str]) -> Result<$t, String> {
                Ok($read_words)
            }
        }
    };
}

readable!((), 1, |_ss| ());

readable!(String, 1, |ss| ss[0].to_string());

// Is `impl Readable for bool` necessary?

impl Readable for char {
    type Output = char;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<char, String> {
        let chars: Vec<char> = words[0].chars().collect();
        if chars.len() == 1 {
            Ok(chars[0])
        } else {
            Err(format!("cannot parse `{}` as a char", words[0]))
        }
    }
}

/// Reads a string as `Vec<char>`.
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
pub struct Chars();

impl Readable for Chars {
    type Output = Vec<char>;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<Vec<char>, String> {
        Ok(words[0].chars().collect())
    }
}

/// Reads a string as `Vec<u8>`
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "AB"
/// read!(bs = Bytes);
/// let indices = ((bs[0] - b'A') as usize, (bs[1] - b'A') as usize);
/// assert_eq!(indices, (0, 1));
/// ```
pub struct Bytes();

impl Readable for Bytes {
    type Output = Vec<u8>;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<Vec<u8>, String> {
        Ok(words[0].bytes().collect())
    }
}

// Primitive integers
// Implemented by copy and paste instead of macro for compilation speedup

impl Readable for i8 {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<i8, String> {
        use std::str::FromStr;
        i8::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as i8", words[0])
        })
    }
}

impl Readable for u8 {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<u8, String> {
        use std::str::FromStr;
        u8::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as u8", words[0])
        })
    }
}

impl Readable for i16 {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<i16, String> {
        use std::str::FromStr;
        i16::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as i16", words[0])
        })
    }
}

impl Readable for u16 {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<u16, String> {
        use std::str::FromStr;
        u16::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as u16", words[0])
        })
    }
}

impl Readable for i32 {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<i32, String> {
        use std::str::FromStr;
        i32::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as i32", words[0])
        })
    }
}

impl Readable for u32 {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<u32, String> {
        use std::str::FromStr;
        u32::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as u32", words[0])
        })
    }
}

impl Readable for i64 {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<i64, String> {
        use std::str::FromStr;
        i64::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as i64", words[0])
        })
    }
}

impl Readable for u64 {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<u64, String> {
        use std::str::FromStr;
        u64::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as u64", words[0])
        })
    }
}

impl Readable for isize {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<isize, String> {
        use std::str::FromStr;
        <isize>::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as isize", words[0])
        })
    }
}

impl Readable for usize {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<usize, String> {
        use std::str::FromStr;
        <usize>::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as usize", words[0])
        })
    }
}

impl Readable for f32 {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<f32, String> {
        use std::str::FromStr;
        f32::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as f32", words[0])
        })
    }
}

impl Readable for f64 {
    type Output = Self;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<f64, String> {
        use std::str::FromStr;
        f64::from_str(words[0]).map_err(|_| {
            format!("cannot parse `{}` as f64", words[0])
        })
    }
}

// 0-origin unsigned integers
// Copy and paste instead of using macro for compilation speedup

// TODO: 実際の問題を使った例にする
/// Converts 1-origin integer into 0-origin when read from stdin.
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "1"
/// read!(a = u8_);
/// assert_eq!(a, 0);
/// ```
#[allow(non_camel_case_types)]
pub struct u8_;

impl Readable for u8_ {
    type Output = u8;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        u8::read_words(words).map(|n| n-1)
    }
}

/// Converts 1-origin integer into 0-origin when read from stdin.
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "1"
/// read!(a = u16_);
/// assert_eq!(a, 0);
/// ```
#[allow(non_camel_case_types)]
pub struct u16_;

impl Readable for u16_ {
    type Output = u16;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        u16::read_words(words).map(|n| n-1)
    }
}

/// Converts 1-origin integer into 0-origin when read from stdin.
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "1"
/// read!(a = u32_);
/// assert_eq!(a, 0);
/// ```
#[allow(non_camel_case_types)]
pub struct u32_;

impl Readable for u32_ {
    type Output = u32;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        u32::read_words(words).map(|n| n-1)
    }
}

/// Converts 1-origin integer into 0-origin when read from stdin.
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "1"
/// read!(a = u64_);
/// assert_eq!(a, 0);
/// ```
#[allow(non_camel_case_types)]
pub struct u64_;

impl Readable for u64_ {
    type Output = u64;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        u64::read_words(words).map(|n| n-1)
    }
}

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
pub struct usize_;

impl Readable for usize_ {
    type Output = usize;
    const WORDS_COUNT: usize = 1;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        <usize>::read_words(words).map(|n| n-1)
    }
}

// Tuples
// Copy and paste instead of using macro for compilation speedup

impl<T1: Readable, T2: Readable> Readable for (T1, T2) {
    type Output = (T1::Output, T2::Output);
    const WORDS_COUNT: usize = T1::WORDS_COUNT + T2::WORDS_COUNT;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        assert_eq!(words.len(), Self::WORDS_COUNT);

        let mut start = 0;

        let count1 = T1::WORDS_COUNT;
        let val1 = T1::read_words(&words[start .. start+count1])?;
        start += count1;

        let val2 = T2::read_words(&words[start..])?;

        Ok((val1, val2))
    }
}

impl<T1: Readable, T2: Readable, T3: Readable> Readable for (T1, T2, T3) {
    type Output = (T1::Output, T2::Output, T3::Output);
    const WORDS_COUNT: usize = T1::WORDS_COUNT + T2::WORDS_COUNT + T3::WORDS_COUNT;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        assert_eq!(words.len(), Self::WORDS_COUNT);

        let mut start = 0;

        let count1 = T1::WORDS_COUNT;
        let val1 = T1::read_words(&words[start .. start+count1])?;
        start += count1;

        let count2 = T2::WORDS_COUNT;
        let val2 = T2::read_words(&words[start .. start+count2])?;
        start += count2;

        let val3 = T3::read_words(&words[start..])?;

        Ok((val1, val2, val3))
    }
}

impl<T1: Readable, T2: Readable, T3: Readable, T4: Readable> Readable for (T1, T2, T3, T4) {
    type Output = (T1::Output, T2::Output, T3::Output, T4::Output);
    const WORDS_COUNT: usize = T1::WORDS_COUNT + T2::WORDS_COUNT + T3::WORDS_COUNT + T4::WORDS_COUNT;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        assert_eq!(words.len(), Self::WORDS_COUNT);

        let mut start = 0;

        let count1 = T1::WORDS_COUNT;
        let val1 = T1::read_words(&words[start .. start+count1])?;
        start += count1;

        let count2 = T2::WORDS_COUNT;
        let val2 = T2::read_words(&words[start .. start+count2])?;
        start += count2;

        let count3 = T3::WORDS_COUNT;
        let val3 = T3::read_words(&words[start .. start+count3])?;
        start += count3;

        let val4 = T4::read_words(&words[start..])?;

        Ok((val1, val2, val3, val4))
    }
}

impl<T1: Readable, T2: Readable, T3: Readable, T4: Readable, T5: Readable> Readable for (T1, T2, T3, T4, T5) {
    type Output = (T1::Output, T2::Output, T3::Output, T4::Output, T5::Output);
    const WORDS_COUNT: usize = T1::WORDS_COUNT + T2::WORDS_COUNT + T3::WORDS_COUNT + T4::WORDS_COUNT + T5::WORDS_COUNT;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        assert_eq!(words.len(), Self::WORDS_COUNT);

        let mut start = 0;

        let count1 = T1::WORDS_COUNT;
        let val1 = T1::read_words(&words[start .. start+count1])?;
        start += count1;

        let count2 = T2::WORDS_COUNT;
        let val2 = T2::read_words(&words[start .. start+count2])?;
        start += count2;

        let count3 = T3::WORDS_COUNT;
        let val3 = T3::read_words(&words[start .. start+count3])?;
        start += count3;

        let count4 = T4::WORDS_COUNT;
        let val4 = T4::read_words(&words[start .. start+count4])?;
        start += count4;

        let val5 = T5::read_words(&words[start..])?;

        Ok((val1, val2, val3, val4, val5))
    }
}


impl<T1: Readable, T2: Readable, T3: Readable, T4: Readable, T5: Readable, T6: Readable> Readable for (T1, T2, T3, T4, T5, T6) {
    type Output = (T1::Output, T2::Output, T3::Output, T4::Output, T5::Output, T6::Output);
    const WORDS_COUNT: usize = T1::WORDS_COUNT + T2::WORDS_COUNT + T3::WORDS_COUNT + T4::WORDS_COUNT + T5::WORDS_COUNT + T6::WORDS_COUNT;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        assert_eq!(words.len(), Self::WORDS_COUNT);

        let mut start = 0;

        let count1 = T1::WORDS_COUNT;
        let val1 = T1::read_words(&words[start .. start+count1])?;
        start += count1;

        let count2 = T2::WORDS_COUNT;
        let val2 = T2::read_words(&words[start .. start+count2])?;
        start += count2;

        let count3 = T3::WORDS_COUNT;
        let val3 = T3::read_words(&words[start .. start+count3])?;
        start += count3;

        let count4 = T4::WORDS_COUNT;
        let val4 = T4::read_words(&words[start .. start+count4])?;
        start += count4;

        let count5 = T5::WORDS_COUNT;
        let val5 = T5::read_words(&words[start .. start+count5])?;
        start += count5;

        let val6 = T6::read_words(&words[start..])?;

        Ok((val1, val2, val3, val4, val5, val6))
    }
}

impl<T: Readable> Readable for [T; 2] {
    type Output = [T::Output; 2];
    const WORDS_COUNT: usize = T::WORDS_COUNT * 2;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        assert_eq!(words.len(), Self::WORDS_COUNT);

        let val1 = T::read_words(&words[T::WORDS_COUNT*0 .. T::WORDS_COUNT*1])?;
        let val2 = T::read_words(&words[T::WORDS_COUNT*1 .. T::WORDS_COUNT*2])?;
        Ok([val1, val2])
    }
}

impl<T: Readable> Readable for [T; 3] {
    type Output = [T::Output; 3];
    const WORDS_COUNT: usize = T::WORDS_COUNT * 3;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        assert_eq!(words.len(), Self::WORDS_COUNT);

        let val1 = T::read_words(&words[T::WORDS_COUNT*0 .. T::WORDS_COUNT*1])?;
        let val2 = T::read_words(&words[T::WORDS_COUNT*1 .. T::WORDS_COUNT*2])?;
        let val3 = T::read_words(&words[T::WORDS_COUNT*2 .. T::WORDS_COUNT*3])?;
        Ok([val1, val2, val3])
    }
}

impl<T: Readable> Readable for [T; 4] {
    type Output = [T::Output; 4];
    const WORDS_COUNT: usize = T::WORDS_COUNT * 4;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        assert_eq!(words.len(), Self::WORDS_COUNT);

        let val1 = T::read_words(&words[T::WORDS_COUNT*0 .. T::WORDS_COUNT*1])?;
        let val2 = T::read_words(&words[T::WORDS_COUNT*1 .. T::WORDS_COUNT*2])?;
        let val3 = T::read_words(&words[T::WORDS_COUNT*2 .. T::WORDS_COUNT*3])?;
        let val4 = T::read_words(&words[T::WORDS_COUNT*3 .. T::WORDS_COUNT*4])?;
        Ok([val1, val2, val3, val4])
    }
}

impl<T: Readable> Readable for [T; 5] {
    type Output = [T::Output; 5];
    const WORDS_COUNT: usize = T::WORDS_COUNT * 5;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        assert_eq!(words.len(), Self::WORDS_COUNT);

        let val1 = T::read_words(&words[T::WORDS_COUNT*0 .. T::WORDS_COUNT*1])?;
        let val2 = T::read_words(&words[T::WORDS_COUNT*1 .. T::WORDS_COUNT*2])?;
        let val3 = T::read_words(&words[T::WORDS_COUNT*2 .. T::WORDS_COUNT*3])?;
        let val4 = T::read_words(&words[T::WORDS_COUNT*3 .. T::WORDS_COUNT*4])?;
        let val5 = T::read_words(&words[T::WORDS_COUNT*4 .. T::WORDS_COUNT*5])?;
        Ok([val1, val2, val3, val4, val5])
    }
}

impl<T: Readable> Readable for [T; 6] {
    type Output = [T::Output; 6];
    const WORDS_COUNT: usize = T::WORDS_COUNT * 6;

    fn read_words(words: &[&str]) -> Result<Self::Output, String> {
        assert_eq!(words.len(), Self::WORDS_COUNT);

        let val1 = T::read_words(&words[T::WORDS_COUNT*0 .. T::WORDS_COUNT*1])?;
        let val2 = T::read_words(&words[T::WORDS_COUNT*1 .. T::WORDS_COUNT*2])?;
        let val3 = T::read_words(&words[T::WORDS_COUNT*2 .. T::WORDS_COUNT*3])?;
        let val4 = T::read_words(&words[T::WORDS_COUNT*3 .. T::WORDS_COUNT*4])?;
        let val5 = T::read_words(&words[T::WORDS_COUNT*4 .. T::WORDS_COUNT*5])?;
        let val6 = T::read_words(&words[T::WORDS_COUNT*5 .. T::WORDS_COUNT*6])?;
        Ok([val1, val2, val3, val4, val5, val6])
    }
}

/// Readable by `read` function/macro.
pub trait ReadableFromLine {
    type Output;

    fn read_line(line: &str) -> Result<Self::Output, String>;
}

fn split_into_words(line: &str) -> Vec<&str> {
    line.trim_end_matches('\n').split_whitespace().collect()
}

impl<T: Readable> ReadableFromLine for T {
    type Output = T::Output;

    fn read_line(line: &str) -> Result<T::Output, String> {
        let words = split_into_words(line);
        if words.len() != T::WORDS_COUNT {
            return Err(format!("line `{}` has {} words, expected {}",
                               line, words.len(), T::WORDS_COUNT));
        }

        T::read_words(&words)
    }
}

pub fn read_words_into_vec<T: Readable>(words: &[&str], line: &str) -> Result<Vec<T::Output>, String> {
    let n = T::WORDS_COUNT;
    assert_eq!(words.len() % n, 0);

    let mut result = Vec::new();
    for chunk in words.chunks(n) {
        match T::read_words(chunk) {
            Ok(v) => result.push(v),
            Err(msg) => {
                let fragment_msg = if n == 1 {
                    format!("word {}", result.len())
                } else {
                    let l = result.len();
                    format!("words {}-{}", n*l + 1, (n+1) * l)
                };
                return Err(format!(
                    "{} of line `{}`: {}", fragment_msg, line, msg
                ));
            }
        }
    }
    Ok(result)
}

pub fn split_into_words_for_collection<T: Readable>(
    line: &str, prefix_words_count: usize
) -> Result<Vec<&str>, String> {
    let n = T::WORDS_COUNT;
    let words = split_into_words(line);
    if words.len() < prefix_words_count {
        return Err(
            format!("line `{}` has {} words, expected at least {}",
                    line, words.len(), prefix_words_count)
        );
    }
    if (words.len() - prefix_words_count) % T::WORDS_COUNT != 0 {
        return Err(
            format!("line `{}` has {} words, expected {} + {}",
                    line, words.len(), prefix_words_count, n)
        );
    }
    Ok(words)
}

/// Make collection type readable from input line.
///
/// The collection type must implement `FromIterator`.
///
/// For example, `Vec` is readable from input line thanks to the following declaration:
///
/// ```ignore
/// readable_collection!(U => Vec<U>, Vec<U::Output>);
/// ```
///
/// To make `HashSet` readable, declare as:
///
/// ```ignore
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
#[macro_export]
macro_rules! readable_collection {
    ($u:ident => $collection_in:ty, $collection_out:ty) => {
        readable_collection!($u: => $collection_in, $collection_out);
    };

    ($u:ident : $( $bound:path ),* => $collection_in:ty, $collection_out:ty) => {
        // Copy and paste impls instead of using recursive macro for compilation speedup

        impl<$u: Readable> ReadableFromLine for $collection_in
        where
            <$u as Readable>::Output: Sized $(+ $bound)*
        {
            type Output = $collection_out;

            fn read_line(line: &str) -> Result<Self::Output, String> {
                let words = split_into_words_for_collection::<$u>(line, 0)?;
                Ok(read_words_into_vec::<$u>(&words, line)?.into_iter().collect())
            }
        }

        impl<T1: Readable, $u: Readable> ReadableFromLine for (T1, $collection_in)
        where
            <$u as Readable>::Output: Sized $(+ $bound)*
        {
            type Output = (T1::Output, $collection_out);

            fn read_line(line: &str) -> Result<Self::Output, String> {
                let prefix_len = T1::WORDS_COUNT;
                let words = split_into_words_for_collection::<$u>(line, prefix_len)?;

                let val1 = T1::read_words(&words[..prefix_len])?;
                let rest = read_words_into_vec::<$u>(&words[prefix_len..], line)?;
                Ok((val1, rest.into_iter().collect()))
            }
        }

        impl<T1: Readable, T2: Readable, $u: Readable> ReadableFromLine for (T1, T2, $collection_in)
        where
            <$u as Readable>::Output: Sized $(+ $bound)*
        {
            type Output = (T1::Output, T2::Output, $collection_out);

            fn read_line(line: &str) -> Result<Self::Output, String> {
                let prefix_len = <(T1, T2)>::WORDS_COUNT;
                let words = split_into_words_for_collection::<$u>(line, prefix_len)?;
                let mut start = 0;

                let count1 = T1::WORDS_COUNT;
                let val1 = T1::read_words(&words[start .. start+count1])?;
                start += count1;

                let count2 = T2::WORDS_COUNT;
                let val2 = T2::read_words(&words[start .. start+count2])?;

                let rest = read_words_into_vec::<$u>(&words[prefix_len..], line)?;
                Ok((val1, val2, rest.into_iter().collect()))
            }
        }

        impl<T1: Readable, T2: Readable, T3: Readable, $u: Readable> ReadableFromLine for (T1, T2, T3, $collection_in)
        where
            <$u as Readable>::Output: Sized $(+ $bound)*
        {
            type Output = (T1::Output, T2::Output, T3::Output, $collection_out);

            fn read_line(line: &str) -> Result<Self::Output, String> {
                let prefix_len = <(T1, T2, T3)>::WORDS_COUNT;
                let words = split_into_words_for_collection::<$u>(line, prefix_len)?;
                let mut start = 0;

                let count1 = T1::WORDS_COUNT;
                let val1 = T1::read_words(&words[start .. start+count1])?;
                start += count1;

                let count2 = T2::WORDS_COUNT;
                let val2 = T2::read_words(&words[start .. start+count2])?;
                start += count2;

                let count3 = T3::WORDS_COUNT;
                let val3 = T3::read_words(&words[start .. start+count3])?;

                let rest = read_words_into_vec::<$u>(&words[prefix_len..], line)?;
                Ok((val1, val2, val3, rest.into_iter().collect()))
            }
        }

        impl<T1: Readable, T2: Readable, T3: Readable, T4: Readable, $u: Readable> ReadableFromLine for (T1, T2, T3, T4, $collection_in)
        where
            <$u as Readable>::Output: Sized $(+ $bound)*
        {
            type Output = (T1::Output, T2::Output, T3::Output, T4::Output, $collection_out);

            fn read_line(line: &str) -> Result<Self::Output, String> {
                let prefix_len = <(T1, T2, T3, T4)>::WORDS_COUNT;
                let words = split_into_words_for_collection::<$u>(line, prefix_len)?;
                let mut start = 0;

                let count1 = T1::WORDS_COUNT;
                let val1 = T1::read_words(&words[start .. start+count1])?;
                start += count1;

                let count2 = T2::WORDS_COUNT;
                let val2 = T2::read_words(&words[start .. start+count2])?;
                start += count2;

                let count3 = T3::WORDS_COUNT;
                let val3 = T3::read_words(&words[start .. start+count3])?;
                start += count3;

                let count4 = T4::WORDS_COUNT;
                let val4 = T4::read_words(&words[start .. start+count4])?;

                let rest = read_words_into_vec::<$u>(&words[prefix_len..], line)?;
                Ok((val1, val2, val3, val4, rest.into_iter().collect()))
            }
        }
    };
}

readable_collection!(U => Vec<U>, Vec<U::Output>);

// Do not provide by default for compilation speedup

// readable_collection!(
//     U => std::collections::VecDeque<U>, std::collections::VecDeque<U::Output>
// );

// readable_collection!(
//     U: Eq, std::hash::Hash => std::collections::HashSet<U>, std::collections::HashSet<U::Output>
// );

// readable_collection!(
//     U: Ord => std::collections::BTreeSet<U>, std::collections::BTreeSet<U::Output>
// );

// readable_collection!(
//     U: Ord => std::collections::BinaryHeap<U>, std::collections::BinaryHeap<U::Output>
// );

/// Returns `Readable`s read from a line of stdin.
///
/// 読み込むことのできる型は、以下の通りである。
///
/// - [`Readable`](trait.Readable.html)をimplした型
/// - [`Readable`](trait.Readable.html)を要素型とするコレクション
/// - コレクションが最後の要素型になっているタプル (eg. `(i32, Vec<i32>)`)
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
/// `=`記号の右側には、[`Readable`](trait.Readable.html)をimplした任意の型を置くことができる。
/// また、最後の型に限り、[`readable_collection`](../macro.readable_collection)マクロで宣言した
/// コレクション型を置くことができる。
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "5 10 20 30 40 50"
/// read!(len = usize, mut nums = Vec<usize>);
/// assert_eq!(len, 5);
/// assert_eq!(nums, vec![1usize, 17, 8, 3, 2, 6]);
/// ```
///
/// *pattern* `=` *type* の代わりに `!` と書くと、その位置のwordを捨てる。
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "10 20"
/// read!(!, k = usize);
/// assert_eq!(k, 20);
/// ```
///
/// 単に`read!()`と書くと、入力の1行を捨てる。
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "5\n10 20 30 40 50"
/// read!();
/// read!(nums = Vec<i32>);
/// assert_eq!(nums, vec![10, 20, 30, 40, 50]);
/// ```
#[macro_export]
macro_rules! read {
    // Discards a line
    () => {
        let mut line = String::new();
        // Can be faster by disabling UTF-8 validation,
        // but keeps it enabled in case of feeding a wrong test case manually.
        std::io::stdin().read_line(&mut line).unwrap();
    };

    // Handles one-pattern case separately because of
    // - avoiding "unnecessaryparentheses" warning
    // - simplifying `read_inner`
    //
    // On Codeforces environment, optional pattern '$(,)?' may not be supported.
    ( $pat:pat = $t:ty $(,)* ) => {
        let $pat = read::<$t>();
    };
    ( ! $(,)* ) => {
        let _ = read::<()>();
    };

    ( $pat:pat = $t:ty, $( $rest:tt )+ ) => {
        read_inner!($pat = $t; $($rest)+);
    };
    ( !, $( $rest:tt )+ ) => {
        read_inner!(_ = (); $($rest)+);
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! read_inner {
    // Processes patterns
    ( $( $acc_pat:pat = $acc_t:ty ),+ ; $pat:pat = $t:ty, $( $rest:tt )* ) => {
        read_inner!($( $acc_pat = $acc_t ),+ , $pat = $t ; $($rest)*);
    };
    ( $( $acc_pat:pat = $acc_t:ty ),+ ; !, $( $rest:tt )* ) => {
        read_inner!($( $acc_pat = $acc_t ),+ , _ = () ; $($rest)*);
    };

    // In case the last assignment has no trailing comma
    ( $( $acc_pat:pat = $acc_t:ty ),+ ; $pat:pat = $t:ty ) => {
        read_inner!($( $acc_pat = $acc_t ),+ , $pat = $t ;);
    };
    ( $( $acc_pat:pat = $acc_t:ty ),+ ; ! ) => {
        read_inner!($( $acc_pat = $acc_t ),+ , _ = () ;);
    };

    // Gets a ReadableFromLine
    ( $( $pat:pat = $t:ty ),+ ; ) => {
        let ($($pat),+) = read::<($($t),+)>();
    };
}

/// Readable by `read_chunk` function/macro.
pub trait ReadableFromChunk {
    type Output;

    fn lines_count() -> usize;

    fn read_chunk(lines: &[String]) -> Result<Self::Output, String>;
}

impl<T1: ReadableFromLine, T2: ReadableFromLine> ReadableFromChunk for (T1, T2) {
    type Output = (T1::Output, T2::Output);

    fn lines_count() -> usize { 2 }

    fn read_chunk(lines: &[String]) -> Result<Self::Output, String> {
        let out1 = T1::read_line(&lines[0])?;
        let out2 = T2::read_line(&lines[1])?;
        Ok((out1, out2))
    }
}

impl<T1: ReadableFromLine, T2: ReadableFromLine, T3: ReadableFromLine> ReadableFromChunk for (T1, T2, T3) {
    type Output = (T1::Output, T2::Output, T3::Output);

    fn lines_count() -> usize { 3 }

    fn read_chunk(lines: &[String]) -> Result<Self::Output, String> {
        let out1 = T1::read_line(&lines[0])?;
        let out2 = T2::read_line(&lines[1])?;
        let out3 = T3::read_line(&lines[2])?;
        Ok((out1, out2, out3))
    }
}

impl<T1: ReadableFromLine, T2: ReadableFromLine, T3: ReadableFromLine, T4: ReadableFromLine> ReadableFromChunk for (T1, T2, T3, T4) {
    type Output = (T1::Output, T2::Output, T3::Output, T4::Output);

    fn lines_count() -> usize { 4 }

    fn read_chunk(lines: &[String]) -> Result<Self::Output, String> {
        let out1 = T1::read_line(&lines[0])?;
        let out2 = T2::read_line(&lines[1])?;
        let out3 = T3::read_line(&lines[2])?;
        let out4 = T4::read_line(&lines[3])?;
        Ok((out1, out2, out3, out4))
    }
}

/// Reads multiple lines from stdin.
pub fn read_chunk<T: ReadableFromChunk>() -> T::Output {
    let stdin = std::io::stdin();
    let mut handle = stdin.lock();
    read_chunk_from_handle::<T>(&mut handle).unwrap()
}

fn read_chunk_from_handle<T: ReadableFromChunk>(handle: &mut std::io::StdinLock) -> Option<T::Output> {
    use std::io::BufRead;

    let mut lines = vec![String::new(); T::lines_count()];
    let mut first = true;
    for line in &mut lines {
        if handle.read_line(line).unwrap() == 0 && first {
            return None;
        }
        first = false;
    }
    Some(T::read_chunk(&lines).unwrap())
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
///     read_chunk!(
///         a = u16,
///         (b, c) = (u16, u16),
///         s = String
///     );
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
/// but using `read_chunk` has some advantages:
///
/// - You don't have to write `read` several times.
/// - `read_chunk` gets the mutex for stdin only once. It makes inputting a little bit faster.
#[macro_export]
macro_rules! read_chunk {
    // Gets ReadableFromLine's
    ( $( $pat:pat = $t:ty ),+ ) => {
        let ($($pat),+) = read_chunk::<($($t),+)>();
    };
}

static mut STDIN: Option<std::io::Stdin> = None;

/// Iterator created by [`read_lines`](fn.read_lines.html) function.
pub struct ReadLines<T: ReadableFromLine> {
    lock: std::io::StdinLock<'static>,
    phantom: std::marker::PhantomData<T>
}

impl<T: ReadableFromLine> Iterator for ReadLines<T> {
    type Item = T::Output;

    fn next(&mut self) -> Option<T::Output> {
        use std::io::BufRead;

        let mut line = String::new();
        if self.lock.read_line(&mut line).unwrap() > 0 {
            Some(T::read_line(&line).unwrap())
        } else {
            None
        }
    }
}

// TODO: Solve ABC118 B
/// Creates an iterator reading stdin line by line.
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
///     yn(check(&read_lines::<String>().collect::<Vec<_>>()));
/// }
/// ```
///
/// You can read only `n` lines by `take` method on the iterator.
///
/// ```no_run
/// # #[macro_use] extern crate atcoder_snippets;
/// # use atcoder_snippets::read::*;
/// // Stdin: "3\n1 10\n2 20\n3 30\n2\n1 10 100\n2 20 200"
/// read!(n = usize);
/// let nums1: Vec<(u8, u8)> = read_lines::<(u8, u8)>().take(n).collect();
/// assert_eq!(nums1, vec![(1, 10), (2, 20), (3, 30)]);
///
/// read!();
/// let nums2: Vec<(u8, u8, u8)> = read_lines::<(u8, u8, u8)>().collect();
/// assert_eq!(nums2, vec![(1, 10, 100), (2, 20, 200)]);
/// ```
///
/// # Deadlock
///
/// `read_lines` gets the mutex for stdin, and release it when the iterator is dropped.
/// So, it causes deadlock to read stdin before the iterator is dropped.
pub fn read_lines<T: ReadableFromLine>() -> ReadLines<T> {
    unsafe {
        if STDIN.is_none() {
            STDIN = Some(std::io::stdin());
        }
    }

    ReadLines {
        lock: unsafe { STDIN.as_ref().unwrap().lock() },
        phantom: std::marker::PhantomData::<T>
    }
}

/// Iterator created by [`read_chunks`](fn.read_chunks.html) function.
pub struct ReadChunks<T: ReadableFromChunk> {
    lock: std::io::StdinLock<'static>,
    phantom: std::marker::PhantomData<T>
}

impl<T: ReadableFromChunk> Iterator for ReadChunks<T> {
    type Item = T::Output;

    fn next(&mut self) -> Option<T::Output> {
        read_chunk_from_handle::<T>(&mut self.lock)
    }
}

/// Creates an iterator reading stdin chunk by chunk.
pub fn read_chunks<T: ReadableFromChunk>() -> ReadChunks<T> {
    unsafe {
        if STDIN.is_none() {
            STDIN = Some(std::io::stdin());
        }
    }

    ReadChunks {
        lock: unsafe { STDIN.as_ref().unwrap().lock() },
        phantom: std::marker::PhantomData::<T>
    }
}

// TODO: parse().unwrap()ではうまくいかない例を示す
/// `Readable`を読み出すことができる型。
///
/// このトレイトにより、`Readable`の実装が簡単になる場合がある。
pub trait Words {
    fn read<T: Readable>(&self) -> T::Output;
}

impl<'a> Words for [&'a str] {
    fn read<T: Readable>(&self) -> T::Output {
        T::read_words(self).unwrap()
    }
}

impl<'a> Words for &'a str {
    fn read<T: Readable>(&self) -> T::Output {
        T::read_words(&[self]).unwrap()
    }
}

// END SNIPPET

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Debug, PartialEq, Eq)]
    struct Pair(i32, i32);

    impl Readable for Pair {
        type Output = Self;
        const WORDS_COUNT: usize = 2;

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
    fn test_read_words_one_origin_integers() {
        assert_eq!(u8_::read_words(&["1"]), Ok(0));
        assert_eq!(u16_::read_words(&["1"]), Ok(0));
        assert_eq!(u32_::read_words(&["1"]), Ok(0));
        assert_eq!(u64_::read_words(&["1"]), Ok(0));
        assert_eq!(usize_::read_words(&["1"]), Ok(0));
    }

    #[test]
    fn test_read_words_custom() {
        assert_eq!(Pair::read_words(&["1", "2"]), Ok(Pair(1, 2)));
    }

    #[test]
    fn test_read_words_tuple_2() {
        type T0 = (char, char);
        assert!(T0::read_words(&["a", "a"]).is_ok());
        type T1 = (Pair, char);
        assert!(T1::read_words(&["10", "10", "a"]).is_ok());
        type T2 = (Pair, Pair);
        assert!(T2::read_words(&["10", "10", "10", "10"]).is_ok());
    }

    #[test]
    fn test_read_words_tuple_3() {
        type T0 = (char, char, char);
        assert!(T0::read_words(&["a", "a", "a"]).is_ok());
        type T1 = (Pair, char, char);
        assert!(T1::read_words(&["10", "10", "a", "a"]).is_ok());
        type T2 = (Pair, Pair, char);
        assert!(T2::read_words(&["10", "10", "10", "10", "a"]).is_ok());
        type T3 = (Pair, Pair, Pair);
        assert!(T3::read_words(&["10", "10", "10", "10", "10", "10"]).is_ok());
    }

    #[test]
    fn test_read_words_tuple_4() {
        type T0 = (char, char, char, char);
        assert!(T0::read_words(&["a", "a", "a", "a"]).is_ok());
        type T1 = (Pair, char, char, char);
        assert!(T1::read_words(&["10", "10", "a", "a", "a"]).is_ok());
        type T2 = (Pair, Pair, char, char);
        assert!(T2::read_words(&["10", "10", "10", "10", "a", "a"]).is_ok());
        type T3 = (Pair, Pair, Pair, char);
        assert!(T3::read_words(&["10", "10", "10", "10", "10", "10", "a"]).is_ok());
        type T4 = (Pair, Pair, Pair, Pair);
        assert!(T4::read_words(&["10", "10", "10", "10", "10", "10", "10", "10"]).is_ok());
    }

    #[test]
    fn test_read_words_tuple_5() {
        type T0 = (char, char, char, char, char);
        assert!(T0::read_words(&["a", "a", "a", "a", "a"]).is_ok());
        type T1 = (Pair, char, char, char, char);
        assert!(T1::read_words(&["10", "10", "a", "a", "a", "a"]).is_ok());
        type T2 = (Pair, Pair, char, char, char);
        assert!(T2::read_words(&["10", "10", "10", "10", "a", "a", "a"]).is_ok());
        type T3 = (Pair, Pair, Pair, char, char);
        assert!(T3::read_words(&["10", "10", "10", "10", "10", "10", "a", "a"]).is_ok());
        type T4 = (Pair, Pair, Pair, Pair, char);
        assert!(T4::read_words(&["10", "10", "10", "10", "10", "10", "10", "10", "a"]).is_ok());
        type T5 = (Pair, Pair, Pair, Pair, Pair);
        assert!(T5::read_words(&["10", "10", "10", "10", "10", "10", "10", "10", "10", "10"]).is_ok());
    }

    #[test]
    fn test_read_words_tuple_6() {
        type T0 = (char, char, char, char, char, char);
        assert!(T0::read_words(&["a", "a", "a", "a", "a", "a"]).is_ok());
        type T1 = (Pair, char, char, char, char, char);
        assert!(T1::read_words(&["10", "10", "a", "a", "a", "a", "a"]).is_ok());
        type T2 = (Pair, Pair, char, char, char, char);
        assert!(T2::read_words(&["10", "10", "10", "10", "a", "a", "a", "a"]).is_ok());
        type T3 = (Pair, Pair, Pair, char, char, char);
        assert!(T3::read_words(&["10", "10", "10", "10", "10", "10", "a", "a", "a"]).is_ok());
        type T4 = (Pair, Pair, Pair, Pair, char, char);
        assert!(T4::read_words(&["10", "10", "10", "10", "10", "10", "10", "10", "a", "a"]).is_ok());
        type T5 = (Pair, Pair, Pair, Pair, Pair, char);
        assert!(T5::read_words(&["10", "10", "10", "10", "10", "10", "10", "10", "10", "10", "a"]).is_ok());
        type T6 = (Pair, Pair, Pair, Pair, Pair, Pair);
        assert!(T6::read_words(&["10", "10", "10", "10", "10", "10", "10", "10", "10", "10", "10", "10"]).is_ok());
    }

    #[test]
    fn test_read_words_array_2 () {
        let val = <[Pair; 2]>::read_words(&["0", "1", "2", "3"]).unwrap();
        assert_eq!(val, [Pair(0, 1), Pair(2, 3)]);
    }

    #[test]
    fn test_read_words_array_3 () {
        let val = <[Pair; 3]>::read_words(&["0", "1", "2", "3", "4", "5"]).unwrap();
        assert_eq!(val, [Pair(0, 1), Pair(2, 3), Pair(4, 5)]);
    }

    #[test]
    fn test_read_words_array_4 () {
        let val = <[Pair; 4]>::read_words(&["0", "1", "2", "3", "4", "5", "6", "7"]).unwrap();
        assert_eq!(val, [Pair(0, 1), Pair(2, 3), Pair(4, 5), Pair(6, 7)]);
    }

    #[test]
    fn test_read_words_array_5 () {
        let val = <[Pair; 5]>::read_words(&["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]).unwrap();
        assert_eq!(val, [Pair(0, 1), Pair(2, 3), Pair(4, 5), Pair(6, 7), Pair(8, 9)]);
    }

    #[test]
    fn test_read_words_array_6 () {
        let val = <[Pair; 6]>::read_words(&["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11"]).unwrap();
        assert_eq!(val, [Pair(0, 1), Pair(2, 3), Pair(4, 5), Pair(6, 7), Pair(8, 9), Pair(10, 11)]);
    }

    #[test]
    fn test_read_words_nested_tuple() {
        assert_eq!(<(i32, (i32, i32), i32)>::read_words(&["1", "2", "3", "4"]),
                   Ok((1, (2, 3), 4)));
    }

    #[test]
    fn test_read_line_vector() {
        assert_eq!(Vec::<i32>::read_line("1 2 3\n"), Ok(vec![1, 2, 3]));
    }

    #[test]
    fn test_read_line_readable_and_vector() {
        assert_eq!(<(char, Vec<i32>)>::read_line("a 10 20"),
                   Ok(('a', vec![10, 20])));
        assert_eq!(<((char, char), Vec<i32>)>::read_line("a b 10 20"),
                   Ok((('a', 'b'), vec![10, 20])));
        assert_eq!(<((char, char), Vec<i32>)>::read_line("a b"),
                   Ok((('a', 'b'), vec![])));
        assert!(<((char, char), Vec<i32>)>::read_line("a").is_err());
    }

    #[test]
    fn test_read_line_2_readables_and_vector() {
        assert_eq!(<(char, char, Vec<i32>)>::read_line("a b 10 20"),
                   Ok(('a', 'b', vec![10, 20])));
        assert_eq!(<(char, char, Vec<i32>)>::read_line("a b"),
                   Ok(('a', 'b', vec![])));
        assert!(<(char, char, Vec<i32>)>::read_line("a").is_err());

        assert!(<(Pair, char, Vec<i32>)>::read_line("10 10 a").is_ok());
        assert!(<(Pair, Pair, Vec<i32>)>::read_line("10 10 10 10").is_ok());
    }

    #[test]
    fn test_read_line_3_readables_and_vector() {
        assert_eq!(<(char, char, char, Vec<i32>)>::read_line("a b c 10 20"),
                   Ok(('a', 'b', 'c', vec![10, 20])));
        assert_eq!(<(char, char, char, Vec<i32>)>::read_line("a b c"),
                   Ok(('a', 'b', 'c', vec![])));
        assert!(<(char, char, char, Vec<i32>)>::read_line("a b").is_err());

        type T1 = (Pair, char, char, Vec<i32>);
        assert!(T1::read_line("10 10 a a").is_ok());
        type T2 = (Pair, Pair, char, Vec<i32>);
        assert!(T2::read_line("10 10 10 10 a").is_ok());
        type T3 = (Pair, Pair, Pair, Vec<i32>);
        assert!(T3::read_line("10 10 10 10 10 10").is_ok());
    }

    #[test]
    fn test_read_line_4_readables_and_vector() {
        assert_eq!(<(char, char, char, char, Vec<i32>)>::read_line("a b c d 10 20"),
                   Ok(('a', 'b', 'c', 'd', vec![10, 20])));
        assert_eq!(<(char, char, char, char, Vec<i32>)>::read_line("a b c d"),
                   Ok(('a', 'b', 'c', 'd', vec![])));
        assert!(<(char, char, char, char, Vec<i32>)>::read_line("a b c").is_err());

        type T1 = (Pair, char, char, char, Vec<i32>);
        assert!(T1::read_line("10 10 a a a").is_ok());
        type T2 = (Pair, Pair, char, char, Vec<i32>);
        assert!(T2::read_line("10 10 10 10 a a").is_ok());
        type T3 = (Pair, Pair, Pair, char, Vec<i32>);
        assert!(T3::read_line("10 10 10 10 10 10 a").is_ok());
        type T4 = (Pair, Pair, Pair, Pair, Vec<i32>);
        assert!(T4::read_line("10 10 10 10 10 10 10 10").is_ok());
    }

    /*
    #[test]
    fn test_read_collections() {
        assert_eq!(VecDeque::<u32_>::read_line("1 2 3 4 5"),
                   Ok((0..5).collect::<VecDeque<_>>()));
        assert_eq!(HashSet::<u32_>::read_line("1 2 3 4 5"),
                   Ok((0..5).collect::<HashSet<_>>()));
        assert_eq!(BTreeSet::<u32_>::read_line("1 2 3 4 5"),
                   Ok((0..5).collect::<BTreeSet<_>>()));
        let mut heap = BinaryHeap::<u32_>::read_line("1 5 2 4 3").unwrap();
        let mut heap_items = Vec::new();
        while let Some(item) = heap.pop() {
            heap_items.push(item);
        }
        assert_eq!(heap_items, (0..5).rev().collect::<Vec<_>>());
    }
    */

    #[test]
    fn test_read_line_vector_of_one_origin_integers() {
        assert_eq!(Vec::<usize_>::read_line("1 2 3\n"), Ok(vec![0, 1, 2]));
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
