//! Utility snippets for fighting AtCoder.
//!
//! Use [cargo-snippet](https://github.com/hatoo/cargo-snippet) for copy-and-pasting snippets easily.


#![feature(plugin)]
#![feature(test)]
#![plugin(cargo_snippet)]

#[macro_use] pub mod read;
pub mod write;
pub mod num;
pub mod cmp;
pub mod iter;
pub mod slice;
pub mod collections;
pub mod vec;
pub mod bsearch;
pub mod z;
pub mod rolling_hash;
pub mod utils;
