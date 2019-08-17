// #![feature(test)]

extern crate criterion;
extern crate atcoder_snippets;

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use atcoder_snippets::z::*;

fn bench_z_match_indices(c: &mut Criterion) {
    let mut text1 = Vec::new();
        for _ in 0..10 {
            text1.extend_from_slice(&[0u8; 999]);
            text1.push(1u8)
        }
    let pattern1 = vec![0u8; 100];
    c.bench_function(
        "Z algorithm with 10^4 text and 10^2 pattern",
        move |b| b.iter(|| {
            text1.z_match_indices(&pattern1).for_each(|_| { black_box(0); })
        })
    );

    let mut text2 = Vec::new();
        for _ in 0..10 {
            text2.extend_from_slice(&[0u8; 9_999]);
            text2.push(1u8)
        }
    let pattern2 = vec![0u8; 1_000];
    c.bench_function(
        "Z algorithm with 10^5 text and 10^3 pattern",
        move |b| b.iter(|| {
            text2.z_match_indices(&pattern2).for_each(|_| { black_box(0); })
        })
    );
}

criterion_group!(benches, bench_z_match_indices);
criterion_main!(benches);
