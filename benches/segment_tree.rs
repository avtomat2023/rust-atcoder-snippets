use std::ops::Range;
use criterion::{Criterion, black_box, criterion_group, criterion_main};
use rand::prelude::*;
use rand_xorshift::XorShiftRng;
use atcoder_snippets::collections::segment_tree::SegmentTree;

fn bench_random_queries(c: &mut Criterion) {
    const ITEM_LEN: usize = 10_000_000;
    let tree = SegmentTree::from_vec(vec![0; ITEM_LEN], 0, |&a, &b| a+b);

    const QUERY_LEN: usize = 10_000;
    let mut rng = XorShiftRng::from_seed(
        [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
         0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]
    );
    let nums: Vec<usize> = (0..QUERY_LEN*2).map(|_| rng.gen::<usize>() % ITEM_LEN).collect();
    let queries: Vec<Range<usize>> = nums.chunks(2).map(|is| is[0]..is[1]).collect();

    c.bench_function(
        "segment_tree: 10^4 queries on a tree with 10^7 items",
        |b| b.iter(|| {
            for query in &queries {
                black_box(tree.query(query.clone()));
            }
        })
    );
}

criterion_group!(
    name = benches;
    config = Criterion::default().sample_size(50);
    targets = bench_random_queries
);
criterion_main!(benches);
