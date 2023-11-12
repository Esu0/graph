use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use graph::dynamic_tree::splay_tree;

fn bm_nop(c: &mut Criterion) {
    c.bench_function("Nop", |b| {
        let v = splay_tree::bench::gen_tree(1000);
        b.iter(|| splay_tree::bench::bm_nop(&v))
    });
}

fn bm_zig(c: &mut Criterion) {
    c.bench_function("zig action", |b| {
        let v = splay_tree::bench::gen_tree(1000);
        b.iter(|| splay_tree::bench::bm_zig(&v))
    });
}

fn bm_splay(c: &mut Criterion) {
    let mut group = c.benchmark_group("splay action");
    for size in 10..=17 {
        group.throughput(Throughput::Bytes(size));
        group.bench_with_input(
            BenchmarkId::new("node number", 1 << size),
            &(1 << size),
            |b, &size| {
                let v = splay_tree::bench::gen_tree(size);
                b.iter(|| splay_tree::bench::bm_splay(&v))
            },
        );
    }
}
criterion_group!(benches, bm_nop, bm_zig, bm_splay);
criterion_main!(benches);
