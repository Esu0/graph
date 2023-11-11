use criterion::{criterion_group, criterion_main, Criterion};
use graph::dynamic_tree::splay_tree::{Direction, NodePtr};
use rand::{thread_rng, Rng};

fn gen_tree(n: usize) -> Vec<NodePtr<usize>> {
    let mut v = vec![None; n];
    gen_tree_rec(NodePtr::new(1), n, 1, &mut v);
    v.iter().filter_map(|x| *x).collect()
}

// parent.key == k
fn gen_tree_rec(parent: NodePtr<usize>, n: usize, k: usize, v: &mut Vec<Option<NodePtr<usize>>>) {
    v[k - 1] = Some(parent);
    if k * 2 <= n {
        gen_tree_rec(
            parent.insert(k * 2, Direction::Left, Direction::Left),
            n,
            k * 2,
            v,
        );
        if k * 2 + 1 <= n {
            gen_tree_rec(
                parent.insert(k * 2 + 1, Direction::Right, Direction::Right),
                n,
                k * 2 + 1,
                v,
            );
        }
    }
}

fn bm_nop(c: &mut Criterion) {
    c.bench_function("Nop", |b| {
        let v = gen_tree(1000);
        b.iter(|| {
            let k = thread_rng().gen_range(0..1000);
            if !v[k].is_root() {}
        })
    });
}
fn bm_zig(c: &mut Criterion) {
    c.bench_function("zig action", |b| {
        let v = gen_tree(1000);
        b.iter(|| {
            let k = thread_rng().gen_range(0..1000);
            if !v[k].is_root() {
                v[k].zig();
            }
        })
    });
}

criterion_group!(benches, bm_nop, bm_zig);
criterion_main!(benches);
