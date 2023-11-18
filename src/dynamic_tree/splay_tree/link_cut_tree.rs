use crate::graph::traits;

use super::{Node, NodePtr};

struct LinkCutTree<K, Op, KeyAdd, Operate, OpAdd, RevOp> {
    root: Vec<NodePtr<K, Op>>,
    key_add: KeyAdd,
    operate: Operate,
    op_add: OpAdd,
    rev_op: RevOp,
}

impl<
        K: Clone,
        Op: Default + Eq,
        KeyAdd: Fn(&K, &K) -> K,
        Operate: Fn(&mut K, &Op, usize),
        OpAdd: Fn(&mut Op, &Op),
        RevOp: Fn(&mut K),
    > LinkCutTree<K, Op, KeyAdd, Operate, OpAdd, RevOp>
{
    pub fn new<Idx: Copy, T: crate::graph::traits::MarkedTree<Idx, K>>(
        tree: &T,
        key_add: KeyAdd,
        operate: Operate,
        op_add: OpAdd,
        rev_op: RevOp,
    ) -> Self {
        let mut roots = vec![];
        if let Some(root) = tree.root() {
            let mut stack: Vec<(Option<NodePtr<K, Op>>, Idx)> = vec![(None, root)];
            while let Some((p, idx)) = stack.pop() {
                let node: NodePtr<_, Op> = NodePtr::new(tree.marker(idx).clone());
                let mut nodes: [_; 64] = std::array::from_fn(|_| None);
                let mut i: u32 = 1;
                nodes[0] = Some(node.as_mut());
                let mut children = tree.children(idx);
                while let Some(child) = children.next() {
                    stack.extend(std::iter::repeat(Some(node)).zip(children));
                    let node_ptr =
                        NodePtr::from_key_and_edges(tree.marker(child).clone(), None, None, None);

                    let j = i.trailing_ones() as usize;
                    let node = node.as_mut();
                    if let Some(child) = nodes.get_mut(j.wrapping_sub(1)).map(|x| x.take().unwrap())
                    {
                        node.left = Some(child.into());
                        child.parent = Some(node_ptr);
                        debug_assert!(node.right.is_none());
                        // 修正箇所: nodes[0]がsomeかどうかは確定しない
                        let mut before = &*nodes[0].take().unwrap();
                        nodes[1..j.wrapping_sub(1)].iter_mut().for_each(|n| {
                            let n = n.take().unwrap();
                            n.sum = key_add(&n.sum, &before.sum);
                            n.size += before.size;
                            before = n;
                        });
                        child.sum = key_add(&child.sum, &before.sum);
                        child.size += before.size;
                        node.sum = key_add(&child.sum, &node.key);
                        node.size = child.size + 1;
                    } else {
                        node.sum = node.key.clone();
                    }
                    if let Some(Some(parent)) = nodes.get_mut(j + 1) {
                        parent.right = Some(node_ptr);
                        node.parent = Some((*parent).into());
                    }
                    nodes[j] = Some(node);

                    children = tree.children(child);
                    i += 1;
                }
                let mut itr = nodes.iter_mut().filter_map(|x| x.take());
                if let Some(mut root) = itr.next() {
                    itr.for_each(|x| {
                        x.right = Some(root.into());
                        x.sum = key_add(&x.sum, &root.sum);
                        x.size += root.size;
                        root = x;
                    });
                    root.parent = p;
                    roots.push(root.into());
                }
            }
        }
        Self {
            root: roots,
            key_add,
            operate,
            op_add,
            rev_op,
        }
    }

    fn expose(&self, x: &mut Node<K, Op>) -> NodePtr<K, Op> {
        self.splay(x);
        x.right = None;
        let mut p = NodePtr::from(&*x);

        while let Some(c_ptr) = p.as_ref().parent {
            let c = c_ptr.as_mut();
            self.splay(x);
            c.right = Some(p);
            self.update(c);
            p = c_ptr;
        }
        self.splay(x);
        return p;
    }

    /// 子が変わったタイミングで実行
    /// # Safety
    /// * 自身の子ノードの参照が他に存在しない
    fn update(&self, x: &mut Node<K, Op>) {
        x.sum = x.key.clone();
        x.size = 1;
        if let Some(l) = x.left.map(NodePtr::as_ref) {
            x.size += l.size;
            x.sum = (self.key_add)(&l.sum, &x.key);
        }
        if let Some(r) = x.right.map(NodePtr::as_ref) {
            x.size += r.size;
            x.sum = (self.key_add)(&x.sum, &r.sum);
        }
    }

    /// # Safety
    /// * 木に含まれるノードの参照が存在しない
    /// * 自身の左の子ノードが存在する
    fn cut(&self, x: &mut Node<K, Op>) {
        self.expose(x);
        let l = unsafe {
            let l = x.left.take();
            debug_assert!(l.is_some());
            l.unwrap_unchecked()
        };
        l.as_mut().parent = None;
    }

    /// # Safety
    /// * 自身の子ノードの参照が他に存在しない
    fn evert(&mut self, x: &mut Node<K, Op>) {
        self.expose(x);
        std::mem::swap(&mut x.left, &mut x.right);
        if let Some(l) = x.left {
            self.toggle(l.as_mut());
        }
        if let Some(r) = x.right {
            self.toggle(r.as_mut());
        }
    }

    fn link(&mut self, child: &mut Node<K, Op>, parent: &mut Node<K, Op>) {
        self.expose(child);
        self.expose(parent);
        child.parent = Some(parent.into());
        parent.right = Some(child.into());
    }

    fn toggle(&self, x: &mut Node<K, Op>) {
        debug_assert!(!x.rev);
        x.rev = true;
        (self.rev_op)(&mut x.sum);
        std::mem::swap(&mut x.left, &mut x.right);
    }

    /// # Safety
    /// * 自身の子ノードの参照が他に存在しない
    fn push(&self, x: &mut Node<K, Op>) {
        let def = Op::default();
        if x.op != def {
            if let Some(l) = x.left {
                self.propergate(l.as_mut(), &x.op);
            }
            if let Some(r) = x.right {
                self.propergate(r.as_mut(), &x.op);
            }
            x.op = def;
        }
        if x.rev {
            x.rev = false;
            if let Some(l) = x.left {
                self.toggle(l.as_mut());
            }
            if let Some(r) = x.right {
                self.toggle(r.as_mut());
            }
        }
    }

    fn push_manual_child(
        &self,
        p: &mut Node<K, Op>,
        ch1: Option<&mut Node<K, Op>>,
        ch2: Option<&mut Node<K, Op>>,
    ) {
        let def = Op::default();
        match (ch1, ch2) {
            (Some(c1), Some(c2)) => {
                if p.op != def {
                    self.propergate(c1, &p.op);
                    self.propergate(c2, &p.op);
                }
                if p.rev {
                    self.toggle(c1);
                    self.toggle(c2);
                }
            }
            (Some(c1), None) => {
                if p.op != def {
                    self.propergate(c1, &p.op);
                }
                if p.rev {
                    self.toggle(c1);
                }
            }
            (None, Some(c2)) => {
                if p.op != def {
                    self.propergate(c2, &p.op);
                }
                if p.rev {
                    self.toggle(c2);
                }
            }
            (None, None) => {}
        }
        p.op = def;
        p.rev = false;
    }

    fn propergate(&self, x: &mut Node<K, Op>, op: &Op) {
        (self.op_add)(&mut x.op, op);
        (self.operate)(&mut x.key, &x.op, 1);
        (self.operate)(&mut x.sum, &x.op, x.size);
    }

    /// # Safety
    /// * 基本的に木に含まれるノードの参照は存在してはいけないが、
    /// 自身の孫以下の参照は存在してもOK
    fn splay(&self, x: &mut Node<K, Op>) {
        self.push(x);
        let s_ptr = NodePtr::from(&*x);
        let Some(mut p) = x.parent.map(NodePtr::as_mut) else {
            return;
        };
        let mut next_d = p.which(s_ptr);

        loop {
            if let Some(d1) = next_d {
                // self.push(p);
                let Some(gp_ptr) = p.parent else {
                    self.push_manual_child(p, Some(x), p.child(d1.opposite()).map(NodePtr::as_mut));
                    self.push(x);
                    // zig action
                    p.link_child_tree(x.child(d1.opposite()), d1);
                    self.update(p);
                    x.link_child(p, d1.opposite());
                    x.parent = None;

                    self.update(x);
                    break;
                };
                let gp = gp_ptr.as_mut();
                // gp.push();
                if let Some(d2) = gp.which(p.into()) {
                    if let Some(ggp_ptr) = gp.parent {
                        self.push_manual_child(
                            gp,
                            Some(p),
                            gp.child(d2.opposite()).map(NodePtr::as_mut),
                        );
                        self.push_manual_child(
                            p,
                            Some(x),
                            p.child(d1.opposite()).map(NodePtr::as_mut),
                        );
                        self.push(x);
                        // xの次の親はggpであり、次のループでupdateされるので
                        // ggp.update();を実行する必要はない。

                        if d1 == d2 {
                            // zig-zig action
                            gp.link_child_tree(p.child(d1.opposite()), d1);
                            // 上の操作でgp <-> pのリンクが切れる。pのd1の反対方向の子ノードは
                            // xじゃない方の子ノードだから、gpの子ノードの参照は存在しない
                            self.update(gp);
                            p.link_child_tree(x.child(d1.opposite()), d1);
                            p.link_child(gp, d1.opposite());
                            // 上の操作でp <-> xのリンクが切れる。ここでgpのライフタイムは終了し、
                            // pの子ノードの参照は存在しなくなる。
                            self.update(p);
                            x.link_child(p, d1.opposite());

                            // pのライフタイムが終了、同様の理由でupdateは安全
                            self.update(x);
                        } else {
                            // zig-zag action
                            gp.link_child_tree(x.child(d1), d2);
                            self.update(gp);
                            p.link_child_tree(x.child(d2), d1);
                            self.update(p);
                            x.link_child(gp, d1);
                            x.link_child(p, d2);
                            self.update(x);
                        }

                        p = ggp_ptr.as_mut();
                        next_d = p.which(gp_ptr);
                        // p.cas_child(gp_ptr, s_ptr);
                        // x.parent = Some(ggp_ptr);
                    } else {
                        self.push_manual_child(
                            p,
                            Some(x),
                            p.child(d1.opposite()).map(NodePtr::as_mut),
                        );
                        self.push(x);
                        x.parent = None;

                        if d1 == d2 {
                            // zig-zig action
                            gp.link_child_tree(p.child(d1.opposite()), d1);
                            // 上の操作でgp <-> pのリンクが切れる。pのd1の反対方向の子ノードは
                            // xじゃない方の子ノードだから、gpの子ノードの参照は存在しない
                            self.update(gp);
                            p.link_child_tree(x.child(d1.opposite()), d1);
                            p.link_child(gp, d1.opposite());
                            // 上の操作でp <-> xのリンクが切れる。ここでgpのライフタイムは終了し、
                            // pの子ノードの参照は存在しなくなる。
                            self.update(p);
                            x.link_child(p, d1.opposite());
                            // drop(p);
                            // pのライフタイムが終了、同様の理由でupdateは安全
                            self.update(x);
                        } else {
                            // zig-zag action
                            gp.link_child_tree(x.child(d1), d2);
                            self.update(gp);
                            p.link_child_tree(x.child(d2), d1);
                            self.update(p);
                            x.link_child(gp, d1);
                            x.link_child(p, d2);
                            // drop(p);
                            self.update(x);
                        }

                        break;
                    }
                } else {
                    self.push_manual_child(p, Some(x), p.child(d1.opposite()).map(NodePtr::as_mut));
                    self.push(x);
                    // zig action
                    p.link_child_tree(x.child(d1.opposite()), d1);
                    self.update(p);
                    x.parent = p.parent;
                    x.link_child(p, d1.opposite());
                    self.update(x);
                    break;
                }
            } else {
                x.parent = Some(p.into());
                break;
            }
        }
    }
}

struct IndexedTree<T> {
    nodes: Vec<T>,
    childs: Vec<Vec<usize>>,
}

impl<T> traits::Tree<usize> for IndexedTree<T> {
    fn root(&self) -> Option<usize> {
        Some(0)
    }

    fn children(&self, n: usize) -> impl Iterator<Item = usize> {
        self.childs
            .get(n)
            .map(|x| x.iter().copied())
            .unwrap_or_default()
    }
}

impl<T> traits::Graph<usize> for IndexedTree<T> {
    fn adjacency(&self, v: usize) -> impl Iterator<Item = usize> {
        <Self as traits::Tree<_>>::children(self, v)
    }
}

impl<T> traits::MarkedGraph<usize, T> for IndexedTree<T> {
    fn marker(&self, v: usize) -> &T {
        &self.nodes[v]
    }

    fn marker_mut(&mut self, v: usize) -> &mut T {
        &mut self.nodes[v]
    }
}

impl<T> traits::MarkedTree<usize, T> for IndexedTree<T> {}

#[cfg(test)]
mod test {
    use std::vec;

    #[allow(unused_imports)]
    use super::*;
    use std::fmt::Write;

    #[test]
    fn link_cut_tree_build() {
        let tree = IndexedTree {
            nodes: vec![0, 1, 2, 3, 4, 5, 6, 7],
            childs: vec![vec![1, 2], vec![3, 4], vec![5, 6]],
        };
        let lct = LinkCutTree::new(
            &tree,
            |x, y| x + y,
            |x, y: &i32, z| *x += z as i32 * *y,
            |x, y| *x += *y,
            |_| {},
        );
        for root in lct.root {
            root.tree().display_manual(|s, n| write!(s, "{}", n.sum));
        }
    }
}
