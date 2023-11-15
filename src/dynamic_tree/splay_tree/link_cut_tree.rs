use super::{NodePtr, Node};

struct LinkCutTree<K, Op, KeyAdd, Operate, OpAdd, RevOp> {
    root: Option<NodePtr<K, Op>>,
    key_add: KeyAdd,
    operate: Operate,
    op_add: OpAdd,
    rev_op: RevOp,
}

impl<K: Clone, Op: Default + Eq, KeyAdd: Fn(&K, &K) -> K, Operate: Fn(&mut K, &Op, usize), OpAdd: Fn(&mut Op, &Op), RevOp: Fn(&mut K)> LinkCutTree<K, Op, KeyAdd, Operate, OpAdd, RevOp> {
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

        loop {
            // let p = p_ptr.as_mut();
            self.push(p);

            if let Some(d1) = p.which(s_ptr) {
                let Some(gp_ptr) = p.parent else {
                    // zig action
                    p.link_child_tree(x.child(d1.opposite()), d1);
                    self.update(p);
                    x.link_child(p, d1.opposite());
                    x.parent = None;

                    self.update(x);
                    break;
                };
                let gp = gp_ptr.as_mut();
                self.push(gp);
                if let Some(d2) = gp.which(p.into()) {
                    if let Some(ggp_ptr) = gp.parent {
                        // xの次の親はggpであり、次のループでupdateされるので
                        // ggp.update();を実行する必要はない。

                        if d1 == d2 {
                            // zig-zig action
                            gp.link_child_tree(p.child(d1.opposite()), d1);
                            // 上の操作でgp <-> pのリンクが切れる。pのd1の反対方向の子ノードは
                            // xじゃない方の子ノードだから、gpの子ノードの参照は存在しない
                            // gp.update();
                            p.link_child_tree(x.child(d1.opposite()), d1);
                            p.link_child(gp, d1.opposite());
                            // 上の操作でp <-> xのリンクが切れる。ここでgpのライフタイムは終了し、
                            // pの子ノードの参照は存在しなくなる。
                            // p.update();
                            x.link_child(p, d1.opposite());

                            // 次のループにおけるxの親を設定しておく
                            p = ggp_ptr.as_mut();
                            // pのライフタイムが終了、同様の理由でupdateは安全
                        } else {
                            // zig-zag action
                            gp.link_child_tree(x.child(d1), d2);
                            // gp.update();
                            p.link_child_tree(x.child(d2), d1);
                            // p.update();
                            x.link_child(gp, d1);
                            x.link_child(p, d2);
                            p = ggp_ptr.as_mut();
                        }

                        self.update(x);
                        p.cas_child(gp_ptr, s_ptr);
                        x.parent = Some(ggp_ptr);
                    } else {
                        x.parent = None;

                        if d1 == d2 {
                            // zig-zig action
                            gp.link_child_tree(p.child(d1.opposite()), d1);
                            // 上の操作でgp <-> pのリンクが切れる。pのd1の反対方向の子ノードは
                            // xじゃない方の子ノードだから、gpの子ノードの参照は存在しない
                            // gp.update();
                            p.link_child_tree(x.child(d1.opposite()), d1);
                            p.link_child(gp, d1.opposite());
                            // 上の操作でp <-> xのリンクが切れる。ここでgpのライフタイムは終了し、
                            // pの子ノードの参照は存在しなくなる。
                            // p.update();
                            x.link_child(p, d1.opposite());
                            // drop(p);
                            // pのライフタイムが終了、同様の理由でupdateは安全
                        } else {
                            // zig-zag action
                            gp.link_child_tree(x.child(d1), d2);
                            // gp.update();
                            p.link_child_tree(x.child(d2), d1);
                            // p.update();
                            x.link_child(gp, d1);
                            x.link_child(p, d2);
                            // drop(p);
                        }
                        self.update(x);
                        break;
                    }
                } else {
                    // zig action
                    p.link_child_tree(x.child(d1.opposite()), d1);
                    self.update(p);
                    x.parent = p.parent;
                    x.link_child(p, d1.opposite());
                    self.update(x);
                    break;
                }
            } else {
                break;
            }
        }
    }
}
