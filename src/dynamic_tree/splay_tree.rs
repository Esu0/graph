#![allow(dead_code)]
pub mod link_cut_tree;

use std::{
    fmt::{self, Debug, Display},
    ptr::NonNull,
};


#[derive(Eq)]
enum Tree<K, Op> {
    Null,
    Root(NonNull<Node<K, Op>>),
}

impl<K, Op> From<Tree<K, Op>> for Option<NodePtr<K, Op>> {
    fn from(value: Tree<K, Op>) -> Self {
        match value {
            Tree::Null => None,
            Tree::Root(n) => Some(NodePtr(n)),
        }
    }
}

impl<K: PartialEq, Op> PartialEq for Tree<K, Op> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Tree::Null, Tree::Null) => true,
            (Tree::Root(l), Tree::Root(r)) => unsafe {
                let (l, r) = (l.as_ref(), r.as_ref());
                l.key == r.key
                    && Tree::from(l.left) == Tree::from(r.left)
                    && Tree::from(l.right) == Tree::from(r.right)
            },
            _ => false,
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
struct Node<K, Op> {
    left: Option<NodePtr<K, Op>>,
    right: Option<NodePtr<K, Op>>,
    parent: Option<NodePtr<K, Op>>,
    key: K,
    sum: K,
    op: Op,
    size: usize,
    /// 左の子と右の子が反転されているか
    rev: bool,
}

#[derive(Eq)]
pub struct NodePtr<K, Op>(NonNull<Node<K, Op>>);

impl<K, Op> PartialEq for NodePtr<K, Op> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K, Op> Clone for NodePtr<K, Op> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, Op> Copy for NodePtr<K, Op> {}

impl<K, Op> Tree<K, Op> {
    const fn new() -> Self {
        Self::Null
    }

    fn option(&self) -> Option<NodePtr<K, Op>> {
        self.clone_shallow().into()
    }

    fn clone_shallow(&self) -> Self {
        match self {
            Self::Null => Self::Null,
            Self::Root(n) => Self::Root(*n),
        }
    }

    fn from_option(option: Option<NodePtr<K, Op>>) -> Self {
        match option {
            Some(n) => Tree::Root(n.0),
            None => Tree::Null,
        }
    }

    fn search_dfs(&self, key: &K) -> Option<NodePtr<K, Op>>
    where
        K: Eq,
    {
        if let Some(root) = self.option() {
            let mut stack: Vec<NodePtr<K, Op>> = vec![root];
            while let Some(n_ptr) = stack.pop() {
                let mut n = n_ptr.as_ref();
                if &n.key == key {
                    return Some(n_ptr);
                } else {
                    if let Some(right) = n.child(Direction::Right) {
                        stack.push(right);
                    }
                    while let Some(left) = n.child(Direction::Left) {
                        n = left.as_ref();
                        if &n.key == key {
                            return Some(left);
                        } else {
                            if let Some(r) = n.child(Direction::Right) {
                                stack.push(r);
                            }
                        }
                    }
                }
            }
            None
        } else {
            None
        }
    }

    fn search_bfs(&self, key: &K) -> Option<NodePtr<K, Op>>
    where
        K: Eq,
    {
        if let Some(root) = self.option() {
            let mut queue = std::collections::VecDeque::from([root]);
            while let Some(n_ptr) = queue.pop_front() {
                let n = n_ptr.as_ref();
                if &n.key == key {
                    return Some(n_ptr);
                } else {
                    if let Some(l) = n.child(Direction::Left) {
                        queue.push_back(l);
                    }
                    if let Some(r) = n.child(Direction::Right) {
                        queue.push_back(r);
                    }
                }
            }
            None
        } else {
            None
        }
    }

    fn fmt_rec(&self, f: &mut fmt::Formatter, level: usize) -> fmt::Result
    where
        K: Display,
    {
        if let Some(s) = self.option() {
            Self::from_option(s.as_ref().left).fmt_rec(f, level + 1)?;
            writeln!(f, "{}{}", "\t".repeat(level), s.as_ref().key)?;
            Self::from_option(s.as_ref().right).fmt_rec(f, level + 1)?;
        }
        Ok(())
    }

    fn fmt_debug_rec(&self, f: &mut fmt::Formatter) -> fmt::Result
    where
        K: Debug,
    {
        if let Some(s) = self.option() {
            write!(f, "{{{:?}, parent: ", s.as_ref().key)?;
            if let Some(p) = s.as_ref().parent {
                write!(f, "{:?}", p.as_ref().key)?;
            } else {
                write!(f, "null")?;
            }
            write!(f, ", left: ")?;
            Self::from_option(s.as_ref().left).fmt_debug_rec(f)?;
            write!(f, ", right: ")?;
            Self::from_option(s.as_ref().right).fmt_debug_rec(f)?;
            write!(f, "}}")
        } else {
            write!(f, "null")
        }
    }
}

impl<K, Op> Node<K, Op> {
    /// # Safety
    /// `self`の親ノードへの可変参照が他に存在しない
    fn is_root(&self) -> bool {
        match self.parent {
            None => true,
            Some(p) => p.as_ref().which(self.into()).is_none(),
        }
    }

    fn new_ptr(key: K) -> NonNull<Self>
    where
        K: Clone,
        Op: Default,
    {
        Box::leak(Box::new(Self {
            left: None,
            right: None,
            parent: None,
            sum: key.clone(),
            key,
            op: Op::default(),
            size: 1,
            rev: false,
        }))
        .into()
    }

    /// # Safety
    /// `self.left != self.right || (self.left == None && self.right == None)`
    fn which(&self, child: NodePtr<K, Op>) -> Option<Direction> {
        if self.left == Some(child) {
            Some(Direction::Left)
        } else if self.right == Some(child) {
            Some(Direction::Right)
        } else {
            None
        }
    }

    fn child(&self, dir: Direction) -> Option<NodePtr<K, Op>> {
        if let Direction::Left = dir {
            self.left
        } else {
            self.right
        }
    }

    fn replace_child(&mut self, dir: Direction, child: Option<NodePtr<K, Op>>) -> Option<NodePtr<K, Op>> {
        match dir {
            Direction::Left => std::mem::replace(&mut self.left, child),
            Direction::Right => std::mem::replace(&mut self.right, child),
        }
    }

    fn child_mut(&mut self, dir: Direction) -> &mut Option<NodePtr<K, Op>> {
        match dir {
            Direction::Left => &mut self.left,
            Direction::Right => &mut self.right,
        }
    }

    /// # Safety
    /// `self`の左の子ノードへの参照が他に存在しない
    pub fn insert_left(&mut self, key: K, child_dir: Direction) -> NodePtr<K, Op>
    where
        K: Clone,
        Op: Default,
    {
        let l = self.left;
        let new_node = match child_dir {
            Direction::Left => NodePtr::from_key_and_edges(key, l, None, Some(self.into())),
            Direction::Right => NodePtr::from_key_and_edges(key, None, l, Some(self.into())),
        };
        self.left = Some(new_node);
        if let Some(l) = l.map(NodePtr::as_mut) {
            l.parent = Some(new_node);
        }
        new_node
    }

    /// # Safety
    /// `self`の右の子ノードへの参照が他に存在しない
    pub fn insert_right(&mut self, key: K, child_dir: Direction) -> NodePtr<K, Op>
    where
        K: Clone,
        Op: Default,
    {
        let r = self.right;
        let new_node = match child_dir {
            Direction::Left => NodePtr::from_key_and_edges(key, r, None, Some(self.into())),
            Direction::Right => NodePtr::from_key_and_edges(key, None, r, Some(self.into())),
        };
        self.right = Some(new_node);
        if let Some(r) = r.map(NodePtr::as_mut) {
            r.parent = Some(new_node);
        }
        new_node
    }

    /// # Safety
    /// `self`の`dir`の方向の子ノードへの参照が他に存在しない
    pub fn insert(&mut self, key: K, dir: Direction, child_dir: Direction) -> NodePtr<K, Op>
    where
        K: Clone,
        Op: Default,
    {
        match dir {
            Direction::Left => self.insert_left(key, child_dir),
            Direction::Right => self.insert_right(key, child_dir),
        }
    }

    /// `self` <-> `child`のリンクを行う。
    fn link_child<'a, 'b>(&'a mut self, child: &'a mut Self, dir: Direction) {
        self.replace_child(dir, Some(child.into()));
        child.parent = Some(self.into());
    }

    /// `self` <-> `child`のリンクを行う。
    /// `child`が存在しない場合は、`self`の`dir`の方向の子ノードが存在しなくなる
    /// # Safety
    /// `child`が指すノードへの参照が他に存在しない
    fn link_child_tree(&mut self, child: Option<NodePtr<K, Op>>, dir: Direction) {
        self.replace_child(dir, child);
        if let Some(child) = child.map(NodePtr::as_mut) {
            child.parent = Some(self.into());
        }
    }

    /// # Safety
    /// `self.left != self.right || (self.left == None && self.right == None)`
    fn cas_child(&mut self, old: NodePtr<K, Op>, new: NodePtr<K, Op>) -> bool {
        if let Some(d) = self.which(old) {
            self.replace_child(d, Some(new));
            true
        } else {
            false
        }
    }

    fn cas_child_with(
        &mut self,
        old: NodePtr<K, Op>,
        f: impl FnOnce(Direction) -> Option<NodePtr<K, Op>>,
    ) -> bool {
        if let Some(d) = self.which(old) {
            self.replace_child(d, f(d));
            true
        } else {
            false
        }
    }
    fn from_raw_parts(
        key: K,
        sum: K,
        op: Op,
        size: usize,
        left: Option<NodePtr<K, Op>>,
        right: Option<NodePtr<K, Op>>,
        parent: Option<NodePtr<K, Op>>,
        rev: bool,
    ) -> NonNull<Self> {
        Box::leak(Box::new(Self {
            left,
            right,
            parent,
            key,
            sum,
            op,
            size,
            rev,
        }))
        .into()
    }

    /// # Safety
    /// * 基本的に木に含まれるノードの参照は存在してはいけないが、
    /// 自身の孫以下の参照は存在してもOK
    fn splay(&mut self) {
        // self.push();
        let s_ptr = NodePtr::from(&*self);
        let Some(mut p) = self.parent.map(NodePtr::as_mut) else {
            return;
        };

        loop {
            // let p = p_ptr.as_mut();
            // p.push();

            if let Some(d1) = p.which(s_ptr) {
                let Some(gp_ptr) = p.parent else {
                    // zig action
                    p.link_child_tree(self.child(d1.opposite()), d1);
                    // p.update();
                    self.link_child(p, d1.opposite());
                    self.parent = None;

                    // self.update();
                    break;
                };
                let gp = gp_ptr.as_mut();
                // gp.push();
                if let Some(d2) = gp.which(p.into()) {
                    if let Some(ggp_ptr) = gp.parent {
                        // selfの次の親はggpであり、次のループでupdateされるので
                        // ggp.update();を実行する必要はない。

                        if d1 == d2 {
                            // zig-zig action
                            gp.link_child_tree(p.child(d1.opposite()), d1);
                            // 上の操作でgp <-> pのリンクが切れる。pのd1の反対方向の子ノードは
                            // selfじゃない方の子ノードだから、gpの子ノードの参照は存在しない
                            // gp.update();
                            p.link_child_tree(self.child(d1.opposite()), d1);
                            p.link_child(gp, d1.opposite());
                            // 上の操作でp <-> selfのリンクが切れる。ここでgpのライフタイムは終了し、
                            // pの子ノードの参照は存在しなくなる。
                            // p.update();
                            self.link_child(p, d1.opposite());

                            // 次のループにおけるselfの親を設定しておく
                            p = ggp_ptr.as_mut();
                            // pのライフタイムが終了、同様の理由でupdateは安全
                            // self.update();
                        } else {
                            // zig-zag action
                            gp.link_child_tree(self.child(d1), d2);
                            // gp.update();
                            p.link_child_tree(self.child(d2), d1);
                            // p.update();
                            self.link_child(gp, d1);
                            self.link_child(p, d2);
                            p = ggp_ptr.as_mut();
                            // self.update();
                        }

                        p.cas_child(gp_ptr, s_ptr);
                        self.parent = Some(ggp_ptr);
                    } else {
                        self.parent = None;

                        if d1 == d2 {
                            // zig-zig action
                            gp.link_child_tree(p.child(d1.opposite()), d1);
                            // 上の操作でgp <-> pのリンクが切れる。pのd1の反対方向の子ノードは
                            // selfじゃない方の子ノードだから、gpの子ノードの参照は存在しない
                            // gp.update();
                            p.link_child_tree(self.child(d1.opposite()), d1);
                            p.link_child(gp, d1.opposite());
                            // 上の操作でp <-> selfのリンクが切れる。ここでgpのライフタイムは終了し、
                            // pの子ノードの参照は存在しなくなる。
                            // p.update();
                            self.link_child(p, d1.opposite());
                            // drop(p);
                            // pのライフタイムが終了、同様の理由でupdateは安全
                            // self.update();
                        } else {
                            // zig-zag action
                            gp.link_child_tree(self.child(d1), d2);
                            // gp.update();
                            p.link_child_tree(self.child(d2), d1);
                            // p.update();
                            self.link_child(gp, d1);
                            self.link_child(p, d2);
                            // drop(p);
                            // self.update();
                        }

                        break;
                    }
                } else {
                    // zig action
                    p.link_child_tree(self.child(d1.opposite()), d1);
                    self.parent = p.parent;
                    self.link_child(p, d1.opposite());
                    break;
                }
            } else {
                break;
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Direction {
    Left,
    Right,
}

impl Direction {
    fn opposite(self) -> Self {
        match self {
            Self::Left => Self::Right,
            Self::Right => Self::Left,
        }
    }
}

impl<'a, K, Op> From<&'a mut Node<K, Op>> for NodePtr<K, Op> {
    fn from(value: &'a mut Node<K, Op>) -> Self {
        Self(NonNull::from(value))
    }
}

impl<'a, K, Op> From<&'a Node<K, Op>> for NodePtr<K, Op> {
    fn from(value: &'a Node<K, Op>) -> Self {
        Self(NonNull::from(value))
    }
}

impl<K, Op> From<Option<NodePtr<K, Op>>> for Tree<K, Op> {
    fn from(value: Option<NodePtr<K, Op>>) -> Self {
        Self::from_option(value)
    }
}

impl<K, Op> NodePtr<K, Op> {
    fn new(key: K) -> Self
    where
        K: Clone,
        Op: Default,
    {
        Self(Node::new_ptr(key))
    }

    fn from_key_and_edges(key: K, left: Option<NodePtr<K, Op>>, right: Option<NodePtr<K, Op>>, parent: Option<NodePtr<K, Op>>) -> Self
    where
        K: Clone,
        Op: Default,
    {
        Self::from_raw_parts(key.clone(), key, Op::default(), 1, left, right, parent, false)
    }

    fn from_raw_parts(
        key: K,
        sum: K,
        op: Op,
        size: usize,
        left: Option<NodePtr<K, Op>>,
        right: Option<NodePtr<K, Op>>,
        parent: Option<NodePtr<K, Op>>,
        rev: bool,
    ) -> Self {
        Self(Node::from_raw_parts(key, sum, op, size, left, right, parent, rev))
    }

    fn insert(self, key: K, dir: Direction, child_dir: Direction) -> Self
    where
        K: Clone,
        Op: Default,
    {
        self.as_mut().insert(key, dir, child_dir)
    }

    fn is_root(self) -> bool {
        self.as_ref().is_root()
    }

    fn as_mut<'a>(mut self) -> &'a mut Node<K, Op> {
        unsafe { self.0.as_mut() }
    }

    fn as_ref<'a>(self) -> &'a Node<K, Op> {
        unsafe { self.0.as_ref() }
    }

    /// # Safety
    /// * 親ノードが存在する
    /// * selfの親ノードへの参照が他に存在しない
    /// * selfの子ノードへの参照が他に存在しない
    /// * selfの兄弟ノードへの参照が他に存在しない
    /// * selfの親の親ノードへの参照が他に存在しない
    /// * 自身のノードへの参照が他に存在しない
    fn zig(self) {
        let s = self.as_mut();
        let p_ptr = {
            debug_assert!(s.parent.is_some());
            unsafe { s.parent.unwrap_unchecked() }
        };

        let p = p_ptr.as_mut();
        let gp = p.parent;
        // debug_assert!(self != p_ptr && Some(p_ptr) != gp && Some(self) != gp);
        gp.map(|gp| gp.as_mut().cas_child(p_ptr, self));
        s.parent = gp;

        if let Some(d) = p.which(self) {
            let child = s.child(d.opposite());
            s.link_child(p, d.opposite());
            // *s.child_mut(d) = Some(p_ptr);
            p.link_child_tree(child, d);
        }
    }

    /// # Safety
    /// * 親ノードとその親ノードが存在する
    /// * 親の親ノードのdirの方向の子ノードが自身の親ノードであり、
    /// 自身の親ノードのdirの方向の子ノードが自身である
    fn zig_zig(self, dir: Direction) {
        let s = self.as_mut();
        let p_ptr = unsafe {
            debug_assert!(s.parent.is_some());
            s.parent.unwrap_unchecked()
        };
        let p = p_ptr.as_mut();
        let gp_ptr = unsafe {
            debug_assert!(p.parent.is_some());
            p.parent.unwrap_unchecked()
        };
        let gp = gp_ptr.as_mut();
        let ggp = gp.parent;
        if let Some(ggp) = ggp {
            ggp.as_mut().link_child(s, dir);
        }
        p.link_child_tree(s.child(dir.opposite()), dir);
        gp.link_child_tree(p.child(dir.opposite()), dir);
        s.link_child(p, dir.opposite());
        p.link_child(gp, dir.opposite());
    }

    /// # Safety
    /// * 基本的に木に含まれるノードの参照は存在してはいけないが、
    /// 自身の孫以下の参照は存在してもOK
    fn splay(self) {
        self.as_mut().splay();
    }

    fn tree(self) -> Tree<K, Op> {
        self.into()
    }

    fn drop_node(self) {
        unsafe { drop(Box::from_raw(self.0.as_ptr())) }
    }

    // fn expose(self) {
    //     self.splay();
    //     self.as_mut().right = None;
    //     {
    //         let mut p = self;

    //         while let Some(c) = p.as_ref().parent {
    //             c.splay();
    //             c.as_mut().right = Some(p);
    //             p = c;
    //         }
    //     }
    //     self.splay();
    // }
}

impl<K, Op> From<NodePtr<K, Op>> for Tree<K, Op> {
    fn from(value: NodePtr<K, Op>) -> Self {
        Tree::Root(value.0)
    }
}

impl<K: Display, Op> Display for Tree<K, Op> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_rec(f, 0)
    }
}

impl<K: Debug, Op> Debug for Tree<K, Op> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_debug_rec(f)?;
        writeln!(f)
    }
}

enum TreeGenerator<K> {
    Child(K),
    Parent(K),
    Null,
}

fn gen_tree<K: Clone>(struc: Vec<TreeGenerator<K>>) -> Option<NodePtr<K, ()>> {
    let mut stack = vec![];
    for s in struc {
        match s {
            TreeGenerator::Child(k) => {
                stack.push(Some(NodePtr::new(k)));
            }
            TreeGenerator::Parent(k) => {
                let r = stack.pop().expect("invalid tree structure");
                let l = stack.pop().expect("invalid tree structure");
                let n = NodePtr::from_key_and_edges(k, l, r, None);
                if let Some(l) = l {
                    l.as_mut().parent = Some(n);
                }
                if let Some(r) = r {
                    r.as_mut().parent = Some(n);
                }
                stack.push(Some(n));
            }
            TreeGenerator::Null => {
                stack.push(None);
            }
        }
    }
    assert!(stack.len() == 1, "invalid tree structure");
    stack.pop().flatten()
}

// macro_rules! tree_rec {
//     () => {
//         None
//     };
//     ($e:expr, $($e1:expr),* ; $($($e2:expr),+);+) => {
//         stack.push($e.map(|k| NodePtr::new(k)));
//         tree_rec!($($e1),* ; $($($e2),+);+)
//     };
//     (; $e:expr, $($e1:expr),* ; $($($e2:expr),+);+) => {

//         let l= stack.pop().flatten();
//         let r= stack.pop().flatten();
//         let n = NodePtr::from_raw_parts($e, l, r, None);
//         if let Some(l) = l {
//             l.as_mut().parent = Some(n);
//         }
//         if let Some(r) = r {
//             r.as_mut().parent = Some(n);
//         }
//         stack.push(Some(n));

//     }
// }

// macro_rules! tree {
//     () => {
//         tree_rec!()
//     };
//     // ($($e:expr),+) => {

//     // };
//     ($($($e:expr),+);*) => {
//         {
//             let mut stack: Vec<Option<NodePtr<_>>> = vec![];
//             tree_rec!($($($e),+);*)
//         }
//     }
// }

pub mod bench {
    use super::*;
    use rand::Rng;

    pub struct NodeList<K, Op>(Vec<NodePtr<K, Op>>);

    pub fn gen_tree(n: usize) -> NodeList<usize, ()> {
        let mut v = vec![None; n];
        gen_tree_rec(NodePtr::new(1), n, 1, &mut v);
        NodeList(v.iter().filter_map(|x| *x).collect())
    }

    // parent.key == k
    fn gen_tree_rec(
        parent: NodePtr<usize, ()>,
        n: usize,
        k: usize,
        v: &mut Vec<Option<NodePtr<usize, ()>>>,
    ) {
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

    pub fn bm_nop(v: &NodeList<usize, ()>) {
        let k = rand::thread_rng().gen_range(0..v.0.len());
        if !v.0[k].is_root() {}
    }

    pub fn bm_zig(v: &NodeList<usize, ()>) {
        let k = rand::thread_rng().gen_range(0..v.0.len());
        if !v.0[k].is_root() {
            v.0[k].zig();
        }
    }

    pub fn bm_splay(v: &NodeList<usize, ()>) {
        let k = rand::thread_rng().gen_range(0..v.0.len());
        v.0[k].splay();
    }

    impl<K, Op> Drop for NodeList<K, Op> {
        fn drop(&mut self) {
            for n in self.0.iter() {
                n.drop_node();
            }
        }
    }
}
#[cfg(test)]
mod test {
    use super::Direction::*;
    use super::TreeGenerator::*;
    #[allow(unused_imports)]
    use super::*;

    #[test]
    fn zig_step() {}

    #[test]
    fn eq_tree() {
        let node1: NodePtr<_, ()> = NodePtr::new(0);
        let node2 = NodePtr::new(0);
        assert_eq!(node1.tree(), node2.tree());
        node1.insert(1, Left, Left);
        node2.insert(1, Left, Left);
        assert_eq!(node1.tree(), node2.tree());
        node1.insert(2, Right, Right);
        assert_ne!(node1.tree(), node2.tree());
        node2.insert(2, Right, Right);
        assert_eq!(node1.tree(), node2.tree());
    }

    #[test]
    fn zig_test() {
        let node = NodePtr::new(0);
        let right = node.insert(2, Right, Left);
        let left = node.insert(9, Left, Left);
        let gc = right.insert(1, Left, Left);
        left.insert(3, Right, Right);
        left.insert(4, Left, Left);
        right.insert(5, Right, Right);
        assert_eq!(
            node.tree(),
            Tree::from(gen_tree(vec![
                Child(4),
                Child(3),
                Parent(9),
                Child(1),
                Child(5),
                Parent(2),
                Parent(0),
            ]))
        );

        left.zig();
        assert_eq!(
            left.tree(),
            Tree::from(gen_tree(vec![
                Child(4),
                Child(3),
                Child(1),
                Child(5),
                Parent(2),
                Parent(0),
                Parent(9),
            ]))
        );

        right.zig();
        assert_eq!(
            left.tree(),
            Tree::from(gen_tree(vec![
                Child(4),
                Child(3),
                Child(1),
                Parent(0),
                Child(5),
                Parent(2),
                Parent(9),
            ]))
        );

        gc.zig();
        assert_eq!(
            left.tree(),
            Tree::from(gen_tree(vec![
                Child(4),
                Child(3),
                Null,
                Parent(0),
                Null,
                Parent(1),
                Child(5),
                Parent(2),
                Parent(9),
            ]))
        );
    }

    #[test]
    fn gen_tree_test() {
        println!(
            "{}",
            Tree::from(gen_tree(vec![
                Child(0i32),
                Child(1),
                Parent(2),
                Null,
                Parent(3),
                Null,
                Child(4),
                Parent(5),
                Parent(6)
            ]))
        );
    }

    #[test]
    fn splay_test() {
        let root = gen_tree(vec![
            Child(0),
            Child(2),
            Parent(1),
            Child(3),
            Child(5),
            Parent(4),
            Parent(6),
        ]);
        println!("{}", Tree::from(root));
        let n3 = Tree::from(root).search_dfs(&3).unwrap();
        n3.splay();
        println!("{}", Tree::from(n3));
        let n0 = Tree::from(n3).search_dfs(&0).unwrap();
        n0.splay();
        println!("{}", Tree::from(n0));
        println!("{:?}", Tree::from(n0));
    }

    #[test]
    fn search_dfs_test() {
        let root = Tree::from(gen_tree(vec![
            Child(0),
            Child(2),
            Parent(1),
            Child(3),
            Null,
            Parent(5),
            Null,
            Parent(4),
            Parent(6),
        ]));
        assert!((0..7).all(|i| root.search_dfs(&i).is_some()));
        assert!(!(7..9).any(|i| root.search_dfs(&i).is_some()));
    }

    #[test]
    fn search_bfs_test() {
        let root = Tree::from(gen_tree(vec![
            Child(0),
            Child(2),
            Parent(1),
            Child(3),
            Null,
            Parent(5),
            Null,
            Parent(4),
            Parent(6),
        ]));
        assert!((0..7).all(|i| root.search_bfs(&i).is_some()));
        assert!(!(7..9).any(|i| root.search_bfs(&i).is_some()));
    }

    #[test]
    fn bench_test() {
        let nodes = bench::gen_tree(1000);
        for _ in 0..100000 {
            bench::bm_splay(&nodes);
        }
    }
}
