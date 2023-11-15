#![allow(dead_code)]
pub mod link_cut_tree;

use std::{
    fmt::{self, Debug, Display},
    ptr::NonNull,
};

pub struct SplayTree<K> {
    root: Tree<K>,
}

#[derive(Eq)]
enum Tree<K> {
    Null,
    Root(NonNull<Node<K>>),
}

impl<K> From<Tree<K>> for Option<NodePtr<K>> {
    fn from(value: Tree<K>) -> Self {
        match value {
            Tree::Null => None,
            Tree::Root(n) => Some(NodePtr(n)),
        }
    }
}

impl<K: PartialEq> PartialEq for Tree<K> {
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
struct Node<K> {
    left: Option<NodePtr<K>>,
    right: Option<NodePtr<K>>,
    parent: Option<NodePtr<K>>,
    key: K,
    /// 左の子と右の子が反転されているか
    rev: bool,
}

#[derive(Eq)]
pub struct NodePtr<K>(NonNull<Node<K>>);

impl<K> PartialEq for NodePtr<K> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K> Clone for NodePtr<K> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K> Copy for NodePtr<K> {}

impl<K> Tree<K> {
    const fn new() -> Self {
        Self::Null
    }

    fn option(&self) -> Option<NodePtr<K>> {
        self.clone_shallow().into()
    }

    fn clone_shallow(&self) -> Self {
        match self {
            Self::Null => Self::Null,
            Self::Root(n) => Self::Root(*n),
        }
    }

    fn from_option(option: Option<NodePtr<K>>) -> Self {
        match option {
            Some(n) => Tree::Root(n.0),
            None => Tree::Null,
        }
    }

    fn search_dfs(&self, key: &K) -> Option<NodePtr<K>>
    where
        K: Eq,
    {
        if let Some(root) = self.option() {
            let mut stack: Vec<NodePtr<K>> = vec![root];
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

    fn search_bfs(&self, key: &K) -> Option<NodePtr<K>>
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

impl<K> Node<K> {
    /// # Safety
    /// `self`の親ノードへの可変参照が他に存在しない
    fn is_root(&self) -> bool {
        match self.parent {
            None => true,
            Some(p) => p.as_ref().which(self.into()).is_none(),
        }
    }

    fn new_ptr(key: K) -> NonNull<Self> {
        Box::leak(Box::new(Self {
            left: None,
            right: None,
            parent: None,
            key,
            rev: false,
        }))
        .into()
    }

    /// # Safety
    /// `self.left != self.right || (self.left == None && self.right == None)`
    fn which(&self, child: NodePtr<K>) -> Option<Direction> {
        if self.left == Some(child) {
            Some(Direction::Left)
        } else if self.right == Some(child) {
            Some(Direction::Right)
        } else {
            None
        }
    }

    fn child(&self, dir: Direction) -> Option<NodePtr<K>> {
        if let Direction::Left = dir {
            self.left
        } else {
            self.right
        }
    }

    fn replace_child(&mut self, dir: Direction, child: Option<NodePtr<K>>) -> Option<NodePtr<K>> {
        match dir {
            Direction::Left => std::mem::replace(&mut self.left, child),
            Direction::Right => std::mem::replace(&mut self.right, child),
        }
    }

    fn child_mut(&mut self, dir: Direction) -> &mut Option<NodePtr<K>> {
        match dir {
            Direction::Left => &mut self.left,
            Direction::Right => &mut self.right,
        }
    }

    /// # Safety
    /// `self`の左の子ノードへの参照が他に存在しない
    pub fn insert_left(&mut self, key: K, child_dir: Direction) -> NodePtr<K> {
        let l = self.left;
        let new_node = match child_dir {
            Direction::Left => NodePtr::from_raw_parts(key, l, None, Some(self.into()), false),
            Direction::Right => NodePtr::from_raw_parts(key, None, l, Some(self.into()), false),
        };
        self.left = Some(new_node);
        if let Some(l) = l.map(NodePtr::as_mut) {
            l.parent = Some(new_node);
        }
        new_node
    }

    /// # Safety
    /// `self`の右の子ノードへの参照が他に存在しない
    pub fn insert_right(&mut self, key: K, child_dir: Direction) -> NodePtr<K> {
        let r = self.right;
        let new_node = match child_dir {
            Direction::Left => NodePtr::from_raw_parts(key, r, None, Some(self.into()), false),
            Direction::Right => NodePtr::from_raw_parts(key, None, r, Some(self.into()), false),
        };
        self.right = Some(new_node);
        if let Some(r) = r.map(NodePtr::as_mut) {
            r.parent = Some(new_node);
        }
        new_node
    }

    /// # Safety
    /// `self`の`dir`の方向の子ノードへの参照が他に存在しない
    pub fn insert(&mut self, key: K, dir: Direction, child_dir: Direction) -> NodePtr<K> {
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
    fn link_child_tree(&mut self, child: Option<NodePtr<K>>, dir: Direction) {
        self.replace_child(dir, child);
        if let Some(child) = child.map(NodePtr::as_mut) {
            child.parent = Some(self.into());
        }
    }

    /// # Safety
    /// `self.left != self.right || (self.left == None && self.right == None)`
    fn cas_child(&mut self, old: NodePtr<K>, new: NodePtr<K>) -> bool {
        if let Some(d) = self.which(old) {
            self.replace_child(d, Some(new));
            true
        } else {
            false
        }
    }

    fn cas_child_with(
        &mut self,
        old: NodePtr<K>,
        f: impl FnOnce(Direction) -> Option<NodePtr<K>>,
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
        left: Option<NodePtr<K>>,
        right: Option<NodePtr<K>>,
        parent: Option<NodePtr<K>>,
        rev: bool,
    ) -> NonNull<Self> {
        Box::leak(Box::new(Self {
            left,
            right,
            parent,
            key,
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

    fn expose(&mut self) -> NodePtr<K> {
        self.splay();
        self.right = None;
        let mut p = NodePtr::from(&*self);

        while let Some(c_ptr) = p.as_ref().parent {
            let c = c_ptr.as_mut();
            c.splay();
            c.right = Some(p);
            c.update();
            p = c_ptr;
        }
        self.splay();
        return p;
    }

    /// # Safety
    /// * 木に含まれるノードの参照が存在しない
    /// * 自身の左の子ノードが存在する
    fn cut(&mut self) {
        self.expose();
        let l = unsafe {
            let l = self.left.take();
            debug_assert!(l.is_some());
            l.unwrap_unchecked()
        };
        l.as_mut().parent = None;
    }

    fn link(&mut self, parent: &mut Self) {
        self.expose();
        parent.expose();
        self.parent = Some(parent.into());
        parent.right = Some(self.into());
    }

    fn toggle(&mut self) {
        self.rev = true;
        std::mem::swap(&mut self.left, &mut self.right);
    }

    fn update(&mut self) {}

    /// # Safety
    /// * 自身の子ノードの参照が他に存在しない
    fn push(&mut self) {
        if self.rev {
            self.rev = false;
            if let Some(l) = self.left {
                l.as_mut().toggle();
            }
            if let Some(r) = self.right {
                r.as_mut().toggle();
            }
        }
    }
    fn evert(&mut self) {
        self.expose();
        std::mem::swap(&mut self.left, &mut self.right);
        if let Some(l) = self.left {
            l.as_mut().toggle();
        }
        if let Some(r) = self.right {
            r.as_mut().toggle();
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

impl<'a, K> From<&'a mut Node<K>> for NodePtr<K> {
    fn from(value: &'a mut Node<K>) -> Self {
        Self(NonNull::from(value))
    }
}

impl<'a, K> From<&'a Node<K>> for NodePtr<K> {
    fn from(value: &'a Node<K>) -> Self {
        Self(NonNull::from(value))
    }
}

impl<K> From<Option<NodePtr<K>>> for Tree<K> {
    fn from(value: Option<NodePtr<K>>) -> Self {
        Self::from_option(value)
    }
}

impl<K> NodePtr<K> {
    fn new(key: K) -> Self {
        Self(Node::new_ptr(key))
    }

    fn from_raw_parts(
        key: K,
        left: Option<NodePtr<K>>,
        right: Option<NodePtr<K>>,
        parent: Option<NodePtr<K>>,
        rev: bool,
    ) -> Self {
        Self(Node::from_raw_parts(key, left, right, parent, rev))
    }

    fn insert(self, key: K, dir: Direction, child_dir: Direction) -> Self {
        self.as_mut().insert(key, dir, child_dir)
    }

    fn is_root(self) -> bool {
        self.as_ref().is_root()
    }

    fn as_mut<'a>(mut self) -> &'a mut Node<K> {
        unsafe { self.0.as_mut() }
    }

    fn as_ref<'a>(self) -> &'a Node<K> {
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

    fn tree(self) -> Tree<K> {
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

impl<K> From<NodePtr<K>> for Tree<K> {
    fn from(value: NodePtr<K>) -> Self {
        Tree::Root(value.0)
    }
}

impl<K: Display> Display for Tree<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_rec(f, 0)
    }
}

impl<K: Debug> Debug for Tree<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_debug_rec(f)?;
        writeln!(f)
    }
}
impl<K> SplayTree<K> {
    pub const fn new() -> Self {
        Self { root: Tree::new() }
    }
}

enum TreeGenerator<K> {
    Child(K),
    Parent(K),
    Null,
}

fn gen_tree<K>(struc: Vec<TreeGenerator<K>>) -> Option<NodePtr<K>> {
    let mut stack = vec![];
    for s in struc {
        match s {
            TreeGenerator::Child(k) => {
                stack.push(Some(NodePtr::new(k)));
            }
            TreeGenerator::Parent(k) => {
                let r = stack.pop().expect("invalid tree structure");
                let l = stack.pop().expect("invalid tree structure");
                let n = NodePtr::from_raw_parts(k, l, r, None, false);
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

    pub struct NodeList<K>(Vec<NodePtr<K>>);

    pub fn gen_tree(n: usize) -> NodeList<usize> {
        let mut v = vec![None; n];
        gen_tree_rec(NodePtr::new(1), n, 1, &mut v);
        NodeList(v.iter().filter_map(|x| *x).collect())
    }

    // parent.key == k
    fn gen_tree_rec(
        parent: NodePtr<usize>,
        n: usize,
        k: usize,
        v: &mut Vec<Option<NodePtr<usize>>>,
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

    pub fn bm_nop(v: &NodeList<usize>) {
        let k = rand::thread_rng().gen_range(0..v.0.len());
        if !v.0[k].is_root() {}
    }

    pub fn bm_zig(v: &NodeList<usize>) {
        let k = rand::thread_rng().gen_range(0..v.0.len());
        if !v.0[k].is_root() {
            v.0[k].zig();
        }
    }

    pub fn bm_splay(v: &NodeList<usize>) {
        let k = rand::thread_rng().gen_range(0..v.0.len());
        v.0[k].splay();
    }

    impl<K> Drop for NodeList<K> {
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
        let node1 = NodePtr::new(0);
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
