#![allow(dead_code)]
use std::{
    fmt::{self, Debug, Display},
    ptr::NonNull,
};

pub struct SplayTree<K> {
    root: Tree<K>,
}

// private
#[derive(Eq)]
pub enum Tree<K> {
    Null,
    Root(NonNull<Node<K>>),
}

// impl<K> PartialEq for Tree<K> {
//     fn eq(&self, other: &Self) -> bool {
//         match (self, other) {
//             (Tree::Null, Tree::Null) => true,
//             (Tree::Root(l), Tree::Root(r)) => l == r,
//             _ => false,
//         }
//     }
// }

impl<K> From<Tree<K>> for Option<NonNull<Node<K>>> {
    fn from(value: Tree<K>) -> Self {
        match value {
            Tree::Null => None,
            Tree::Root(n) => Some(n),
        }
    }
}

impl<K: PartialEq> PartialEq for Tree<K> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Tree::Null, Tree::Null) => true,
            (Tree::Root(l), Tree::Root(r)) => unsafe {
                let (l, r) = (l.as_ref(), r.as_ref());
                l.key == r.key && Tree::from(l.left) == Tree::from(r.left) && Tree::from(l.right) == Tree::from(r.right)
            },
            _ => false,
        }
    }
}


// private
#[derive(Clone, PartialEq, Eq)]
pub struct Node<K> {
    left: Option<NodePtr<K>>,
    right: Option<NodePtr<K>>,
    parent: Option<NodePtr<K>>,
    key: K,
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

    fn option(&self) -> Option<NonNull<Node<K>>> {
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

    fn as_mut<'a>(self) -> Option<&'a mut Node<K>> {
        self.option().map(|mut n| unsafe { n.as_mut() })
    }

    fn splay(self) -> Self {
        while let Self::Root(r) = self {
            if unsafe { r.as_ref().is_root() } {
                break;
            }
        }
        unimplemented!()
    }

    fn fmt_rec(&self, f: &mut fmt::Formatter, level: usize) -> fmt::Result
    where
        K: Display,
    {
        if let Some(s) = self.option() {
            unsafe {
                Self::from_option(s.as_ref().left).fmt_rec(f, level + 1)?;
                writeln!(f, "{}{}", "\t".repeat(level), s.as_ref().key)?;
                Self::from_option(s.as_ref().right).fmt_rec(f, level + 1)?;
            }
        }
        Ok(())
    }

    fn fmt_debug_rec(&self, f: &mut fmt::Formatter) -> fmt::Result
    where
        K: Debug,
    {
        if let Some(s) = self.option() {
            unsafe {
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
            }
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
            Some(p) => {
                p.as_ref().which(self.into()).is_none()
            },
        }
    }

    fn new_ptr(key: K) -> NonNull<Self> {
        Box::leak(Box::new(Self {
            left: None,
            right: None,
            parent: None,
            key,
        }))
        .into()
    }

    /// # Safety
    /// `self.left != self.right`
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
    /// `self`の子ノードへの参照が他に存在しない
    pub fn insert_left(&mut self, key: K, child_dir: Direction) -> NodePtr<K> {
        let l = self.left;
        let new_node = match child_dir {
            Direction::Left => NodePtr::from_raw_parts(key, l, None, Some(self.into())),
            Direction::Right => NodePtr::from_raw_parts(key, None, l, Some(self.into())),
        };
        self.left = Some(new_node);
        if let Some(l) = l.map(NodePtr::as_mut) {
            l.parent = Some(new_node);
        }
        new_node
    }

    /// # Safety
    /// `self`の子ノードへの参照が他に存在しない
    pub fn insert_right(&mut self, key: K, child_dir: Direction) -> NodePtr<K> {
        let r = self.right;
        let new_node = match child_dir {
            Direction::Left => NodePtr::from_raw_parts(key, r, None, Some(self.into())),
            Direction::Right => NodePtr::from_raw_parts(key, None, r, Some(self.into())),
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
    /// `self.left != self.right`
    fn cas(&mut self, old: NodePtr<K>, new: NodePtr<K>) -> bool {
        if let Some(d) = self.which(old) {
            self.replace_child(d, Some(new));
            true
        } else { false }
    }

    fn from_raw_parts(
        key: K,
        left: Option<NodePtr<K>>,
        right: Option<NodePtr<K>>,
        parent: Option<NodePtr<K>>,
    ) -> NonNull<Self> {
        Box::leak(Box::new(Self {
            left,
            right,
            parent,
            key,
        }))
        .into()
    }
}

// private
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Direction {
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
    // private
    pub fn new(key: K) -> Self {
        Self(Node::new_ptr(key))
    }

    fn from_raw_parts(
        key: K,
        left: Option<NodePtr<K>>,
        right: Option<NodePtr<K>>,
        parent: Option<NodePtr<K>>,
    ) -> Self {
        Self(Node::from_raw_parts(key, left, right, parent))
    }

    pub fn insert(self, key: K, dir: Direction, child_dir: Direction) -> Self {
        self.as_mut().insert(key, dir, child_dir)
    }
    // private
    pub fn is_root(self) -> bool {
        self.as_ref().is_root()
    }

    fn as_mut<'a>(mut self) -> &'a mut Node<K> {
        unsafe { self.0.as_mut() }
    }

    fn as_ref<'a>(self) -> &'a Node<K> {
        unsafe { self.0.as_ref() }
    }

    // private function
    /// # Safety
    /// * 親ノードが存在する
    /// * selfの親ノードへの参照が他に存在しない
    /// * selfの子ノードへの参照が他に存在しない
    /// * selfの兄弟ノードへの参照が他に存在しない
    /// * selfの親の親ノードへの参照が他に存在しない
    /// * 自身のノードへの参照が他に存在しない
    pub fn zig(self) {
        let s = self.as_mut();
        let p_ptr = {
            let p = s.parent;
            debug_assert!(p.is_some());
            unsafe { p.unwrap_unchecked() }
        };

        let p = p_ptr.as_mut();
        let gp = p.parent;
        // debug_assert!(self != p_ptr && Some(p_ptr) != gp && Some(self) != gp);
        gp.map(|gp| gp.as_mut().cas(p_ptr, self));
        s.parent = gp;
        
        if let Some(d) = p.which(self) {
            let child = s.child(d.opposite());
            s.link_child(p, d.opposite());
            // *s.child_mut(d) = Some(p_ptr);
            p.link_child_tree(child, d);
        }
    }

    fn zig_zig(self) {
        
    }
    fn tree(self) -> Tree<K> {
        self.into()
    }
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
#[cfg(test)]
mod test {
    use super::Direction::*;
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
    fn print_tree() {
        let node = NodePtr::new(0);
        let right = node.insert(2, Right, Left);
        let left = node.insert(9, Left, Left);
        let gc = right.insert(1, Left, Left);
        left.insert(3, Right, Right);
        left.insert(4, Left, Left);
        right.insert(5, Right, Right);
        println!("{}", node.tree());
        left.zig();
        println!("zig 9 :\n{}", left.tree());
        println!("{:?}", left.tree());

        right.zig();
        println!("zig 2:\n{}", left.tree());
        println!("{:?}", left.tree());

        gc.zig();
        println!("zig 1:\n{}", left.tree());
        println!("{:?}", left.tree());
    }
}
