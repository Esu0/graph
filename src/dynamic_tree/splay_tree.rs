use std::ptr::NonNull;

pub struct SplayTree<K> {
    root: Tree<K>,
}

#[derive(Eq)]
enum Tree<K> {
    Null,
    Root(NonNull<Node<K>>),
}

impl<K> PartialEq for Tree<K> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Tree::Null, Tree::Null) => true,
            (Tree::Root(l), Tree::Root(r)) => l == r,
            _ => false,
        }
    }
}

impl<K> From<Tree<K>> for Option<NonNull<Node<K>>> {
    fn from(value: Tree<K>) -> Self {
        match value {
            Tree::Null => None,
            Tree::Root(n) => Some(n),
        }
    }
}

impl<K> Clone for Tree<K> {
    fn clone(&self) -> Self {
        match self {
            Tree::Null => Tree::Null,
            Tree::Root(n) => Tree::Root(*n),
        }
    }
}
impl<K> Copy for Tree<K> {}

// impl<K> Eq for Tree<K> {}

struct Node<K> {
    left: Tree<K>,
    right: Tree<K>,
    parent: Tree<K>,
    key: K,
}

impl<K> Tree<K> {
    const fn new() -> Self {
        Self::Null
    }

    fn option(self) -> Option<NonNull<Node<K>>> {
        self.into()
    }

    fn splay(self) -> Self {
        while let Self::Root(r) = self {
            if unsafe {r.as_ref().is_root()} {
                break;
            }

        }
        unimplemented!()
    }

    fn zig(self) -> Self {
        if let Self::Root(mut s) = self {
            unsafe {
                let mut p = s.as_ref().parent.option().unwrap();
                if Self::Root(s) == p.as_ref().left {
                    let r = s.as_ref().right;
                    s.as_mut().right = Self::Root(p);
                    if let Tree::Root(mut r) = r {
                        r.as_mut().parent = Tree::Root(p);
                    }
                    p.as_mut().left = r;
                } else if Self::Root(s) == p.as_ref().right {
                    let l = s.as_ref().left;
                    s.as_mut().left = Self::Root(p);
                    if let Tree::Root(mut l) = l {
                        l.as_mut().parent = Tree::Root(p);
                    }
                    p.as_mut().right = l;
                }
                s.as_mut().parent = p.as_ref().parent;
            }
            self
        } else {
            Self::Null
        }
    }
}

impl<K> Node<K> {
    fn is_root(&self) -> bool {
        match self.parent {
            Tree::Null => true,
            Tree::Root(p) => unsafe {
                let p = p.as_ref();
                let s = Tree::Root(NonNull::from(self));
                p.left != s && p.right != s
            }
        }
    }
}
impl<K> SplayTree<K> {
    pub const fn new() -> Self {
        Self {
            root: Tree::new(),
        }
    }

    
}