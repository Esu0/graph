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

    unsafe fn as_mut<'a>(self) -> Option<&'a mut Node<K>> {
        self.option().map(|mut n| unsafe {n.as_mut()})
    }

    fn splay(self) -> Self {
        while let Self::Root(r) = self {
            if unsafe {r.as_ref().is_root()} {
                break;
            }

        }
        unimplemented!()
    }

    fn zig(self) {
        unsafe {
            let mut s_ptr = self.option().unwrap();
            let mut p_ptr = s_ptr.as_ref().parent.option().unwrap();
            let gp = p_ptr.as_ref().parent;
            debug_assert!(s_ptr != p_ptr && Self::Root(p_ptr) != gp && self != gp);
            let s = s_ptr.as_mut();
            let p = p_ptr.as_mut();
            if let Some(gp) = gp.as_mut() {
                if gp.left == self {
                    gp.left = self;
                } else if gp.right == self {
                    gp.right = self;
                }
            }
            if p.left == self {
                let right = s.right;
                debug_assert!(![Self::Root(p_ptr), self].contains(&right));

                p.parent = self;
                p.left = right;

                s.parent = gp;
                s.right = Self::Root(p_ptr);

                if let Some(right) = right.as_mut() {
                    right.parent = Self::Root(p_ptr);
                }
            } else if p.right == self {
                let left = s.left;
                debug_assert!(left != Self::Root(p_ptr) && left != self);
                p.parent = self;
                p.right = left;

                s.parent = gp;
                s.left = Self::Root(p_ptr);

                if let Some(left) = left.as_mut() {
                    left.parent = Self::Root(p_ptr);
                }
            }
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

    fn new_ptr(key: K) -> NonNull<Self> {
        Box::leak(Box::new(Self {
            left: Tree::new(),
            right: Tree::new(),
            parent: Tree::new(),
            key,
        })).into()
    }
}
impl<K> SplayTree<K> {
    pub const fn new() -> Self {
        Self {
            root: Tree::new(),
        }
    }

    
}

#[cfg(test)]
mod test {
    #[allow(unused_imports)]
    use super::*;

    #[test]
    fn zig_step() {

    }
}