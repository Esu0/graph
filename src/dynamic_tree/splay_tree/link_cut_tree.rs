use super::NodePtr;

struct LinkCutTree<K> {
    root: Option<NodePtr<K>>,
}

impl<K> LinkCutTree<K> {
    fn expose(&self, x: NodePtr<K>) {
        x.splay();
        x.as_mut().right = None;
        {
            let mut p = x;

            while let Some(c) = p.as_ref().parent {
                c.splay();
                c.as_mut().right = Some(p);
                p = c;
            }
        }
        x.splay();
    }
}