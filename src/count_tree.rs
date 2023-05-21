use crate::trie::{self, Trie};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Node<'a> {
    pub str: &'a str,
    /// Includes the counts of the children.
    pub count: u64,
    /// Empty if this is a leaf node.
    pub children: Vec<Node<'a>>,
}

impl<'a, F> From<&'a Trie<u64, F>> for Node<'a> {
    fn from(trie: &'a Trie<u64, F>) -> Self {
        fn from(trie_node: &trie::Node<u64>) -> Node {
            let mut count = trie_node.value().copied().unwrap_or(0);
            let mut children = Vec::new();
            for trie_node in trie_node.children() {
                let node = from(trie_node);
                count += node.count;
                children.push(node);
            }
            Node {
                str: trie_node.key_part(),
                count,
                children,
            }
        }
        from(&trie.root)
    }
}

impl<'data> Node<'data> {
    pub fn height(&self) -> usize {
        let mut max_depth = 0;
        for child in self.children.iter() {
            max_depth = max_depth.max(child.height() + 1);
        }
        max_depth
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Node<'data>) -> bool,
    {
        fn retain<'data, F>(node: &mut Node<'data>, f: &mut F)
        where
            F: FnMut(&Node<'data>) -> bool,
        {
            for child in node.children.iter_mut() {
                retain(child, f);
            }
            node.children.retain(|node| f(node));
        }
        retain(self, &mut f)
    }

    pub fn sort_by_key<F, K>(&mut self, mut f: F)
    where
        F: FnMut(&Node<'data>) -> K,
        K: Ord,
    {
        fn sort_by_key<'data, F, K>(node: &mut Node<'data>, f: &mut F)
        where
            F: FnMut(&Node<'data>) -> K,
            K: Ord,
        {
            for child in node.children.iter_mut() {
                sort_by_key(child, f);
            }
            node.children.sort_by_key(|node| f(node));
        }
        sort_by_key(self, &mut f)
    }

    pub fn fold<F, T>(&self, init: T, mut f: F) -> T
    where
        F: FnMut(T, &Node<'data>) -> T,
    {
        fn fold<'data, F, T>(node: &Node<'data>, acc: T, f: &mut F) -> T
        where
            F: FnMut(T, &Node<'data>) -> T,
        {
            let mut acc = f(acc, node);
            for child in node.children.iter() {
                acc = fold(child, acc, f);
            }
            acc
        }
        fold(self, init, &mut f)
    }
}
