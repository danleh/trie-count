use crate::trie::Trie;
use crate::trie::TrieNode;

pub struct StrCountNode<'data> {
    pub str: &'data str,
    /// Includes the counts of the children.
    pub count: u64,
    /// Empty if this is a leaf node.
    pub children: Vec<StrCountNode<'data>>,
}

impl<'data, F> From<&'data Trie<u64, F>> for StrCountNode<'data> {
    fn from(trie: &'data Trie<u64, F>) -> Self {
        fn from(trie_node: &TrieNode<u64>) -> StrCountNode {
            let mut count = trie_node.value().copied().unwrap_or(0);
            let mut children = Vec::new();
            for trie_node in trie_node.children() {
                let node = from(trie_node);
                count += node.count;
                children.push(node);
            }
            StrCountNode {
                str: trie_node.key_part(),
                count,
                children,
            }
        }
        from(&trie.root)
    }
}

impl<'data> StrCountNode<'data> {
    pub fn height(&self) -> usize {
        let mut max_depth = 0;
        for child in self.children.iter() {
            max_depth = max_depth.max(child.height() + 1);
        }
        max_depth
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&StrCountNode<'data>) -> bool,
    {
        fn retain<'data, F>(node: &mut StrCountNode<'data>, f: &mut F)
        where
            F: FnMut(&StrCountNode<'data>) -> bool,
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
        F: FnMut(&StrCountNode<'data>) -> K,
        K: Ord,
    {
        fn sort_by_key<'data, F, K>(node: &mut StrCountNode<'data>, f: &mut F)
        where
            F: FnMut(&StrCountNode<'data>) -> K,
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
        F: FnMut(T, &StrCountNode<'data>) -> T,
    {
        fn fold<'data, F, T>(node: &StrCountNode<'data>, acc: T, f: &mut F) -> T
        where
            F: FnMut(T, &StrCountNode<'data>) -> T,
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
