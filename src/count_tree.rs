use crate::trie::{self, Trie};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Node<'a> {
    pub str: &'a str,
    /// Includes the counts of the children.
    pub count: u64,
    /// Empty if this is a leaf node.
    pub children: Box<[Node<'a>]>,
}

impl<'a> From<&'a Trie<u64>> for Node<'a> {
    fn from(trie: &'a Trie<u64>) -> Self {
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
                children: children.into_boxed_slice(),
            }
        }
        from(&trie.root)
    }
}

impl<'data> Node<'data> {
    pub fn sort_by_count_desc(&mut self) {
        for child in self.children.iter_mut() {
            child.sort_by_count_desc();
        }
        self.children.sort_by_key(|node| std::cmp::Reverse(node.count));
    }

    pub fn sort_by_str(&mut self) {
        for child in self.children.iter_mut() {
            child.sort_by_str();
        }
        self.children.sort_by_key(|node| node.str);
    }
}
