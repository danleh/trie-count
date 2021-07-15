
// see also https://github.com/michaelsproul/rust_radix_trie/blob/master/examples/string_frequency.rs

// TODO generalize over generic sequences of T, and values V (instead of str, usize)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trie {
    // We use a "pseudo node" with just the empty string as prefix, which avoids duplicate code.
    root: Node,

    // See `Node::try_insert`.
    tokenize_at: Option<char>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Node {
    // Since the prefix cannot be grown (only when merging a node with its only child, which is
    // currently not implemented), we can save the capacity pointer and just make this a boxed str.
    prefix: Box<str>,

    // Invariant: None of the children share a prefix.
    children: Vec<Node>,

    // TODO chache size of subtree
    // subtree_size: usize,

    // TODO maybe:
    // parent: &Node,
}

// see https://users.rust-lang.org/t/is-this-code-idiomatic/51798/14
// and https://www.hackertouch.com/longest-common-prefix-in-rust.html
// fn longest_common_prefix<'a>(strings: &[&'a str]) -> &'a str {
//     match strings.split_first() {
//         Some((mut prefix, rest)) => {
//             for (idx, char) in prefix.char_indices() {
                
//             }
//             unimplemented!()
//         },
//         None => "",
//     }
// }

impl Trie {
    pub fn new() -> Self {
        Self { 
            root: Node::new_leaf(""),
            tokenize_at: None,
        }
    }

    pub fn with_split_token(token: char) -> Self {
        Self { 
            root: Node::new_leaf(""),
            tokenize_at: Some(token),
        }
    }

    pub fn insert(&mut self, str: &str) {
        assert!(self.root.try_insert(str, self.tokenize_at));
    }

    // TODO pub fn remove(&mut self, Node?)
    // TODO merge node with child if only single child / merge node with parent if only child

    pub fn by_levels(&self) -> Vec<(&str, usize)> {
        let mut result = Vec::new();
        // Do not include the always empty root node prefix, so iterate over children.
        for child in &self.root.children {
            child.by_levels(0, &mut result);
        }
        result
        
        // TODO imperative implementation
        // let mut level = 0;
        // let current = self.root;
        // unimplemented!()
    }

    /// Returns (prefix, level, count).
    pub fn by_levels_with_count(&self) -> Vec<(&str, usize, usize)> {
        let mut result = Vec::new();
        // Do not include the always empty root node prefix, so iterate over children.
        for child in &self.root.children {
            child.by_levels_with_count(0, &mut result);
        }
        result
        // TODO use iterator, see below
    }

    pub fn sort_by_count(&mut self) {
        self.root.sort_by_count()
    }

    pub fn len(&self) -> usize {
        self.root.len()
    }

    // pub fn graphviz(&self) -> String {
    //     todo!()
    // }

    // fn iter(&self) -> impl Iterator<Item=&str> {
    //     todo!()
    // }
}

impl Node {
    fn new_leaf(str: &str) -> Self {
        Self {
            prefix: str.into(),
            children: Vec::new(),
        }
    }

    fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }

    // TODO make lazy iterator, not collecting into result
    fn by_levels<'a>(&'a self, level: usize, result: &mut Vec<(&'a str, usize)>) {
        result.push((&self.prefix, level));
        for child in &self.children {
            child.by_levels(level+1, result);
        }
    }

    // TODO iterator, rename to iter_with_count()
    fn by_levels_with_count<'a>(&'a self, level: usize, result: &mut Vec<(&'a str, usize, usize)>) {
        result.push((&self.prefix, level, self.len()));
        for child in &self.children {
            child.by_levels_with_count(level+1, result);
        }
    }

    fn len(&self) -> usize {
        if self.is_leaf() {
            1
        } else {
            self.children.iter().map(|node| node.len()).sum()
        }
    }

    fn sort_by_count(&mut self) {
        self.children.sort_by_cached_key(|node| std::cmp::Reverse(node.len()));
        for child in &mut self.children {
            child.sort_by_count();
        }
    }

    fn try_insert(&mut self, str: &str, tokenize_at: Option<char>) -> bool {
        let mut common_prefix_len = self.prefix
            // Iterate over unicode scalar values in prefix and input in lock-step.
            .char_indices()
            .zip(str.chars())
            // Stop at the first character difference.
            .find(|((_, c1), c2)| c1 != c2)
            // Return the prefix up to the difference...
            .map(|((byte_pos, _), _)| byte_pos)
            // ...or the whole string (actually, the shorter of the two), if no difference was found.
            .unwrap_or(std::cmp::min(self.prefix.len(), str.len()));

        // If the tokenize option is set, only allow "breaks" (i.e., split between prefix and rest)
        // after said token. Since we already found a common prefix, we can short it to just end
        // after the token.
        if let Some(token) = tokenize_at {
            common_prefix_len = str[..common_prefix_len].rfind(token).map_or(0, |pos| pos+1);
        }

        let (common_prefix, rest) = str.split_at(common_prefix_len);

        // Insertion case A)
        // This node is a full prefix of the input, so try to insert into one of our children.
        if common_prefix == &self.prefix[..] {
            // FIXME test with empty insertion or "foo", "foobar", stack overflow?
            // If this node was a leaf, make it explicit by adding an "empty" child.
            // if self.is_leaf() {
            //     self.children.push(Self::new_leaf(""));
            // }

            if rest.is_empty() {
                unimplemented!("duplicate value");
            }

            for child in &mut self.children {
                if child.try_insert(rest, tokenize_at) {
                    return true;
                }
            }
            self.children.push(Self::new_leaf(rest));
            return true;
        }

        // Insertion case B)
        // No common prefix, so cannot insert into this sub-trie.
        if common_prefix.is_empty() {
            return false;
        }
        
        // Insertion case C)
        // This prefix and the input partially overlap, so split this node into the common prefix,
        // and insert a new intermediate node with the rest and current children.
        let (_, prefix_rest) = self.prefix.split_at(common_prefix_len);
        
        let current_children = std::mem::replace(&mut self.children, Vec::new());
        let new_intermediate = Self {
            prefix: prefix_rest.into(),
            children: current_children,
        };

        self.prefix = common_prefix.into();
        self.children = vec![
            new_intermediate,
            Self::new_leaf(rest)
        ];
        return true;
    }
}