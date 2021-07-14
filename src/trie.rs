// TODO generalize over generic sequences of T, and values V (instead of str, usize)
#[derive(Debug, Clone)]
pub struct Trie {
    root: Node,
}

#[derive(Debug, Clone)]
struct Node {
    // TODO String -> Box<str>
    prefix: String,

    // Invariant: none of the children share a prefix
    children: Vec<Node>,

    // TODO chache size of subtree
    // subtree_size: usize,

    // TODO maybe:
    // parent: &Node,
}

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
        Trie {
            root: Node {
                prefix: "".into(),
                children: Vec::new(),
            }
        }
    }

    pub fn insert(&mut self, str: &str) {
        assert!(self.root.try_insert(str));
    }

    // TODO pub fn remove(&mut self, Node?)

    pub fn by_levels(&self) -> Vec<(&str, usize)> {
        let mut result = Vec::new();
        self.root.by_levels(0, &mut result);
        result
        
        // TODO imperative implementation
        // let mut level = 0;
        // let current = self.root;
        // unimplemented!()
    }

    // pub fn graphviz(&self) -> String {
    //     unimplemented!()
    // }

    // fn iter(&self) -> impl Iterator<Item=&str> {
    //     unimplemented!()
    // }
}

impl Node {
    fn new_leaf(str: &str) -> Self {
        Self {
            prefix: str.into(),
            children: Vec::new(),
        }
    }

    fn by_levels<'a>(&'a self, level: usize, result: &mut Vec<(&'a str, usize)>) {
        result.push((&self.prefix, level));
        for child in &self.children {
            child.by_levels(level+1, result);
        }
    }

    fn try_insert(&mut self, str: &str) -> bool {
        let common_prefix_len = self.prefix
            // Iterate over aligned unicode scalar values in prefix and input.
            .char_indices()
            .zip(str.chars())
            // Stop at the first character difference.
            .find(|((_, c1), c2)| c1 != c2)
            // Return the prefix up to the difference...
            .map(|((byte_pos, _), _)| byte_pos)
            // ...or the whole (shorter of the two) string, if no difference was found.
            .unwrap_or(std::cmp::min(self.prefix.len(), str.len()));
        let (common_prefix, rest) = str.split_at(common_prefix_len);

        // This node is a full prefix of the input, so try to insert into one of our children.
        if common_prefix == self.prefix {
            for child in &mut self.children {
                if child.try_insert(rest) {
                    return true;
                }
            }
            self.children.push(Self::new_leaf(rest));
            return true;
        }

        // No common prefix, so cannot insert into this sub-trie.
        if common_prefix_len == 0 {
            return false;
        }
        
        // This prefix and the input only partially overlap, so split this node into the common prefix, and a new intermediate node with the rest and current children.
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