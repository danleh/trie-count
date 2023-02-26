
// see https://github.com/michaelsproul/rust_radix_trie/blob/master/examples/string_frequency.rs
// and https://github.com/miedzinski/prefix-tree
// and https://en.wikipedia.org/wiki/Radix_tree

// TODO generalize over generic sequences of T, and values V (instead of str, usize)
// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub struct Trie {
//     // We use a "pseudo node" with just the empty string as prefix, which avoids duplicate code.
//     root: Node,

//     // See `Node::try_insert`.
//     tokenize_at: Vec<char>
// }

use unicode_segmentation::{UnicodeSegmentation, GraphemeIndices};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Node {
    // Leaf {
    //     // common_prefix: &'arena str,
    //     // count: usize,
    //     // parent: &Node,
    // },
    // Interior {
    common_prefix: Box<str>,
    children: Vec<Node>,
    // },
}

// struct Node {
//     // Since the prefix cannot be grown (only when merging a node with its only child, which is
//     // currently not implemented), we can save the capacity pointer and just make this a boxed str.
//     common_prefix: Box<str>,

//     // Invariant: None of the children share a prefix.
//     children: Vec<Node>,

//     // TODO chache size of subtree
//     // subtree_size: usize,

//     // TODO maybe:
//     // parent: &Node,
// }

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

// impl Trie {
//     pub fn new() -> Self {
//         Self { 
//             root: Node::new_leaf(""),
//             tokenize_at: None,
//         }
//     }

//     pub fn with_split_token(token: char) -> Self {
//         Self { 
//             root: Node::new_leaf(""),
//             tokenize_at: Some(token),
//         }
//     }

//     pub fn insert(&mut self, str: &str) {
//         assert!(self.root.try_insert(str, self.tokenize_at));
//     }

//     // TODO pub fn remove(&mut self, Node?)
//     // TODO merge node with child if only single child / merge node with parent if only child

//     pub fn by_levels(&self) -> Vec<(&str, usize)> {
//         let mut result = Vec::new();
//         // Do not include the always empty root node prefix, so iterate over children.
//         for child in &self.root.children {
//             child.by_levels(0, &mut result);
//         }
//         result
        
//         // TODO imperative implementation
//         // let mut level = 0;
//         // let current = self.root;
//         // unimplemented!()
//     }

//     /// Returns (prefix, level, count).
//     pub fn by_levels_with_count(&self) -> Vec<(&str, usize, usize)> {
//         let mut result = Vec::new();
//         // Do not include the always empty root node prefix, so iterate over children.
//         for child in &self.root.children {
//             child.by_levels_with_count(0, &mut result);
//         }
//         result
//         // TODO use iterator, see below
//     }

//     pub fn sort_by_count(&mut self) {
//         self.root.sort_by_count()
//     }

//     pub fn len(&self) -> usize {
//         self.root.len()
//     }

//     // pub fn graphviz(&self) -> String {
//     //     todo!()
//     // }

//     // fn iter(&self) -> impl Iterator<Item=&str> {
//     //     todo!()
//     // }
// }

impl Node {
    fn new_leaf(str: &str) -> Self {
        Self {
            common_prefix: str.into(),
            children: Vec::new(),
        }
    }

    fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }

    fn common_prefix(&self) -> &str {
        &self.common_prefix
    }

//     // TODO make lazy iterator, not collecting into result
//     fn by_levels<'a>(&'a self, level: usize, result: &mut Vec<(&'a str, usize)>) {
//         result.push((&self.common_prefix, level));
//         for child in &self.children {
//             child.by_levels(level+1, result);
//         }
//     }

//     // TODO iterator, rename to iter_with_count()
//     fn by_levels_with_count<'a>(&'a self, level: usize, result: &mut Vec<(&'a str, usize, usize)>) {
//         result.push((&self.common_prefix, level, self.len()));
//         for child in &self.children {
//             child.by_levels_with_count(level+1, result);
//         }
//     }

//     fn len(&self) -> usize {
//         if self.is_leaf() {
//             1
//         } else {
//             self.children.iter().map(|node| node.len()).sum()
//         }
//     }

//     fn sort_by_count(&mut self) {
//         self.children.sort_by_cached_key(|node| std::cmp::Reverse(node.len()));
//         for child in &mut self.children {
//             child.sort_by_count();
//         }
//     }

//     fn try_insert(&mut self, str: &str, tokenize_at: Option<char>) -> bool {
//         let mut common_prefix_len = self.common_prefix
//             // Iterate over unicode scalar values in prefix and input in lock-step.
//             .char_indices()
//             .zip(str.chars())
//             // Stop at the first character difference.
//             .find(|((_, c1), c2)| c1 != c2)
//             // Return the prefix up to the difference...
//             .map(|((byte_pos, _), _)| byte_pos)
//             // ...or the whole string (actually, the shorter of the two), if no difference was found.
//             .unwrap_or(std::cmp::min(self.common_prefix.len(), str.len()));

//         // If the tokenize option is set, only allow "breaks" (i.e., split between prefix and rest)
//         // after said token. Since we already found a common prefix, we can short it to just end
//         // after the token.
//         if let Some(token) = tokenize_at {
//             common_prefix_len = str[..common_prefix_len].rfind(token).map_or(0, |pos| pos+1);
//         }

//         let (common_prefix, rest) = str.split_at(common_prefix_len);

//         // Insertion case A)
//         // This node is a full prefix of the input, so try to insert into one of our children.
//         if common_prefix == &self.common_prefix[..] {
//             // FIXME test with empty insertion or "foo", "foobar", stack overflow?
//             // If this node was a leaf, make it explicit by adding an "empty" child.
//             // if self.is_leaf() {
//             //     self.children.push(Self::new_leaf(""));
//             // }

//             if rest.is_empty() {
//                 unimplemented!("duplicate value");
//             }

//             for child in &mut self.children {
//                 if child.try_insert(rest, tokenize_at) {
//                     return true;
//                 }
//             }
//             self.children.push(Self::new_leaf(rest));
//             return true;
//         }

//         // Insertion case B)
//         // No common prefix, so cannot insert into this sub-trie.
//         if common_prefix.is_empty() {
//             return false;
//         }
        
//         // Insertion case C)
//         // This prefix and the input partially overlap, so split this node into the common prefix,
//         // and insert a new intermediate node with the rest and current children.
//         let (_, prefix_rest) = self.common_prefix.split_at(common_prefix_len);
        
//         let current_children = std::mem::replace(&mut self.children, Vec::new());
//         let new_intermediate = Self {
//             common_prefix: prefix_rest.into(),
//             children: current_children,
//         };

//         self.common_prefix = common_prefix.into();
//         self.children = vec![
//             new_intermediate,
//             Self::new_leaf(rest)
//         ];
//         return true;
//     }

    fn insert(&mut self, str: &str /*, tokenize_at: Option<char> */) {
        fn split_points(s: &str) -> GraphemeIndices {
            const IS_EXTENDED: bool = true;
            s.grapheme_indices(IS_EXTENDED)
        }

        let SplitResult { common_prefix, left_rest, right_rest } = split_prefix_rest(str, &self.common_prefix, split_points);

        
    }

}

#[derive(Debug, PartialEq, Eq)]
struct SplitResult<'a> {
    common_prefix: &'a str,
    left_rest: &'a str,
    right_rest: &'a str,
}

fn split_prefix_rest<'a, F, I>(left: &'a str, right: &'a str, split_points: F) -> SplitResult<'a>
where
    F: Fn(&'a str) -> I,
    I: Iterator<Item = (usize, &'a str)>,
{
    let left_iter = split_points(left);
    let right_iter = split_points(right);

    let difference_start_index = left_iter.zip(right_iter)
        // Stop at the first difference and return its index.
        .find(|((_, c1), (_, c2))| c1 != c2)
        .map(|((left_index, _), (right_index, _))| {
            debug_assert_eq!(left_index, right_index);
            left_index
        })
        // No difference was found, but that could be because the zip-iteration
        // above stopped at the shorter of the two strings.
        .unwrap_or(std::cmp::min(left.len(), right.len()));

    let (common_prefix_left, left_rest) = left.split_at(difference_start_index);
    let (common_prefix_right, right_rest) = right.split_at(difference_start_index);
    debug_assert_eq!(common_prefix_left, common_prefix_right);
    let common_prefix = common_prefix_left;

    SplitResult {
        common_prefix,
        left_rest,
        right_rest,
    }
}

#[test]
fn test_compare() {
    fn split_points(s: &str) -> GraphemeIndices {
        s.grapheme_indices(true)
    }

    let result = split_prefix_rest("", "", split_points);
    assert_eq!(result, SplitResult {
        common_prefix: "",
        left_rest: "",
        right_rest: "",
    }, "empty strings");

    let result = split_prefix_rest("foo", "foo", split_points);
    assert_eq!(result, SplitResult {
        common_prefix: "foo",
        left_rest: "",
        right_rest: "",
    }, "equal strings");

    let result = split_prefix_rest("foo", "foobar", split_points);
    assert_eq!(result, SplitResult {
        common_prefix: "foo",
        left_rest: "",
        right_rest: "bar",
    }, "left is prefix of right");

    let result = split_prefix_rest("foobar", "foo", split_points);
    assert_eq!(result, SplitResult {
        common_prefix: "foo",
        left_rest: "bar",
        right_rest: "",
    }, "right is prefix of left");

    let result = split_prefix_rest("foo", "bar", split_points);
    assert_eq!(result, SplitResult {
        common_prefix: "",
        left_rest: "foo",
        right_rest: "bar",
    }, "no common prefix");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn no_common_prefix() {
        let mut node = Node::new_leaf("ab");
        node.insert("ac");

        assert_eq!(node.common_prefix(), "a");
        assert_eq!(node.children.len(), 2);
        assert_eq!(node.children[0].common_prefix(), "b");
        assert_eq!(node.children[1].common_prefix(), "c");
    }

    // TODO: unicode tests: smileys, German umlauts, etc.
    // TODO: counts, duplicate entries
    // TODO: 
}
