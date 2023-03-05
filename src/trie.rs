
// see https://github.com/michaelsproul/rust_radix_trie/blob/master/examples/string_frequency.rs
// and https://github.com/miedzinski/prefix-tree
// and https://en.wikipedia.org/wiki/Radix_tree

// TODO generalize over generic sequences of T, and values V (instead of str, usize)

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub struct Trie {
//     root: Node,
//     // See `Node::try_insert`.
//     tokenize_at: Vec<char>
// }

// impl Trie {

//     pub fn by_levels(&self) -> Vec<(&str, usize)> {
//         todo!()
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
//         todo!()
//     }

//     // pub fn graphviz(&self) -> String {
//     //     todo!()
//     // }
// }

use std::{str::FromStr, cell::RefCell, hint::unreachable_unchecked};

use unicode_segmentation::{UnicodeSegmentation, GraphemeIndices};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Node<T> {
    Leaf { 
        key_rest: Box<str>,
        value: T,
    },
    Interior {
        key_prefix: Box<str>,
        children: Vec<Node<T>>,
    },

    // TODO: Potential extensions, optimizations.
    // parent: &Node,
    // Cache of the subtree values.
    // subtree_size: usize,

    // TODO: Alternative design: allow interior nodes to have values.
}

pub struct SliceKeyIter<'trie, T> {
    key_parts_stack: Vec<&'trie str>,
    // None == pop an element from the key parts stack.
    node_stack: Vec<Option<&'trie Node<T>>>,
}

trait TrieIterator<T> {
    const WITH_KEYS: bool;
    type Key;
    fn key(key_parts: &[&str]) -> Self::Key;

    const WITH_INTERIOR: bool;
    type Value;
    fn interior() -> Self::Value;
    fn value(value: &T) -> Self::Value;

    fn next<'trie>(&mut self) -> Option<(Self::Key, Self::Value)>;
}

trait KeyRepr<'trie> {
    const WITH_KEYS: bool;
    fn key(key_parts: &[&'trie str]) -> Self;
}

impl<'trie> KeyRepr<'trie> for () {
    const WITH_KEYS: bool = false;
    fn key(_: &[&str]) -> Self {}
}

impl<'trie> KeyRepr<'trie> for Vec<&'trie str> {
    const WITH_KEYS: bool = true;
    fn key(key_parts: &[&'trie str]) -> Self {
        key_parts.to_vec()
    }
}

impl<'trie, 'iter: 'trie> KeyRepr<'trie> for &'iter [&'trie str] {
    const WITH_KEYS: bool = true;
    fn key(key_parts: &'iter [&'trie str]) -> Self {
        key_parts
    }
}

impl<'trie> KeyRepr<'trie> for String {
    const WITH_KEYS: bool = true;
    fn key(key_parts: &[&str]) -> Self {
        key_parts.join("")
    }
}

trait ValueRepr<'trie, T>
where
    Self: 'trie,
{
    const WITH_INTERIOR: bool;
    fn interior() -> Self;
    fn value(value: &'trie T) -> Self;
}

impl<'trie, T> ValueRepr<'trie, T> for &'trie T
where
    // Self: 'trie,
{
    const WITH_INTERIOR: bool = false;
    fn interior() -> Self {
        unsafe {
            unreachable_unchecked();
        }
    }
    fn value(value: &'trie T) -> Self {
        value
    }
}

impl<'trie, T> ValueRepr<'trie, T> for Option<&'trie T> {
    const WITH_INTERIOR: bool = true;
    fn interior() -> Self {
        None
    }
    fn value(value: &'trie T) -> Self {
        Some(value)
    }
}

/// Cannot implement the `Iterator` trait because it borrows from the iterator itself.
impl<'trie, T> SliceKeyIter<'trie, T> {
    /// Can be configured with:
    /// - `K` to enable/disable returning the key parts, and with which representation.
    /// - `V` to enable/disable returning interior nodes, and with which representation.
    fn next<'iter, K, V>(&'iter mut self) -> Option<(K, V)>
    where
        K: KeyRepr<'trie>,
        V: ValueRepr<'trie, T>,
    {
        while let Some(cur_node) = self.node_stack.pop() {
            match cur_node {
                Some(node) => {
                    if K::WITH_KEYS {
                        // After processing of this node is finished, pop its key part again.
                        self.node_stack.push(None);
                    }
                    let (key_part, value) = match node {
                        Node::Leaf { key_rest, value } => (key_rest, Some(value)),
                        Node::Interior { key_prefix, children } => {
                            // Process the children next, i.e., depth-first traversal.
                            self.node_stack.extend(children.iter().rev().map(Some));
                            (key_prefix, None)
                        },
                    };
                    if K::WITH_KEYS {
                        self.key_parts_stack.push(key_part);
                    }
                    let key_repr = K::key(self.key_parts_stack.as_slice());
                    match value {
                        None => if V::WITH_INTERIOR {
                            return Some((key_repr, V::interior()));
                        }
                        Some(value) => {
                            return Some((key_repr, V::value(value)));
                        }
                    }
                }
                None => if K::WITH_KEYS {
                    self.key_parts_stack.pop();
                } else {
                    unsafe {
                        unreachable_unchecked();
                    }
                },
            }
        }
        None
    }
}

pub struct VecKeyIter<'trie, T>(SliceKeyIter<'trie, T>);

impl<'trie, T> Iterator for VecKeyIter<'trie, T> {
    type Item = (Vec<&'trie str>, &'trie T);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

pub struct StringKeyIter<'trie, T>(SliceKeyIter<'trie, T>);

impl<'trie, T> Iterator for StringKeyIter<'trie, T> {
    type Item = (String, &'trie T);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

// ASCII Art of this trie:
// "foo"
// ├── "bar"
// │   └── "" -> 0
// │   └── "qux" -> 1
// ├── "qux" -> 2
// └── "" -> 3

#[cfg(test)]
fn test_trie() -> Node<u32> {
    Node::Interior { 
        key_prefix: "foo".into(), 
        children: vec![
            Node::Interior { 
                key_prefix: "bar".into(), 
                children: vec![
                    Node::Leaf { key_rest: "".into(), value: 0 },
                    Node::Leaf { key_rest: "qux".into(), value: 1 },
                ],
            },
            Node::Leaf { key_rest: "qux".into(), value: 2 },
            Node::Leaf { key_rest: "".into(), value: 3 },
        ],
    }
}

#[test]
fn test_iter_key_parts_vec() {
    let root = test_trie();
    let mut iter = root.iter_key_parts_vec();
    assert_eq!(iter.next(), Some((vec!["foo", "bar"], &0)));
    assert_eq!(iter.next(), Some((vec!["foo", "bar", "qux"], &1)));
    assert_eq!(iter.next(), Some((vec!["foo", "qux"], &2)));
    assert_eq!(iter.next(), Some((vec!["foo"], &3)));
    assert_eq!(iter.next(), None);
}

// FIXME
// #[test]
// fn test_iter_lending() {
//     let root = test_trie();
//     let mut iter = root.iter_key_parts();
//     assert_eq!(iter.next(), Some((&["foo", "bar"][..], &0)));
//     assert_eq!(iter.next(), Some((&["foo", "bar", "qux"][..], &1)));
//     assert_eq!(iter.next(), Some((&["foo", "qux"][..], &2)));
//     assert_eq!(iter.next(), Some((&["foo"][..], &3)));
//     assert_eq!(iter.next(), None);
// }

#[test]
fn test_iter_key_string() {
    let root = test_trie();
    let mut iter = root.iter_key_string();
    assert_eq!(iter.next(), Some(("foobar".into(), &0)));
    assert_eq!(iter.next(), Some(("foobarqux".into(), &1)));
    assert_eq!(iter.next(), Some(("fooqux".into(), &2)));
    assert_eq!(iter.next(), Some(("foo".into(), &3)));
    assert_eq!(iter.next(), None);
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InsertResult<T> {
    Ok,
    NotAPrefix { value: T },
    Duplicate { old_value: T },
}

#[cfg(test)]
const TEST_INDENT: &str = "  ";
#[cfg(test)]
const TEST_DELIM: &str = ":";

impl<T> Node<T> {
    pub fn new_leaf(str: &str, value: T) -> Self {
        Node::Leaf {
            key_rest: str.into(),
            value,
        }
    }

    pub fn common_prefix(&self) -> &str {
        match self {
            Node::Leaf { key_rest, .. } => key_rest,
            Node::Interior { key_prefix: key_common_prefix, .. } => key_common_prefix,
        }
    }

    pub fn children(&self) -> impl Iterator<Item=&Node<T>> {
        match self {
            Node::Leaf { .. } => [].iter(),
            Node::Interior { children, .. } => children.iter(),
        }
    }

    pub fn children_mut(&mut self) -> impl Iterator<Item=&mut Node<T>> {
        match self {
            Node::Leaf { .. } => [].iter_mut(),
            Node::Interior { children, .. } => children.iter_mut(),
        }
    }

    pub fn iter_key_parts(&self) -> SliceKeyIter<T> {
        SliceKeyIter {
            key_parts_stack: vec![],
            node_stack: vec![Some(self)],
        }
    }

    pub fn iter_key_parts_vec(&self) -> VecKeyIter<T> {
        VecKeyIter(self.iter_key_parts())
    }

    pub fn iter_key_string(&self) -> StringKeyIter<T> {
        StringKeyIter(self.iter_key_parts())
    }

    #[cfg(test)]
    fn to_test_string(&self) -> String
        where T: std::fmt::Display
    {
        use std::fmt::Write;
        let mut str_acc = String::new();
        let mut iter = self.iter_key_parts();
        while let Some((key_parts, maybe_value)) = iter.next::<true, true>() {
            let level = key_parts.len() - 1;
            for _ in 0..level {
                str_acc.push_str(TEST_INDENT);
            }
            write!(str_acc, "{:?}", key_parts.last().unwrap()).unwrap();
            if let Some(value) = maybe_value { // Leaf.
                write!(str_acc, "{TEST_DELIM}{value}").unwrap();
            }
            str_acc.push('\n');
        }
        str_acc.pop(); // Remove trailing newline.
        str_acc
    }

    // "foo"
    //   "bar"
    //     ""
    //       "qux":1
    //       "":2
    //       "quz":3
    //   "test"
    //     "qux":2
    //   "":3

    #[cfg(test)]
    fn from_test_string(str: &str) -> Self
        where T: FromStr,
              <T as FromStr>::Err: std::fmt::Debug,
    {
        fn parse_line<T>(mut line: &str) -> (isize, &str, Option<T>)
            where
                T: FromStr,
                <T as FromStr>::Err: std::fmt::Debug
        {
            let mut level = 0;
            while let Some(rest) = line.strip_prefix(TEST_INDENT) {
                line = rest;
                level += 1;
            }

            let (key_part, value) = match line.rsplit_once(TEST_DELIM) {
                Some((key_part, value_str)) => {
                    let value: T = value_str.parse().unwrap();
                    (key_part, Some(value))
                }
                None => (line, None),
            };

            let key = key_part.strip_prefix('"').unwrap().strip_suffix('"').unwrap();

            (level, key, value)
        }

        let mut subtries = Vec::new();

        for line in str.lines().rev() {
            let (level, key_part, maybe_value) = parse_line::<T>(line);

            match maybe_value {
                Some(value) => {
                    subtries.push((level, Node::Leaf { key_rest: key_part.into(), value }));
                },
                None => {
                    let mut children = Vec::new();
                    while let Some((subtrie_level, _)) = subtries.last() {
                        if *subtrie_level == level + 1 {
                            // Subtrie is child of current node at `level`.
                            children.push(subtries.pop().unwrap().1);
                        } else if *subtrie_level <= level {
                            break;
                        } else if *subtrie_level >= level + 2 {
                            panic!("missing intermediate node in trie");
                        } else {
                            unreachable!();
                        }
                    }
                    subtries.push((level, Node::Interior { key_prefix: key_part.into(), children })); 
                },
            }
        }

        assert_eq!(subtries.len(), 1, "more than one root node");
        subtries.pop().unwrap().1
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

    fn get(&self, key: &str) -> Option<&T> {
        match self {
            Node::Leaf { key_rest, value } =>
                if &key_rest[..] == key {
                    return Some(value)
                },
            Node::Interior { key_prefix, children } => 
                if let Some(key_rest) = key.strip_prefix(&key_prefix[..]) {
                    for child in children {
                        if let Some(value) = child.get(key_rest) {
                            return Some(value);
                        }
                    }
                }
        }
        None
    }

//     fn iter_with_prefix(&self, key: &str) -> impl Iterator<Item=(&str, &T)> {
//         todo!()
//    }

    fn insert(&mut self, key: &str, value: T) -> InsertResult<T> {
        fn split_points(s: &str) -> GraphemeIndices {
            const IS_EXTENDED: bool = true;
            s.grapheme_indices(IS_EXTENDED)
        }

        let SplitResult { 
            common_prefix, 
            left_rest: self_rest,
            right_rest: key_rest
        } = split_prefix_rest(&self.common_prefix(), key, split_points);

        // No common prefix, so cannot insert into this sub-trie.
        if common_prefix.is_empty() {
            // Try again to insert at another sibling.
            return InsertResult::NotAPrefix { value };
        }

        // use NodeData::*;
        // match (&mut self.data, self_rest.is_empty(), key_rest.is_empty()) {
        //     (Leaf(old_value), true, true) => {
        //         // The insertion is fully contained in this node, so it is a duplicate.
        //         let old_value = std::mem::replace(old_value, value);
        //         return InsertResult::Duplicate { old_value };
        //     },
        //     (Interior { children }, true, true) => {
        //         children.push(Node {
        //             common_prefix: key_rest.into(),
        //             data: Leaf(value),
        //         });
        //         return InsertResult::Ok;
        //     },
        //     (Leaf(value), true, false) => {
                
        //     },
        //     (Leaf(value), false, true) => {
                
        //     },
        //     (Leaf(value), false, false) => {
                
        //     },
        //     (Interior { children }, true, false) => todo!(),
        //     (Interior { children }, false, true) => todo!(),
        //     (Interior { children }, false, false) => todo!(),

        //     // (true, true) => {
        //     //     todo!();
        //     //     // The insertion is fully contained in this node, so this is a duplicate.
        //     //     // let old_value = std::mem::replace(&mut self.value, value);
        //     //     // return InsertResult::Duplicate { old_value };
        //     // },
        //     // (true, false) => todo!(),
        //     // (false, true) => todo!(),
        //     // (false, false) => todo!(),
        // }

        // // The input is already contained in this node, so we're done.
        // if to_insert_rest.is_empty() {
        //     return true;
        //     // TODO: allow for duplicates by adding a count field to the node.
        // }

        // This node is a full prefix of the input, so try to insert into one of our children.
        // if self_rest.is_empty() {
        //     // Try to insert into one of our children.
        //     for child in &mut self.children {
        //         if child.insert(to_insert_rest) {
        //             return true;
        //         }
        //     }

        //     // If no child accepted the insertion, add a new leaf.
        //     self.children.push(Self::new_leaf(to_insert_rest));
        //     return true;
        // }

        // // This node is a partial prefix of the input, so split this node
        // // and insert a new intermediate node with the rest and current children.
        // let new_intermediate = Self {
        //     common_prefix: self_rest.into(),
        //     children: std::mem::take(&mut self.children),
        // };
        // self.children = vec![
        //     new_intermediate,
        //     Self::new_leaf(to_insert_rest)
        // ];
        // self.common_prefix = common_prefix.into();
        
        todo!()
    }

}

#[derive(Debug, PartialEq, Eq)]
struct SplitResult<'a> {
    common_prefix: &'a str,
    left_rest: &'a str,
    right_rest: &'a str,
}

fn split_prefix_rest<'a, F, I, T>(left: &'a str, right: &'a str, split_points: F) -> SplitResult<'a>
where
    F: Fn(&'a str) -> I,
    I: Iterator<Item = (usize, T)>,
    T: PartialEq
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

#[cfg(test)]
mod test {
    use std::assert_matches::assert_matches;

    use super::*;

    #[test]
    fn test_to_string() {
        let root = test_trie();
        let actual = root.to_test_string();
        let expected = r#""foo"
  "bar"
    "":0
    "qux":1
  "qux":2
  "":3"#;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_from_string() {
        let expected = test_trie();
        let string = expected.to_test_string();
        let actual = Node::from_test_string(&string);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_split_prefix_rest() {
        let result = split_prefix_rest("", "", str::char_indices);
        assert_eq!(result, SplitResult {
            common_prefix: "",
            left_rest: "",
            right_rest: "",
        }, "empty strings");

        let result = split_prefix_rest("foo", "foo", str::char_indices);
        assert_eq!(result, SplitResult {
            common_prefix: "foo",
            left_rest: "",
            right_rest: "",
        }, "equal strings");

        let result = split_prefix_rest("foo", "foobar", str::char_indices);
        assert_eq!(result, SplitResult {
            common_prefix: "foo",
            left_rest: "",
            right_rest: "bar",
        }, "left is prefix of right");

        let result = split_prefix_rest("foobar", "foo", str::char_indices);
        assert_eq!(result, SplitResult {
            common_prefix: "foo",
            left_rest: "bar",
            right_rest: "",
        }, "right is prefix of left");

        let result = split_prefix_rest("foo", "bar", str::char_indices);
        assert_eq!(result, SplitResult {
            common_prefix: "",
            left_rest: "foo",
            right_rest: "bar",
        }, "no common prefix");

        let result = split_prefix_rest("foo", "föö", |s| s.grapheme_indices(true));
        assert_eq!(result, SplitResult {
            common_prefix: "f",
            left_rest: "oo",
            right_rest: "öö",
        }, "unicode umlauts");

        let result = split_prefix_rest("🇩🇪", "🇩🇪🇪🇺", |s| s.grapheme_indices(true));
        assert_eq!(result, SplitResult {
            common_prefix: "🇩🇪",
            left_rest: "",
            right_rest: "🇪🇺",
        }, "unicode country flags");
    }

    #[test]
    fn insert_root() {
        // ASCII art of trie before:
        // "foo" -> 1
        let mut root = Node::new_leaf("foo", 1);
        assert_matches!(root.insert("foobar", 2), InsertResult::Ok);
        // ASCII art of trie after:
        // "foo" -> 1
        //   "bar" -> 2
        assert_eq!(root, Node::Interior {
            key_prefix: "foo".into(),
            children: vec![
                Node::Leaf {
                    key_rest: "".into(),
                    value: 1,
                },
                Node::Leaf {
                    key_rest: "bar".into(),
                    value: 2,
                },
            ]
        });
    }

    // #[test]
    // fn test_insert_empty() {
    //     let mut node = Node::new_leaf("", 0);
    //     assert!(node.insert("foobar"));
    //     assert_eq!(node.common_prefix(), "");
    //     assert_eq!(node.children().count(), 1);
    //     assert_eq!(node.children().next().unwrap().common_prefix(), "foobar");
    // }

    // #[test]
    // fn test_insert_duplicate() {
    //     let mut node = Node::new_leaf("foobar");
    //     assert!(node.insert("foobar"));
    //     assert_eq!(node.common_prefix(), "foobar");
    //     assert!(node.children.is_empty());
    // }

    // #[test]
    // fn test_insert_longer() {
    //     let mut node = Node::new_leaf("foo");
    //     assert!(node.insert("foobar"));
    //     assert_eq!(node.common_prefix(), "foo");
    //     assert_eq!(node.children.len(), 1);
    //     assert_eq!(node.children[0].common_prefix(), "bar");
    //     assert!(node.children[0].children.is_empty());
    // }

    // #[test]
    // fn test_insert_split_shorter() {
    //     let mut node = Node::new_leaf("foobar");
    //     assert!(node.insert("foo"));
    //     assert_eq!(node.common_prefix(), "foo");
    //     assert_eq!(node.children.len(), 2);
    //     assert_eq!(node.children[0].common_prefix(), "");
    //     assert!(node.children[0].children.is_empty());
    //     assert_eq!(node.children[1].common_prefix(), "bar");
    //     assert!(node.children[1].children.is_empty());
    // }

    // TODO: unicode tests: smileys, German umlauts, etc.
    // TODO: counts, duplicate entries
    // TODO: 
}
