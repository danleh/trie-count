
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

use std::{str::FromStr, cell::RefCell, hint::unreachable_unchecked, ops::Generator, mem::MaybeUninit};

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

trait KeyRepr<'iter, 'trie> {
    const WITH_KEYS: bool;
    fn key(key_parts: &'iter [&'trie str]) -> Self;
}

/// Implementation for not tracking/returning the key at all.
impl KeyRepr<'_, '_> for () {
    const WITH_KEYS: bool = false;
    fn key(_: &[&str]) -> Self {}
}

/// Implementation for returning the key as a `String`.
impl KeyRepr<'_, '_> for String {
    const WITH_KEYS: bool = true;
    fn key(key_parts: &[&str]) -> Self {
        key_parts.join("")
    }
}

/// Implementation for returning the key as a `Vec` of `&str` parts.
impl<'trie> KeyRepr<'_, 'trie> for Vec<&'trie str> {
    const WITH_KEYS: bool = true;
    fn key(key_parts: &[&'trie str]) -> Self {
        key_parts.to_vec()
    }
}

/// Implementation for returning the key as a `&[&str]` slice.
/// This is the most efficient key representation, since it avoids copying the 
/// key parts and does not require a heap allocation for each key.
impl<'iter, 'trie> KeyRepr<'iter, 'trie> for &'iter [&'trie str] {
    const WITH_KEYS: bool = true;
    fn key(key_parts: &'iter [&'trie str]) -> Self {
        key_parts
    }
}

trait ValueRepr<'trie, T> {
    const WITH_INTERIOR: bool;
    fn interior() -> Self;
    fn value(value: &'trie T) -> Self;
}

/// Implementation for only iterating over leaf nodes (which always have a value).
impl<'trie, T> ValueRepr<'trie, T> for &'trie T {
    const WITH_INTERIOR: bool = false;
    fn interior() -> Self {
        unsafe {
            unreachable_unchecked()
        }
    }
    fn value(value: &'trie T) -> Self {
        value
    }
}

/// Implementation for iterating over all nodes, including interior nodes.
impl<'trie, T> ValueRepr<'trie, T> for Option<&'trie T> {
    const WITH_INTERIOR: bool = true;
    fn interior() -> Self {
        None
    }
    fn value(value: &'trie T) -> Self {
        Some(value)
    }
}

pub trait KeyStack<'trie> {
    type Key<'iter> where Self: 'iter;
    fn push_and_get_current<'iter>(&'iter mut self, key_part: &'trie str) -> Self::Key<'iter>;
    fn pop(&mut self);
}

// /// Implementation for not tracking/returning the key at all.
// impl<'trie> KeyStack<'trie> for () {
//     type Key<'iter> = ();
//     fn push_and_get_current(&mut self, _: &str) {}
//     fn pop(&mut self) {}
// }

/// Implementation for returning the key as a `&[&str]` slice.
/// This is the most efficient key representation (if tracking keys at all),
/// since it avoids copying the key parts and does not require a heap allocation
/// for each key.
impl<'trie> KeyStack<'trie> for Vec<&'trie str> {
    type Key<'iter> = &'iter [&'trie str] where 'trie: 'iter;
    fn push_and_get_current<'iter>(&'iter mut self, key_part: &'trie str) -> &'iter [&'trie str] {
        self.push(key_part);
        self.as_slice()
    }
    fn pop(&mut self) {
        self.pop();
    }
}

// impl<'trie> Key<'trie> for String {
//     type KeyStack = Vec<&'trie str>;
// }

// impl<'trie> KeyStack<'trie, String> for Vec<&'trie str> {
//     fn push_and_get_current(&mut self, key_part: &'trie str) -> String {
//         self.push(key_part);
//         self.join("")
//     }
//     fn pop(&mut self) {
//         self.pop();
//     }
// }


// TODO can this even be generic over owning vs ref vs ref_mut?

pub struct Iter<'trie, T> {
    // The parts of the current key, as encountered along the spine of the tree.
    key_parts_stack: Vec<&'trie str>,
    // Essentially a worklist of nodes to process.
    // `None` is used as a marker, to indicate to pop the last element from the
    // current `key_parts_stack`.
    node_stack: Vec<Option<&'trie Node<T>>>,
}

/// Cannot implement the `Iterator` trait because `next` borrows from the iterator itself
/// (when returning the key parts).
impl<'trie, T> Iter<'trie, T> {
    /// Can be configured with:
    /// - `K` to enable/disable returning the key parts, and with which representation.
    /// - `V` to enable/disable returning interior nodes, and with which representation.
    fn next<'iter, K, V>(&'iter mut self) -> Option<(K, V)>
    where
        K: KeyRepr<'iter, 'trie>,
        V: ValueRepr<'trie, T>,
    {
        while let Some(cur_node) = self.node_stack.pop() {
            match cur_node {
                Some(Node::Leaf { key_rest, value }) => {
                    if K::WITH_KEYS {
                        self.node_stack.push(None);
                        self.key_parts_stack.push(key_rest);
                    }
                    let key_parts = self.key_parts_stack.as_slice();
                    return Some((K::key(key_parts), V::value(value)));
                },
                Some(Node::Interior { key_prefix, children }) => {
                    if K::WITH_KEYS {
                        self.node_stack.push(None);
                        self.key_parts_stack.push(key_prefix);
                    }
                    // Process the children next, i.e., depth-first traversal.
                    self.node_stack.extend(children.iter().rev().map(Some));
                    if V::WITH_INTERIOR {
                        let key_parts = self.key_parts_stack.as_slice();
                        return Some((K::key(key_parts), V::interior()));
                    }
                },
                None => {
                    if K::WITH_KEYS {
                        self.key_parts_stack.pop();
                    } else {
                        // SAFETY: This is unreachable, since we only push `None` if `K::WITH_KEYS`.
                        unsafe {
                            unreachable_unchecked();
                        }
                    }
                }
            }
        }
        None
    }
}

#[inline(never)]
pub fn external_iter_value_optimized_unsafe(node: &Node<i32>) -> impl Iterator<Item=&i32> {
    let mut stack: [MaybeUninit<&Node<i32>>; 1024] = unsafe { MaybeUninit::uninit().assume_init() };
    let mut len = 0;
    unsafe { stack.get_unchecked_mut(len).write(node); }
    len += 1;
    std::iter::from_fn(move || {
        while len > 0 {
            len -= 1;
            let cur_node = unsafe { stack.get_unchecked(len).assume_init() };
            match cur_node {
                Node::Leaf { value, .. } => return Some(value),
                Node::Interior { children, .. } => {
                    for child in children.iter().rev() {
                        len += 1;
                        unsafe { stack.get_unchecked_mut(len).write(child); }
                    }
                }
            }
        }
        None
    })
}

#[inline(never)]
pub fn internal_iter_value(node: &Node<i32>, mut f: impl FnMut(&i32)) {
    fn internal_iter_value(node: &Node<i32>, f: &mut impl FnMut(&i32)) {
        match node {
            Node::Leaf { value, .. } => f(value),
            Node::Interior { children, .. } => {
                for child in children {
                    internal_iter_value(child, f);
                }
            }
        }
    }
    internal_iter_value(node, &mut f)
}

pub struct VecKeyIter<'trie, T>(Iter<'trie, T>);

impl<'trie, T> Iterator for VecKeyIter<'trie, T> {
    type Item = (Vec<&'trie str>, &'trie T);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

pub struct StringKeyIter<'trie, T>(Iter<'trie, T>);

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
    let mut iter = root.external_iter_key_parts_vec();
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
    let mut iter = root.external_iter_key_string();
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

    /// Depth-first traversal of the trie, including interior nodes, and with returning key parts.
    fn internal_iter_generic<'trie, KS, F>(
        &'trie self,
        key_parts_stack: &mut KS,
        f: &mut F)
    where
        KS: KeyStack<'trie>,
        F: for <'iter> FnMut(/* key */ KS::Key<'iter>, Option<&'trie T>)
    {
        match self {
            Node::Leaf { key_rest, value } => {
                // let key_rest = key_rest.to_string();
                let key = key_parts_stack.push_and_get_current(key_rest);
                f(key, Some(value));
                key_parts_stack.pop();
            }
            Node::Interior { key_prefix, children } => {
                // let key_prefix = key_prefix.to_string();
                let key = key_parts_stack.push_and_get_current(key_prefix);
                f(key, None);
                for child in children {
                    child.internal_iter_generic(key_parts_stack, f);
                }
                key_parts_stack.pop();
            }
        }
    }

    pub fn internal_iter<'trie, F>(&'trie self, mut f: F)
    where
        F: for<'iter> FnMut(&'iter [&'trie str], Option<&'trie T>)
    {
        // fn internal_iter<'trie, T>(
        //     cur_node: &'trie Node<T>,
        //     key_parts_stack: &mut Vec<&'trie str>,
        //     f: &mut impl FnMut(&[&'trie str], Option<&'trie T>)
        // ) {
        //     match cur_node {
        //         Node::Leaf { key_rest, value } => {
        //             key_parts_stack.push(key_rest);
        //             f(key_parts_stack.as_slice(), Some(value));
        //             key_parts_stack.pop();
        //         }
        //         Node::Interior { key_prefix, children } => {
        //             key_parts_stack.push(key_prefix);
        //             f(key_parts_stack.as_slice(), None);
        //             for child in children {
        //                 internal_iter(child, key_parts_stack, f);
        //             }
        //             key_parts_stack.pop();
        //         }
        //     }
        // }
        self.internal_iter_generic(&mut Vec::new(), &mut f);
    }

    pub fn internal_iter_leafs(&self, mut f: impl FnMut(/* key_parts */&[&str], /* value */ &T)) {
        fn internal_iter<'trie, T>(
            cur_node: &'trie Node<T>,
            key_parts_stack: &mut Vec<&'trie str>,
            f: &mut impl FnMut(&[&'trie str], &'trie T)
        ) {
            match cur_node {
                Node::Leaf { key_rest, value } => {
                    key_parts_stack.push(key_rest);
                    f(key_parts_stack.as_slice(), value);
                    key_parts_stack.pop();
                }
                Node::Interior { key_prefix, children } => {
                    key_parts_stack.push(key_prefix);
                    for child in children {
                        internal_iter(child, key_parts_stack, f);
                    }
                    key_parts_stack.pop();
                }
            }
        }
        internal_iter(self, &mut Vec::new(), &mut f);
    }

    pub fn internal_iter_values_all(&self, mut f: impl FnMut(/* value */ Option<&T>)) {
        fn internal_iter<'trie, T>(
            cur_node: &'trie Node<T>,
            f: &mut impl FnMut(Option<&'trie T>)
        ) {
            match cur_node {
                Node::Leaf { value, .. } => {
                    f(Some(value));
                }
                Node::Interior { children, .. } => {
                    f(None);
                    for child in children {
                        internal_iter(child, f);
                    }
                }
            }
        }
        internal_iter(self, &mut f);
    }

    pub fn internal_iter_values_leafs(&self, mut f: impl FnMut(/* value */ &T)) {
        fn internal_iter<'trie, T>(
            cur_node: &'trie Node<T>,
            f: &mut impl FnMut(&'trie T)
        ) {
            match cur_node {
                Node::Leaf { value, .. } => {
                    f(value);
                }
                Node::Interior { children, .. } => {
                    for child in children {
                        internal_iter(child, f);
                    }
                }
            }
        }
        internal_iter(self, &mut f);
    }

    pub fn external_iter_key_parts(&self) -> Iter<T> {
        Iter {
            key_parts_stack: vec![],
            node_stack: vec![Some(self)],
        }
    }

    // TODO: add external iterator without keys, and with ony leafs.

    // TODO: Not sure we need those two, the consumer can always just create the appropriate key type from the parts.

    pub fn external_iter_key_parts_vec(&self) -> VecKeyIter<T> {
        VecKeyIter(self.external_iter_key_parts())
    }

    pub fn external_iter_key_string(&self) -> StringKeyIter<T> {
        StringKeyIter(self.external_iter_key_parts())
    }

    #[cfg(test)]
    fn to_test_string(&self) -> String
        where T: std::fmt::Display
    {
        use std::fmt::Write;
        let mut str_acc = String::new();
        let mut iter = self.external_iter_key_parts();
        while let Some((key_parts, maybe_value)) = iter.next::<&[&str], Option<&T>>() {
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
