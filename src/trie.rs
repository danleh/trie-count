
// see https://github.com/michaelsproul/rust_radix_trie/blob/master/examples/string_frequency.rs
// and https://github.com/miedzinski/prefix-tree
// and https://en.wikipedia.org/wiki/Radix_tree

use std::{str::FromStr, marker::PhantomData, iter::Sum};

use unicode_segmentation::{UnicodeSegmentation, GraphemeIndices};

// TODO: generalize over generic sequences of K (e.g., bytes) instead of just `&str`.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trie<T, F> {
    root: Node<T>,
    /// Determines at which points the key string may be split, e.g., only at '/', only at 
    /// unicode grapheme cluster boundaries, or at any character boundary.
    key_split_points: F,
}

impl<T, F, I, P> Trie<T, F>
where
    F: Fn(&str) -> I,
    I: Iterator<Item = (usize, P)>,
    P: PartialEq
{
    pub fn new(key_split_points: F) -> Self {
        Self {
            root: Node::new_root(),
            key_split_points,
        }
    }

    pub fn len(&self) -> usize {
        self.root.len()
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_empty()
    }

    pub fn clear(&mut self) {
        self.root = Node::new_root();
    }

    pub fn insert(&mut self, key: &str, value: T) -> Option<T> {
        match self.root.insert::<true>(key, value) {
            InsertResult::Ok => None,
            InsertResult::Replaced { old_value } => Some(old_value),
            InsertResult::NoPrefix { .. } => unreachable!("not possible when inserting into the root node"),
        }
    }

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
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Node<T> {
    key_part: Box<str>,
    data: NodeData<T>,

    // TODO: Potential extensions, optimizations.
    // parent: &Node,
    // Cache of the subtree values.
    // subtree_size: usize,

    // TODO: Alternative design: allow interior nodes to have values.
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeData<T> {
    Leaf(T),
    Interior(Vec<Node<T>>),
}

// The `KeyStack` trait is essentially a lending iterator, because it returns a key representation
// that can borrow not only from the trie, but also from the key stack itself.
// This is a trait with multiple implementations, e.g., one where the keys are not tracked at all
// (essentially nops, optimized away), and one where keys are tracked in an auxiliary stack.
// Unfortunately, this trait requires GATs (generic associated types), which even after 
// stabilization suffer from a serious compiler bug/limitation, namely that lifetimes in GATs lead
// to an inferred 'static bound for the closure type in the internal iterator functions below :(.
// See https://blog.rust-lang.org/2022/10/28/gats-stabilization.html#implied-static-requirement-from-higher-ranked-trait-bounds
// Hence, we rely on an encoding/polyfill of lifetime-GATs that work even before Rust 1.65 and
// which actually do NOT suffer from this limitation!
// See https://sabrinajewson.org/blog/the-better-alternative-to-lifetime-gats#the-better-gats
// and https://github.com/danielhenrymantilla/nougat.rs.
// I didn't want to  to include a whole dependency (nougat.rs) just for essentially two lines of
// code (the additional trait and weird default type parameter), so I used the method described
// by Sabrina Jewson in her blog above. Great work and thanks to her for sharing this!
// This trait is just to avoid duplicated implementations, so I did not use the sealed bounds
// variant that she describes as well, since it adds even more complexity.
pub trait KeyWithLifetime<'this, ImplicitBounds = &'this Self> {
    type Key;
}

pub trait KeyStack<'trie> : for<'any /* where Self: 'any */> KeyWithLifetime<'any> {
    fn push(&mut self, key_part: &'trie str);
    fn get_current(&self) -> <Self as KeyWithLifetime>::Key;
    fn pop(&mut self);
}

/// Implementation for not tracking/returning the key at all.
impl KeyWithLifetime<'_> for () {
    type Key = ();
}
impl KeyStack<'_> for () {
    fn push(&mut self, _: &str) {}
    fn get_current(&self) {}
    fn pop(&mut self) {}
}

/// Implementation for returning the key as a `&[&str]` slice.
/// This is the most efficient key representation (if tracking keys at all), since it avoids copying
/// the key parts and does not require a heap allocation for each key/iteration.
impl<'this, 'trie> KeyWithLifetime<'this> for Vec<&'trie str> {
    type Key = &'this [&'trie str];
}
impl<'trie> KeyStack<'trie> for Vec<&'trie str> {
    fn push(&mut self, key_part: &'trie str) {
        self.push(key_part);
    }
    fn get_current(&self) -> <Self as KeyWithLifetime>::Key {
        self.as_slice()
    }
    fn pop(&mut self) {
        self.pop();
    }
}

/// Trait for abstracting over values, either both leafs and interior nodes, or only leafs.
pub trait Value<'trie, T> {
    const WITH_INTERIOR: bool;
    fn leaf(value: &'trie T) -> Self;
    fn interior() -> Self;
}

/// Implementation for only iterating over leaf nodes (which always have a value).
impl<'trie, T> Value<'trie, T> for &'trie T {
    const WITH_INTERIOR: bool = false;
    fn leaf(value: &'trie T) -> Self { value }
    fn interior() -> Self { unreachable!() }
}

/// Implementation for iterating over all nodes, including interior nodes (which are `None`).
impl<'trie, T: 'trie> Value<'trie, T> for Option<&'trie T> {
    const WITH_INTERIOR: bool = true;
    fn leaf(value: &'trie T) -> Self { Some(value) }
    fn interior() -> Self { None }
}


/// External pre-order depth-first iterator, configurable by `K` and `V`.
pub struct Iter<'trie, T, K, V> {
    /// A worklist of nodes still to process.
    /// `None` is used as a marker to indicate to pop the last element from the `key_parts_stack`.
    node_stack: Vec<Option<&'trie Node<T>>>,

    /// The parts of the current key, as encountered along the spine of the tree.
    key_parts_stack: K,

    /// Statically encodes the value representation we want to return from the iterator.
    value_representation: PhantomData<V>,
}

// Cannot implement the `Iterator` trait from the standard library because `next` borrows from the
// iterator itself (when returning the key parts).
impl<'trie, T, K, V> Iter<'trie, T, K, V>
where
    K: KeyStack<'trie> + Default,
    V: Value<'trie, T>,
{
    pub fn new(root: &'trie Node<T>) -> Self {
        Self {
            node_stack: vec![Some(root)],
            key_parts_stack: K::default(),
            value_representation: PhantomData,
        }
    }

    #[allow(clippy::needless_lifetimes)]
    pub fn next<'next>(&'next mut self) -> Option<(<K as KeyWithLifetime<'next>>::Key, V)> {
        while let Some(cur_node) = self.node_stack.pop() {
            match cur_node {
                Some(Node::Leaf { key_rest, value }) => {
                    self.node_stack.push(None);
                    self.key_parts_stack.push(key_rest);

                    return Some((self.key_parts_stack.get_current(), V::leaf(value)));
                }
                Some(Node::Interior { key_prefix, children }) => {
                    self.node_stack.push(None);
                    // Process the children next, i.e., depth-first traversal.
                    self.node_stack.extend(children.iter().rev().map(Some));
                    self.key_parts_stack.push(key_prefix);

                    if V::WITH_INTERIOR {
                        return Some((self.key_parts_stack.get_current(), V::interior()));
                    }
                }
                None => self.key_parts_stack.pop(),
            }
        }
        None
    }
}

/// ASCII Art of this trie:
/// "foo"
/// ├── "bar"
/// │   └── "" -> 0
/// │   └── "qux" -> 1
/// ├── "qux" -> 2
/// └── "" -> 3
#[cfg(test)]
fn test_trie() -> Node<u32> {
    Node::Interior { 
        key_prefix: "foo".into(), 
        children: vec![
            Node::Interior { 
                key_prefix: "bar".into(), 
                children: vec![
                    Node::new_leaf("", 0),
                    Node::new_leaf("qux", 1),
                ],
            },
            Node::new_leaf("qux", 2),
            Node::new_leaf("", 3),
        ],
    }
}

#[test]
fn test_iter_lending() {
    let root = test_trie();
    let mut iter = root.external_iter_items_leafs();
    assert_eq!(iter.next(), Some((&["foo", "bar", ""][..], &0)));
    assert_eq!(iter.next(), Some((&["foo", "bar", "qux"][..], &1)));
    assert_eq!(iter.next(), Some((&["foo", "qux"][..], &2)));
    assert_eq!(iter.next(), Some((&["foo", ""][..], &3)));
    assert_eq!(iter.next(), None);
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InsertResult<T> {
    Ok,
    Replaced { old_value: T },
    NoPrefix { value: T }
}

// #[cfg(test)]
const TEST_INDENT: &str = "  ";
// #[cfg(test)]
const TEST_DELIM: &str = ":";

impl<T> Node<T> {

    // Constructors:

    pub fn new_leaf(str: &str, value: T) -> Self {
        Node {
            key_part: str.into(),
            data: NodeData::Leaf(value),
        }
    }

    pub fn new_root() -> Self {
        Node {
            key_part: "".into(),
            data: NodeData::Interior(vec![]),
        }
    }

    // No constructor for interior nodes, because they are only created when splitting nodes.
    // Check `splice_interior` for details.


    // Accessors:

    pub fn children(&self) -> std::slice::Iter<Node<T>> {
        match &self.data {
            NodeData::Leaf(_) => [].iter(),
            NodeData::Interior(children) => children.iter(),
        }
    }

    pub fn children_mut(&mut self) -> std::slice::IterMut<Node<T>> {
        match &mut self.data {
            NodeData::Leaf(_) => [].iter_mut(),
            NodeData::Interior(children) => children.iter_mut(),
        }
    }


    // Other common functions for data structures:
    
    /// Returns the number of mappings (i.e., leafs) in the trie.
    pub fn len(&self) -> usize {
        match &self.data {
            NodeData::Leaf(_) => 1,
            NodeData::Interior { children, .. } => children.iter().map(Self::len).sum(),
        }
    }

    pub fn is_empty(&self) -> bool {
        // This is faster then checking `self.len() == 0`, because it does not need to traverse the
        // whole trie.
        match self {
            Node::Leaf { .. } => false,
            Node::Interior { children, .. } => children.is_empty(),
        }
    }


    // Iterators:

    /// Generic interior pre-order depth-first traversal of the trie, configurable by `K` and `V`.
    fn internal_iter_generic<'trie, K, V, F>(&'trie self, key_parts_stack: &mut K, f: &mut F)
    where
        K: KeyStack<'trie>,
        V: Value<'trie, T>,
        F: for<'any> FnMut(<K as KeyWithLifetime<'any>>::Key, V)
    {
        match self {
            Node::Leaf { key_rest, value } => {
                key_parts_stack.push(key_rest);
                f(key_parts_stack.get_current(), V::leaf(value));
                key_parts_stack.pop();
            }
            Node::Interior { key_prefix, children } => {
                key_parts_stack.push(key_prefix);
                if V::WITH_INTERIOR {
                    f(key_parts_stack.get_current(), V::interior());
                }
                for child in children {
                    child.internal_iter_generic(key_parts_stack, f);
                }
                key_parts_stack.pop();
            }
        }
    }

    /// Depth-first traversal of the trie, including interior nodes, and with key parts.
    /// The value passed to `f` is `None` for interior nodes and `Some(&T)` for leafs.
    pub fn internal_iter_items(&self, mut f: impl FnMut(/* key_parts */ &[&str], /* value */ Option<&T>)) {
        self.internal_iter_generic(&mut Vec::new(), &mut f);
    }

    /// Depth-first traversal of the trie, _not_ including interior nodes, and with key parts.
    /// Since `f` is only called for leafs, the passed value is always a valid `&T`.
    pub fn internal_iter_items_leafs(&self, mut f: impl FnMut(/* key_parts */ &[&str], /* value */ &T)) {
        self.internal_iter_generic(&mut Vec::new(), &mut f);
    }

    /// Depth-first traversal of the trie, without key parts.
    /// Since interior nodes have no value associated with them, they are not included.
    pub fn internal_iter_values(&self, mut f: impl FnMut(/* value */ &T)) {
        self.internal_iter_generic(&mut (), &mut |(), value| f(value));
    }

    /// Returns a depth-first iterator over the trie, including interior nodes, and with key parts.
    /// The iterator item is `None` for interior nodes and `Some(&T)` for leafs.
    pub fn external_iter_items(&self) -> Iter<T, /* key_parts_stack */ Vec<&str>, Option<&T>> {
        Iter::new(self)
    }

    /// Returns a depth-first iterator over the trie, _not_ including interior nodes, and with key parts.
    /// Since the iterator includes only leafs, the returned value is always a valid `&T`.
    pub fn external_iter_items_leafs(&self) -> Iter<T, /* key_parts_stack */ Vec<&str>, &T> {
        Iter::new(self)
    }

    /// Returns a depth-first iterator over the trie, without key parts.
    /// Since interior nodes have no value associated with them, they are not included.
    pub fn external_iter_values(&self) -> Iter<T, /* no key_parts_stack */ (), &T> {
        Iter::new(self)
    }


    // Utility functions for testing:

    #[cfg(test)]
    fn to_test_string(&self) -> String
        where T: std::fmt::Debug
    {
        use std::fmt::Write;
        let mut str_acc = String::new();
        let mut iter = self.external_iter_items();
        while let Some((key_parts, maybe_value)) = iter.next() {
            let level = key_parts.len() - 1;
            for _ in 0..level {
                str_acc.push_str(TEST_INDENT);
            }
            write!(str_acc, "{:?}", key_parts.last().unwrap()).unwrap();
            if let Some(value) = maybe_value { // Leaf.
                write!(str_acc, "{TEST_DELIM}{value:?}").unwrap();
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

    // #[cfg(test)]
    pub fn from_test_string(str: &str) -> Self
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
                    subtries.push((level, Node::new_leaf(key_part, value)));
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

//     fn sort_by_count(&mut self) {
//         self.children.sort_by_cached_key(|node| std::cmp::Reverse(node.len()));
//         for child in &mut self.children {
//             child.sort_by_count();
//         }
//     }


    // Finding, inserting, and removing key value mappings:

    /// Returns `Some(T)` if there is a value associated with the exact given key, 
    /// or `None` if no such value exists.
    pub fn get_exact<'trie>(&'trie self, key_query: &'_ str) -> Option<&'trie T> {
        match self {
            Node::Leaf { key_rest, value } =>
                if &key_rest[..] == key_query {
                    return Some(value)
                },
            Node::Interior { key_prefix, children } => 
                if let Some(key_query) = key_query.strip_prefix(&key_prefix[..]) {
                    for child in children {
                        if let Some(value) = child.get_exact(key_query) {
                            return Some(value);
                        }
                    }
                }
        }
        None
    }

    /// Returns the first value for which the given `key_query` is a prefix of the full key, 
    /// or `None` if no such value exists.
    /// Also returns the key.
    pub fn get_first_with_prefix<'trie>(&'trie self, key_query: &'_ str) -> Option<(/* key */ String, &'trie T)> {
        if let Some((key_matched, subtrie)) = self.get_all_with_prefix(key_query) {
            if let Some((key_parts, value)) = subtrie.external_iter_items_leafs().next() {
                // I would hope that the string allocation and concetenation is optimized away
                // if the caller does not use the key, but I am not sure.
                let mut key = key_matched.to_owned();
                for part in key_parts {
                    key.push_str(part);
                }
                return Some((key, value));
            }
        }
        None
    }

    /// Returns the subtrie for which the given `key_query` is a prefix of the contained keys,
    /// or `None` if none with this prefix exists.
    /// Also returns the part of the key that was matched by parent nodes of the returned subtrie,
    /// i.e., you can concatenate it with the key parts in the returned subtrie to obtain the full keys.
    pub fn get_all_with_prefix<'trie, 'query>(&'trie self, key_query: &'query str) 
    -> Option<(/* key_matched */ &'query str, /* matching_subtrie */ &'trie Node<T>)> {
        fn get_all_with_prefix<'trie, T>(cur_node: &'trie Node<T>, key_query: &'_ str, key_matched_len: usize) 
        -> Option<(/* key_matched_len */ usize, /* matching_subtrie */ &'trie Node<T>)> {
            match cur_node {
                Node::Leaf { key_rest, value: _ } =>
                    if key_rest.starts_with(key_query) {
                        return Some((key_matched_len, cur_node))
                    },
                Node::Interior { key_prefix: self_key, children } =>
                    match split_prefix_rest(key_query, self_key, str::char_indices) {
                        // The queried key was fully a prefix of the current node, so return the whole subtrie.
                        SplitResult { common_prefix: _, left_rest: "", right_rest: _ } =>
                            return Some((key_matched_len, cur_node)),
                        // The current node "consumed" a prefix of the queried key, so search further in the children.
                        SplitResult { common_prefix, left_rest: key_query, right_rest: "" } =>
                            for child in children {
                                if let Some((key_matched_len, node)) = get_all_with_prefix(child, key_query, key_matched_len + common_prefix.len()) {
                                    return Some((key_matched_len, node));
                                }
                            },
                        // Both have a non-empty rest after splitting off the `common_prefix`, 
                        // so neither was a prefix of the other, hence stop the search.
                        SplitResult { .. } => return None
                    }
            }
            None
        }
        get_all_with_prefix(self, key_query, 0)
            .map(|(key_matched_len, subtrie)| (&key_query[..key_matched_len], subtrie))
    }

    // Inserts a fresh interior node of which the old `self` will become a child. That is, go from:
    //  self
    // to:
    //  Node::Interior { interior_key, children: [self, other_child] }
    // TODO: Maybe insert this into the `insert` method code.
    fn splice_interior(&mut self, interior_key: Box<str>, other_child: Node<T>) {
        let new_interior = Node::Interior {
            key_prefix: interior_key,
            children: Vec::with_capacity(2),
        };
        let old_self = std::mem::replace(self, new_interior);
        match self /* == new_interior */ {
            Node::Interior { children, .. } => {
                children.push(old_self);
                children.push(other_child);
            }
            _ => unreachable!("we just replaced self with a new interior node")
        }
    }

    // TODO: Factor out the common two last cases from leafs and interior nodes, in which we 
    // neither access `Leaf::value` nor `Interior::children`, hence the same code.
    pub fn insert<const IS_ROOT: bool>(&mut self, insert_key: &str, insert_value: T) -> InsertResult<T> {
        match self {
            Node::Leaf { key_rest: self_key, value } => {
                match split_prefix_rest(insert_key, self_key, str::char_indices) {
                    // The insertion key is equal to the current node's key, so replace the value.
                    SplitResult { common_prefix: _, left_rest: "", right_rest: "" } => {
                        let old_value = std::mem::replace(value, insert_value);
                        InsertResult::Replaced { old_value }
                    }

                    // The insertion key and the current node's key don't have a common prefix,
                    // now it depends whether this insertion is "allowed" or not:
                    // Only the root node is allowed to have an empty interior key,
                    // in all other cases we hand back to the parent, which shall try to insert somewhere else.
                    // In case of the root node, the match guard will always be false and hence fall through
                    // to the next match arm (which will then split the root node, 
                    // potentially introducing a root with an empty key, which is allowed).
                    SplitResult { common_prefix: "", left_rest: _insert_key, right_rest: _self_key } if !IS_ROOT => {
                        InsertResult::NoPrefix { value: insert_value }
                    }

                    // Split this node into an interior node with the common prefix as key,
                    // and two leaf nodes as children, one for self's old value and one for the inserted value.
                    SplitResult { common_prefix, left_rest: insert_key_rest, right_rest: self_key_rest } => {
                        let common_prefix = common_prefix.into();
                        let new_leaf = Node::new_leaf(insert_key_rest, insert_value);
                        *self_key = self_key_rest.into();
                        self.splice_interior(common_prefix, new_leaf);
                        InsertResult::Ok
                    }
                }
            }
            Node::Interior { key_prefix: self_key, children } => {
                match split_prefix_rest(insert_key, self_key, str::char_indices) {
                    // Interior node with empty key part and no children is only allowed for the 
                    // (initial) "empty" root node.
                    SplitResult { common_prefix: "", left_rest: insert_key, right_rest: "" } if children.is_empty() => {
                        assert!(IS_ROOT);
                        // Replace the "empty" root with a leaf node.
                        *self = Node::new_leaf(insert_key, insert_value);
                        InsertResult::Ok
                    }

                    // The current node's key is a prefix of the `insert_key`,
                    // so this is the right subtrie to insert.
                    SplitResult { common_prefix: _stripped, left_rest: insert_key_rest, right_rest: "" } => {
                        // Try to insert into the children.
                        let mut insert_value = insert_value;
                        for child in children.iter_mut() {
                            match child.insert::<false>(insert_key_rest, insert_value) {
                                // Not successful, so try the next child.
                                InsertResult::NoPrefix { value } => insert_value = value,
                                // Successful (either replaced or inserted a new leaf node), so return.
                                insert_result => return insert_result
                            }
                        }
 
                        // No child could be found where the insert could take place,
                        // so we must create a new leaf node.
                        let insert_new_leaf = Node::new_leaf(insert_key_rest, insert_value);
                        children.push(insert_new_leaf);
                        InsertResult::Ok
                    }

                    // Same logic as for the leaf case above: 
                    // The `insert_key` and `self_key` don't have a common prefix,
                    // so this is not the right subtrie to insert, except for root nodes.
                    SplitResult { common_prefix: "", left_rest: _insert_key, right_rest: _self_key } if !IS_ROOT => {
                        InsertResult::NoPrefix { value: insert_value }
                    }

                    // The current node's key and the insertion key have a common prefix,
                    // so we must split the current node.
                    SplitResult { common_prefix, left_rest: insert_key_rest, right_rest: self_key_rest } => {
                        let common_prefix = common_prefix.into();
                        let new_leaf = Node::new_leaf(insert_key_rest, insert_value);
                        *self_key = self_key_rest.into();
                        self.splice_interior(common_prefix, new_leaf);
                        InsertResult::Ok
                    }
                }
            }
    }
    }

    pub fn insert_or_update(&mut self, key: &str, insert_value: T, update: impl FnOnce(&mut T)) -> InsertResult<T> {
        // TODO: Based on `insert`.
        todo!()
    }

    pub fn remove_exact(&mut self, key: &str) -> Option<T> {
        // TODO: Based on `get_exact`. Maybe refactor into a common function that returns a `&mut Node<T>`?
        todo!()
    }

    #[cfg(test)]
    fn assert_invariants<const IS_ROOT: bool>(&self)
    where T: std::fmt::Debug
    {
        if let Node::Interior { key_prefix, children } = self {
            if !IS_ROOT {
                assert!(!key_prefix.is_empty(), "invariant violated: interior nodes (except the root node) must have a non-empty key part\n{self:?}");
                assert!(children.len() > 1, "invariant violated: interior nodes (except the empty root node) must have at least two children\n{self:?}");
            }
            for (i, child1) in children.iter().enumerate() {
                for child2 in &children[i+1..] {
                    let split_result = split_prefix_rest(child1.key_part(), child2.key_part(), str::char_indices);
                    assert!(split_result.common_prefix.is_empty(), "invariant violated: children of interior nodes must not have a common prefix\n{self:?}");
                }
            }
            for child in children {
                child.assert_invariants::<false>();
            }
        }
    }

    /// Sorts the children alphabetically by their key.
    pub fn sort_by_key(&mut self) {
        if let Node::Interior { key_prefix: _, children } = self {
            for child in children.iter_mut() {
                child.sort_by_key();
            }
            children.sort_by(|a, b| a.key_part().cmp(b.key_part()));
        }
    }

    /// Sorts the trie by the result of the given function applied to each node.
    pub fn sort_by_func<F, O>(&mut self, mut f: F)
    where
        F: FnMut(&Node<T>) -> O,
        O: Ord,
    {
        fn sort_by_func<T, F, O>(cur_node: &mut Node<T>, f: &mut F)
        where
            F: FnMut(&Node<T>) -> O,
            O: Ord,
        {
            if let Node::Interior { key_prefix: _, children } = cur_node {
                for child in children.iter_mut() {
                    sort_by_func(child, f);
                }
                children.sort_by_cached_key(f);
            }
        }
        sort_by_func(self, &mut f);
    }

    pub fn fold<F, G, U>(&self, mut f_leaf: F, f_interior: G) -> U
    where
        F: FnMut(&T) -> U,
        G: Fn(U, U) -> U,
    {
        fn fold<T, F, G, U>(cur_node: &Node<T>, f_leaf: &mut F, f_interior: &G) -> U
        where
            F: FnMut(&T) -> U,
            G: Fn(U, U) -> U,
        {
            match cur_node {
                Node::Leaf { key_rest: _, value } => f_leaf(value),
                Node::Interior { key_prefix: _, children } => {
                    // FIXME: Allow an empty trie at the root.
                    children.iter().map(|child| fold(child, f_leaf, f_interior)).reduce(f_interior).expect("empty trie")
                }
            }
        }
        fold::<T, F, G, U>(self, &mut f_leaf, &f_interior)
    }

    pub fn value_sum(&self) -> T
    where
        T: Sum + Copy
    {
        match self {
            Node::Leaf { key_rest: _, value } => *value,
            Node::Interior { key_prefix: _, children } => children.iter().map(Node::value_sum).sum()
        }
    }

    // pub fn sort_by_value_sum(&mut self)
    // where
    //     T: Ord + Sum + Copy
    // {
    //     fn sort_by_value_sum<T>(cur_node: &mut Node<T>) -> T
    //     where
    //         T: Ord + Sum + Copy
    //     {
    //         match cur_node {
    //             Node::Leaf { key_rest: _, value } => *value,
    //             Node::Interior { key_prefix: _, children } => {
    //                 let sums: Vec<T> = children.iter_mut().map(|child| sort_by_value_sum(child)).collect();
    //                 children.sort_by_cached_key(|node| sort_by_value_sum(node));
    //                 sums.into_iter().sum()
    //             }
    //         }
    //     }
    //     sort_by_value_sum(self);
    // }

    // pub fn sort_by_bottomup_value_fold<F, G, O>(&mut self, mut f_leaf: F, mut f_interior: G)
    // where
    //     F: FnMut(&T) -> O,
    //     G: FnMut(O, O) -> O,
    //     O: Ord,
    // {
    //     fn sort_by_bottomup_value_fold<T, F, G, O>(cur_node: &mut Node<T>, f_leaf: &mut F, f_interior: &mut G) -> O
    //     where
    //         F: FnMut(&T) -> O,
    //         G: FnMut(O, O) -> O,
    //         O: Ord,
    //     {
    //         match cur_node {
    //             Node::Leaf { key_rest: _, value } => f_leaf(value),
    //             Node::Interior { key_prefix: _, children } => {
    //                 let o = {
    //                     let (first_child, children) = children.split_first_mut().unwrap();
    //                     let mut o = sort_by_bottomup_value_fold(first_child, f_leaf, f_interior);
    //                     for child in children.iter_mut() {
    //                         let next_o = sort_by_bottomup_value_fold(child, f_leaf, f_interior);
    //                         o = f_interior(o, next_o);
    //                     }
    //                     o
    //                 };
    //                 children.sort_by_cached_key(|child| sort_by_bottomup_value_fold(child, f_leaf, f_interior));
    //                 o
    //             }
    //         }
    //     }
    //     sort_by_bottomup_value_fold::<T, F, G, O>(self, &mut f_leaf, &mut f_interior);
    // }
}

#[derive(Debug, PartialEq, Eq)]
struct SplitResult<'a> {
    common_prefix: &'a str,
    left_rest: &'a str,
    right_rest: &'a str,
}

fn split_prefix_rest<'a, F, I, P>(left: &'a str, right: &'a str, split_points: F) -> SplitResult<'a>
where
    F: Fn(&'a str) -> I,
    I: Iterator<Item = (usize, P)>,
    P: PartialEq
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

    SplitResult { common_prefix, left_rest, right_rest }
}

#[cfg(test)]
mod test {
    use std::{assert_matches::assert_matches, cmp::Reverse, collections::HashMap, ops::RangeInclusive};


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
    fn test_len_and_is_empty() {
        let root: Node<u32> = Node::new_root();
        assert_eq!(root.len(), 0);
        assert!(root.is_empty());

        let root = Node::new_leaf("foobar", 42);
        assert_eq!(root.len(), 1);
        assert!(!root.is_empty());

        let root = test_trie();
        assert_eq!(root.len(), 4);
        assert!(!root.is_empty());
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
    fn test_get_all_with_prefix() {
        let root = test_trie();

        assert_eq!(root.get_all_with_prefix("fooqux"), Some(("foo", (&Node::new_leaf("qux", 2)))));
        assert_eq!(root.get_all_with_prefix("foobarqux"), Some(("foobar", (&Node::new_leaf("qux", 1)))));
        
        assert_eq!(root.get_all_with_prefix("xyz"), None);
        
        assert_eq!(root.get_all_with_prefix("foobarqXYZ"), None);
        assert_eq!(root.get_all_with_prefix("fooo"), None);
        assert_eq!(root.get_all_with_prefix("fo"), Some(("", &root)));
        assert_eq!(root.get_all_with_prefix(""), Some(("", &root)));
    }

    #[test]
    fn test_get_first_with_prefix() {
        let root = test_trie();

        assert_eq!(root.get_first_with_prefix(""), Some(("foobar".into(), &0)));
        assert_eq!(root.get_first_with_prefix("fo"), Some(("foobar".into(), &0)));
        assert_eq!(root.get_first_with_prefix("foob"), Some(("foobar".into(), &0)));
        assert_eq!(root.get_first_with_prefix("foobar"), Some(("foobar".into(), &0)));
        assert_eq!(root.get_first_with_prefix("foobarxyz"), None);
        assert_eq!(root.get_first_with_prefix("foobarqux"), Some(("foobarqux".into(), &1)));
        assert_eq!(root.get_first_with_prefix("fooqux"), Some(("fooqux".into(), &2)));
        assert_eq!(root.get_first_with_prefix("fooxyz"), None);
    }

    #[test]
    fn test_empty_trie() {
        let root: Node<i32> = Node::new_root();
        assert_eq!(root, Node::Interior { key_prefix: "".into(), children: Vec::new() });
    }

    #[test]
    fn test_insert_into_empty_leaf() {
        let mut root = Node::from_test_string(r#""":1"#);
        assert_matches!(root.insert::<true>("foo", 2), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#"""
  "":1
  "foo":2"#));
    }

    #[test]
    fn test_insert_empty_key() {
        let mut root = Node::from_test_string(r#""foo":1"#);
        assert_matches!(root.insert::<true>("", 2), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#"""
  "foo":1
  "":2"#));
    }

    #[test]
    fn test_insert_duplicate_leaf() {
        let mut root = Node::from_test_string(r#""foo":1"#);
        assert_matches!(root.insert::<true>("foo", 2), InsertResult::Replaced { old_value: 1 });
        assert_eq!(root, Node::from_test_string(r#""foo":2"#));
    }

    #[test]
    fn test_insert_split_leaf() {
        let mut root = Node::from_test_string(r#""foo":1"#);
        assert_matches!(root.insert::<true>("foobar", 2), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#""foo"
  "":1
  "bar":2"#));

        let mut root = Node::from_test_string(r#""foobar":1"#);
        assert_matches!(root.insert::<true>("foo", 2), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#""foo"
  "bar":1
  "":2"#));

        let mut root = Node::from_test_string(r#""foo":1"#);
        assert_matches!(root.insert::<true>("bar", 2), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#"""
  "foo":1
  "bar":2"#));
    }

    #[test]
    fn test_insert_into_empty_root() {
        let mut root: Node<i32> = Node::new_root();
        assert_matches!(root.insert::<true>("foo", 1), InsertResult::Ok);
        // The empty interior node shall be replaced by a leaf node.
        assert_eq!(root, Node::from_test_string(r#""foo":1"#));

        let mut root: Node<i32> = Node::new_root();
        assert_matches!(root.insert::<true>("", 1), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#""":1"#));
    }

    #[test]
    fn test_insert_interior() {
        let mut root = Node::from_test_string(r#""foo"
  "bar":1
  "qux":2"#);
        assert_matches!(root.insert::<true>("foozaz", 3), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#""foo"
  "bar":1
  "qux":2
  "zaz":3"#));
    }

    #[test]
    fn test_insert_split_interior() {
        let mut root = Node::from_test_string(r#""foo"
  "bar":1
  "qux":2"#);
        assert_matches!(root.insert::<true>("foobaz", 3), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#""foo"
  "ba"
    "r":1
    "z":3
  "qux":2"#));
    }

    fn random_values(count: usize, max_string_len: usize, charset: RangeInclusive<char>) -> impl Iterator<Item=(String, usize)> {
        use rand::{Rng, distributions::Uniform, prelude::Distribution};
        let char_distribution = Uniform::from(charset);

        let mut rng = rand::thread_rng();

        (0..count).map(move |i| {
            let str_len = rng.gen_range(0..=max_string_len);
            let str: String = char_distribution
                .sample_iter(&mut rng)
                .take(str_len)
                .collect();
            let value = i;
            (str, value)
        })
    }

    #[test]
    fn test_insert_random_strings() {
        let mut root = Node::new_root();
        let mut hashmap_reference = HashMap::new();

        for (str, value) in random_values(20, 5, 'A'..='C') {
            println!("{}", root.to_test_string());

            print!("insert {str:?}:{value}");
            let result = root.insert::<true>(&str, value);
            println!(" ... {result:?}");

            let result_reference = hashmap_reference.insert(str, value);
            match (&result, result_reference) {
                (InsertResult::Ok, None) => {},
                (InsertResult::Replaced { old_value }, Some(old_value_reference)) if *old_value == old_value_reference => {},
                _ => panic!("mismatch between reference HashMap and trie result\nHashMap: {result_reference:?}\ntrie:{result:?}"),
            }

            root.assert_invariants::<true>();
            assert_eq!(root.len(), hashmap_reference.len());
        }
        println!("{}", root.to_test_string());
        
        let mut insertions_sorted: Vec<(String, usize)> = hashmap_reference.into_iter().collect();
        insertions_sorted.sort();

        let mut trie_items_sorted = Vec::new();
        let mut trie_iter = root.external_iter_items_leafs();
        while let Some((str, value)) = trie_iter.next() {
            trie_items_sorted.push((str.join(""), *value));
        }
        trie_items_sorted.sort();

        assert_eq!(trie_items_sorted, insertions_sorted);
        assert_eq!(trie_items_sorted.len(), root.len());
        
        println!("{} items in final trie:", trie_items_sorted.len());
        for (str, value) in trie_items_sorted {
            println!("  {str:?}:{value}");
        }
    }

    #[test]
    fn test_sort_by_key() {
        let mut root: Node<i32> = Node::from_test_string(r#""foo"
  "qux":1
  "bar":2"#);
        root.sort_by_key();
        assert_eq!(root, Node::from_test_string(r#""foo"
  "bar":2
  "qux":1"#));

        let mut root: Node<i32> = Node::from_test_string(r#""foo"
  "bar":1
  "":2"#);
        root.sort_by_key();
        assert_eq!(root, Node::from_test_string(r#""foo"
  "":2
  "bar":1"#));
    }

    #[test]
    fn test_sort_by_key_random() {
        let mut root = Node::new_root();
        let mut hashmap_reference = HashMap::new();
        for (str, value) in random_values(20, 5, 'A'..='C') {
            root.insert::<true>(&str, value);
            hashmap_reference.insert(str, value);
        }
        
        let mut insertions_sorted: Vec<(String, usize)> = hashmap_reference.into_iter().collect();
        insertions_sorted.sort();

        println!("before sort: {}", root.to_test_string());
        root.sort_by_key();
        println!("after sort: {}", root.to_test_string());
                
        let mut trie_iterator_items = Vec::new();
        let mut trie_iter = root.external_iter_items_leafs();
        while let Some((str, value)) = trie_iter.next() {
            trie_iterator_items.push((str.join(""), *value));
        }

        assert_eq!(trie_iterator_items, insertions_sorted);
    }

    #[test]
    fn test_sort_by_value() {
        let mut root: Node<i32> = Node::from_test_string(r#""foo"
  "":2
  "bar"
    "":4
    "zaz":3
  "qux":1"#);
        root.sort_by_func(|node| match node {
            // Normally, None is sorted before Some, but we want it the other way around.
            Node::Leaf { value, .. } => Reverse(Some(Reverse(*value))),
            Node::Interior { .. } => Reverse(None),
        });
        assert_eq!(root, Node::from_test_string(r#""foo"
  "qux":1
  "":2
  "bar"
    "zaz":3
    "":4"#));
    }

    #[test]
    fn test_directory_tree() {
        let mut root: Node<()> = Node::new_root();

        for entry in walkdir::WalkDir::new(".") {
            let entry = entry.unwrap();
            let path = entry.path();
            let str = path.to_string_lossy();
            if str.contains(".git") || str.contains("target") {
                continue;
            }
            root.insert::<true>(&str, ());
        }

        root.sort_by_key();
        println!("sorted trie:{}", root.to_test_string());

        println!("entries:");
        let mut trie_iter = root.external_iter_items_leafs();
        while let Some((str, _)) = trie_iter.next() {
            println!("  {}", str.join(""));
        }
    }

    // TODO: unicode tests: smileys, German umlauts, etc.
}
