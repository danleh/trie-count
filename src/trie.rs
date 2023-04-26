
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

use std::{str::FromStr, hint::unreachable_unchecked, ops::Generator, mem::MaybeUninit, marker::PhantomData};

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
    pub fn new_leaf(str: &str, value: T) -> Self {
        Node::Leaf {
            key_rest: str.into(),
            value,
        }
    }

    pub fn key_part(&self) -> &str {
        match self {
            Node::Leaf { key_rest, .. } => key_rest,
            Node::Interior { key_prefix, .. } => key_prefix,
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

    #[cfg(test)]
    fn to_test_string(&self) -> String
        where T: std::fmt::Display
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
                Node::Leaf { key_rest, value } =>
                    if key_rest.starts_with(key_query) {
                        return Some((key_matched_len, cur_node))
                    },
                Node::Interior { key_prefix, children } =>
                    match split_prefix_rest(key_query, &key_prefix[..], str::char_indices) {
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

    // Inserts a fresh interior node, of which the old `self` will become a child. That is, go from:
    //  self
    // to:
    //  Node::Interior { interior_key, children: [self, other_children...] }
    fn splice_interior<const N: usize>(&mut self, interior_key: Box<str>, other_children: [Node<T>; N]) {
        let new_interior = Node::Interior {
            key_prefix: interior_key,
            children: Vec::with_capacity(N+1),
        };
        let old_self = std::mem::replace(self, new_interior);
        match self {
            Node::Interior { children, .. } => {
                children.push(old_self);
                children.extend(other_children.into_iter());
            }
            _ => unreachable!("we just replaced self with a new interior node")
        }
    }

    fn insert(&mut self, insert_key: &str, insert_value: T) -> InsertResult<T> {
        fn insert<const IS_ROOT: bool, T>(cur_node: &mut Node<T>, insert_key: &str, insert_value: T) -> InsertResult<T> {
            match cur_node {
                Node::Leaf { key_rest: self_key, value } => {
                    match split_prefix_rest(self_key, insert_key, str::char_indices) {
                        // The insertion key is equal to the current node's key, so replace the value.
                        SplitResult { common_prefix: _, left_rest: "", right_rest: "" } => {
                            let old_value = std::mem::replace(value, insert_value);
                            InsertResult::Replaced { old_value }
                        }
                        // Only the root node is allowed to have an empty interior key,
                        // in all other cases we hand back to the parent, which shall try to insert somewhere else.
                        // In case of the root node, this will always be false and hence fall through to the next match arm
                        // (which will then split the root node, potentially introducing a root with an empty key).
                        SplitResult { common_prefix: "", left_rest: self_key_rest, right_rest: insert_key_rest } if !IS_ROOT => {
                            InsertResult::NoPrefix { value: insert_value }
                        }
                        // Split this node into an interior node with the common prefix as key,
                        // and two leaf nodes as children, one for self's old value and one for the inserted value.
                        SplitResult { common_prefix, left_rest: self_key_rest, right_rest: insert_key_rest } => {
                            let common_prefix = common_prefix.into();
                            let insert_key_rest = insert_key_rest.into();
                            *self_key = self_key_rest.into();
                            cur_node.splice_interior(common_prefix, [Node::Leaf { key_rest: insert_key_rest, value: insert_value }]);
                            InsertResult::Ok
                        }
                    }
                }
                Node::Interior { key_prefix, children } => {
                    todo!()
                    // call insert with IS_ROOT=false on the children, then check for NoPrefix
                }
            }
        }
        insert::<true, T>(self, insert_key, insert_value)
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

    SplitResult { common_prefix, left_rest, right_rest }
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
    fn test_get_all_with_prefix() {
        let root = test_trie();

        assert_eq!(root.get_all_with_prefix("fooqux"), Some(("foo", (&Node::Leaf {
            key_rest: "qux".into(),
            value: 2,
        }))));

        assert_eq!(root.get_all_with_prefix("foobarqux"), Some(("foobar", (&Node::Leaf {
            key_rest: "qux".into(),
            value: 1,
        }))));
        
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
    fn test_insert_into_empty_leaf() {
        let mut root = Node::from_test_string(r#""":1"#);
        assert_matches!(root.insert("foo", 2), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#"""
  "":1
  "foo":2"#));
    }

    #[test]
    fn test_insert_empty_key() {
        let mut root = Node::from_test_string(r#""foo":1"#);
        assert_matches!(root.insert("", 2), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#"""
  "foo":1
  "":2"#));
    }

    #[test]
    fn test_insert_duplicate() {
        let mut root = Node::from_test_string(r#""foo":1"#);
        assert_matches!(root.insert("foo", 2), InsertResult::Replaced { old_value: 1 });
        assert_eq!(root, Node::from_test_string(r#""foo":2"#));
    }

    #[test]
    fn test_insert_split_leaf() {
        let mut root = Node::from_test_string(r#""foo":1"#);
        assert_matches!(root.insert("foobar", 2), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#""foo"
  "":1
  "bar":2"#));

        let mut root = Node::from_test_string(r#""foobar":1"#);
        assert_matches!(root.insert("foo", 2), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#""foo"
  "bar":1
  "":2"#));

        // TODO: Or should this fail?
        let mut root = Node::from_test_string(r#""foo":1"#);
        assert_matches!(root.insert("bar", 2), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#"""
  "foo":1
  "bar":2"#));
    }

    #[test]
    fn test_insert_interior() {
        let mut root = Node::from_test_string(r#""foo"
  "bar":1
  "qux":2"#);
        assert_matches!(root.insert("foozaz", 3), InsertResult::Ok);
        assert_eq!(root, Node::from_test_string(r#""foo"
  "bar":1
  "qux":2
  "zaz":3"#));
    }

    // TODO test_insert_split_interior
    // TODO test_insert_into_empty_interior

    // TODO: unicode tests: smileys, German umlauts, etc.
    // TODO: counts, duplicate entries
}
