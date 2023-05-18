
// see https://github.com/michaelsproul/rust_radix_trie/blob/master/examples/string_frequency.rs
// and https://github.com/miedzinski/prefix-tree
// and https://en.wikipedia.org/wiki/Radix_tree

use std::{str::FromStr, marker::PhantomData, iter::Sum, borrow::Borrow};

use unicode_segmentation::{UnicodeSegmentation, GraphemeIndices};

// TODO: generalize over generic sequences of K (e.g., bytes) instead of just `&str`.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trie<T, /*F*/> {
    // FIXME: Hide this better, provide iterator accessors
    pub(crate) root: Node<T>,

    // /// Determines at which points the key string may be split, e.g., only at '/', only at 
    // /// unicode grapheme cluster boundaries, or at any character boundary.
    // key_split_points: F,
}

impl<T, 
// F, I, P
> Trie<T, /*F*/>
// where
//     F: Fn(&str) -> I,
//     I: Iterator<Item = (usize, P)>,
//     P: PartialEq
{
    // pub fn new(key_split_points: F) -> Self {
    //     Self {
    //         root: Node::empty_root(),
    //         key_split_points,
    //     }
    // }

    pub fn new() -> Self {
        Self {
            root: Node::empty_root(),
        }
    }

    pub fn len(&self) -> usize {
        self.root.len()
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_empty()
    }

    pub fn clear(&mut self) {
        self.root = Node::empty_root();
    }

    pub fn insert(&mut self, key: &str, value: T) -> Option<T>
    // FIXME: Relax the `Clone` requirement.
    where T: Clone
    {
        match self.root.insert::<true>(key, value) {
            InsertResult::Inserted => None,
            InsertResult::Replaced { old_value } => Some(old_value),
            InsertResult::NoPrefix { .. } => unreachable!("not possible when inserting into the root node"),
        }
    }

    pub fn insert_or_update(&mut self, key: &str, value: T, update: impl Fn(&mut T)) {
        self.root.insert_or_update::<true, ()>(key, value, &update);
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
    // parent: Option<&Node<T>>,

    // Cache of the subtree values.
    // subtree_size: usize,

    // TODO: Alternative design: allow interior nodes to have values.
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeData<T> {
    Leaf(T),
    Interior(Vec<Node<T>>),
}

/// Trait for abstracting over the tracking of keys in the iteratior:
/// Either the keys are tracked (and the current `KeyParts` stored in the `KeyStack`),
/// or not tracked at all (in which case `KeyParts` is `()`).
pub trait KeyStack<'trie> : Borrow<Self::KeyParts> {
    type KeyParts: ?Sized;
    fn current_key_parts(&self) -> &Self::KeyParts {
        self.borrow()
    }

    fn push(&mut self, key_part: &'trie str);
    fn pop(&mut self);
}

/// Implementation for not tracking/returning the key at all.
impl KeyStack<'_> for () {
    type KeyParts = ();
    fn push(&mut self, _: &str) {}
    fn pop(&mut self) {}
}

/// Implementation for returning the key as parts in a `&[&str]` slice (which doesn't require
/// allocating, but borrows from the iterator, specifically the key stack).
impl<'trie> KeyStack<'trie> for Vec<&'trie str> {
    type KeyParts = [&'trie str];
    fn push(&mut self, key_part: &'trie str) {
        self.push(key_part);
    }
    fn pop(&mut self) {
        self.pop();
    }
}

/// Trait for abstracting over `Value`s returned by the iterator:
/// Either both leafs and interior nodes are returned, or only leafs.
pub trait Value<'trie, T> : Sized {
    fn from(node: &'trie Node<T>) -> Option<Self>;
}

/// Implementation for iterating only over leaf nodes (which always have a value).
impl<'trie, T> Value<'trie, T> for &'trie T {
    fn from(node: &'trie Node<T>) -> Option<Self> {
        node.value()
    }
}

/// Implementation for iterating over all nodes, including interior nodes (which are `None`).
impl<'trie, T: 'trie> Value<'trie, T> for Option<&'trie T> {
    fn from(node: &'trie Node<T>) -> Option<Self> {
        Some(node.value())
    }
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
impl<'trie, T, KS, V> Iter<'trie, T, KS, V>
where
    KS: KeyStack<'trie> + Default,
    V: Value<'trie, T>,
{
    pub fn new(root: &'trie Node<T>) -> Self {
        Self {
            node_stack: vec![Some(root)],
            key_parts_stack: KS::default(),
            value_representation: PhantomData,
        }
    }

    #[allow(clippy::needless_lifetimes)]
    pub fn next<'next>(&'next mut self) -> Option<(&'next KS::KeyParts, V)> {
        while let Some(cur_node) = self.node_stack.pop() {
            match cur_node {
                Some(node) => {
                    self.key_parts_stack.push(&node.key_part);
                    // Pop from the key parts stack again after having processed this subtrie.
                    self.node_stack.push(None);
                    // Process the children next, i.e., depth-first traversal.
                    self.node_stack.extend(node.children().rev().map(Some));
                    if let Some(value) = V::from(node) {
                        return Some((self.key_parts_stack.current_key_parts(), value));
                    }
                }
                None => self.key_parts_stack.pop(),
            }
        }
        None
    }
}

impl<T> Node<T> {

    // Constructors:

    fn leaf(str: &str, value: T) -> Self {
        Node {
            key_part: str.into(),
            data: NodeData::Leaf(value),
        }
    }

    fn interior(str: &str, children: Vec<Node<T>>) -> Self {
        Node {
            key_part: str.into(),
            data: NodeData::Interior(children),
        }
    }

    fn empty_root() -> Self {
        Self::interior("", Vec::new())
    }


    // Accessors:

    pub fn value(&self) -> Option<&T> {
        match &self.data {
            NodeData::Leaf(value) => Some(value),
            NodeData::Interior(_) => None,
        }
    }

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
    /// O(n), where n is the number of nodes in the trie.
    pub fn len(&self) -> usize {
        match &self.data {
            NodeData::Leaf(_) => 1,
            NodeData::Interior(children) => children.iter().map(Self::len).sum(),
        }
    }

    /// Returns `true` if the trie contains no mappings (i.e., leafs).
    /// O(1).
    pub fn is_empty(&self) -> bool {
        // This is faster then checking `self.len() == 0`, because it does not need to traverse the
        // whole trie to calculate the length first.
        match &self.data {
            NodeData::Leaf(_) => false,
            NodeData::Interior(children) => children.is_empty(),
        }
    }


    // Iterators:

    /// Generic interior pre-order depth-first traversal of the trie, configurable by `K` and `V`.
    fn internal_iter_generic<'trie, KS, V, F>(&'trie self, key_parts_stack: &mut KS, f: &mut F)
    where
        KS: KeyStack<'trie>,
        V: Value<'trie, T>,
        F: FnMut(&KS::KeyParts, V)
    {
        key_parts_stack.push(&self.key_part);
        if let Some(value) = V::from(self) {
            f(key_parts_stack.current_key_parts(), value);
        }
        for child in self.children() {
            child.internal_iter_generic(key_parts_stack, f);
        }
        key_parts_stack.pop();
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


    // Finding, inserting, and removing key value mappings:

    /// Returns `Some(T)` if there is a value associated with the exact given key, 
    /// or `None` if no such value exists.
    pub fn get_exact<'trie>(&'trie self, key_query: &'_ str) -> Option<&'trie T> {
        match &self.data {
            NodeData::Leaf(value) =>
                if &self.key_part[..] == key_query {
                    return Some(value);
                }
            NodeData::Interior(children) => 
                if let Some(key_query) = key_query.strip_prefix(&self.key_part[..]) {
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
            if let Some((subtrie_key_parts, value)) = subtrie.external_iter_items_leafs().next() {
                // I would hope that the string allocation and concetenation is optimized away
                // if the caller does not use the key, but I am not sure.
                let mut key = key_matched.to_owned();
                for part in subtrie_key_parts {
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
            match &cur_node.data {
                NodeData::Leaf(_) =>
                    if cur_node.key_part.starts_with(key_query) {
                        return Some((key_matched_len, cur_node))
                    },
                NodeData::Interior(children) =>
                    match split_prefix_rest(key_query, &cur_node.key_part, str::char_indices) {
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

    pub fn insert<const IS_ROOT: bool>(&mut self, insert_key: &str, insert_value: T) -> InsertResult<T>
    // FIXME: Relax the `Clone` requirement.
    where T: Clone
    {
        match self.insert_or_update::<IS_ROOT, T>(insert_key, insert_value.clone(), &|old_value| std::mem::replace(old_value, insert_value.clone())) {
            InsertOrUpdateResult::Inserted => InsertResult::Inserted,
            InsertOrUpdateResult::Updated { result } => InsertResult::Replaced { old_value: result },
            InsertOrUpdateResult::NoPrefix { value } => InsertResult::NoPrefix { value },
        }
    }

    // TODO: Replace with `entry` API, using `Entry` and `InsertAction`.
    pub fn insert_or_update<const IS_ROOT: bool, U>(&mut self, insert_key: &str, insert_value: T, update: &impl Fn(&mut T) -> U) -> InsertOrUpdateResult<T, U> {
        let split_result = split_prefix_rest(insert_key, &self.key_part, str::char_indices);
        match (&mut self.data, split_result) {
            // This is a leaf and its key is exactly equal to the insertion key.
            // -> Replace the value.
            (NodeData::Leaf(value), SplitResult { common_prefix: _, left_rest: "", right_rest: "" }) => {
                let result = update(value);
                InsertOrUpdateResult::Updated { result }
            }

            // This is the "initial" empty root (an interior node with an empty key and no children).
            // -> Replace with a single new leaf.
            (NodeData::Interior(children), SplitResult { common_prefix, left_rest: insert_key, right_rest }) if IS_ROOT && children.is_empty() => {
                debug_assert!(common_prefix.is_empty());
                debug_assert!(right_rest.is_empty());

                *self = Node::leaf(insert_key, insert_value);
                InsertOrUpdateResult::Inserted
            }

            // This is an interior node and its key is a prefix of the `insert_key`.
            // -> This is the right subtrie to (recursively) try to insert.
            (NodeData::Interior(children), SplitResult { common_prefix: _stripped, left_rest: insert_key_rest, right_rest: "" }) => {
                // Try to insert into the children.
                let mut insert_value = insert_value;
                for child in children.iter_mut() {
                    match child.insert_or_update::<false, U>(insert_key_rest, insert_value, update) {
                        // Not successful, so try the next child.
                        InsertOrUpdateResult::NoPrefix { value } => insert_value = value,
                        // Successful (either replaced or inserted a new leaf node), so return.
                        insert_result => return insert_result
                    }
                }

                // No child could be found where the insert could take place,
                // so we must create a new leaf node.
                let insert_new_leaf = Node::leaf(insert_key_rest, insert_value);
                children.push(insert_new_leaf);
                InsertOrUpdateResult::Inserted
            }

            // The insertion key and the current node's key don't have a common prefix,
            // so insertion in this subtrie is not possible, with one exception:
            // The root node is allowed to have an empty key (in case there is no common prefix
            // among all strings in the trie). In this case, we fall through to the next match arm
            // which will split the root into a new root with an empty key.
            (_, SplitResult { common_prefix: "", left_rest: _insert_key, right_rest: _self_key }) if !IS_ROOT => {
                InsertOrUpdateResult::NoPrefix { value: insert_value }
            }

            // General case: The insertion key and the current node's key have a non-empty common prefix.
            // -> Split this node into an interior node with the common prefix as key,
            // and two leaf nodes as children, one for the old self's subtrie and one for the newly inserted value.
            (_, SplitResult { common_prefix, left_rest: insert_key_rest, right_rest: self_key_rest }) => {
                let new_leaf = Node::leaf(insert_key_rest, insert_value);
                let new_interior = Node::interior(common_prefix, Vec::with_capacity(2));
                self.key_part = self_key_rest.into();
                let old_self = std::mem::replace(self, new_interior);
                match &mut self.data /* == new_interior.data */ {
                    NodeData::Interior(children) => {
                        children.push(old_self);
                        children.push(new_leaf);
                    }
                    _ => unreachable!("we just replaced self with a new interior node")
                }
                InsertOrUpdateResult::Inserted
            }
        }
    }

    pub fn remove_exact(&mut self, key: &str) -> Option<T> {
        // TODO: Based on `get_exact`. Maybe refactor into a common function that returns a `&mut Node<T>`?
        todo!()
    }

    /// Sorts the children alphabetically by their key.
    pub fn sort_by_key(&mut self) {
        if let NodeData::Interior(children) = &mut self.data {
            for child in children.iter_mut() {
                child.sort_by_key();
            }
            children.sort_by(|a, b| a.key_part.cmp(&b.key_part));
        }
    }

//     fn sort_by_count(&mut self) {
//         self.children.sort_by_cached_key(|node| std::cmp::Reverse(node.len()));
//         for child in &mut self.children {
//             child.sort_by_count();
//         }
//     }

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
            if let NodeData::Interior(children) = &mut cur_node.data {
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
            match &cur_node.data {
                NodeData::Leaf(value) => f_leaf(value),
                NodeData::Interior(children) => {
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
        match &self.data {
            NodeData::Leaf(value) => *value,
            NodeData::Interior(children) => children.iter().map(Node::value_sum).sum()
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
                    subtries.push((level, Node::leaf(key_part, value)));
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
                    subtries.push((level, Node::interior(key_part, children))); 
                },
            }
        }

        assert_eq!(subtries.len(), 1, "more than one root node");
        subtries.pop().unwrap().1
    }

    #[cfg(test)]
    fn assert_invariants<const IS_ROOT: bool>(&self)
    where T: std::fmt::Debug
    {
        if let NodeData::Interior(children) = &self.data {
            if IS_ROOT {
                assert!(children.is_empty() || children.len() > 1, "invariant violated: the root node must have either no child (initial empty root), or at least two children\n{self:?}");
            } else {
                assert!(!self.key_part.is_empty(), "invariant violated: interior nodes (except the root node) must have a non-empty key part\n{self:?}");
                assert!(children.len() > 1, "invariant violated: interior nodes (except the empty root node) must have at least two children\n{self:?}");
            }
            for (i, child1) in children.iter().enumerate() {
                for child2 in &children[i+1..] {
                    let split_result = split_prefix_rest(&child1.key_part, &child2.key_part, str::char_indices);
                    assert!(split_result.common_prefix.is_empty(), "invariant violated: children of interior nodes must not have a common prefix\n{self:?}");
                }
            }
            for child in children {
                child.assert_invariants::<false>();
            }
        }
    }
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

/// ASCII Art of this trie:
/// "foo"
/// ├── "bar"
/// │   └── "" -> 0
/// │   └── "qux" -> 1
/// ├── "qux" -> 2
/// └── "" -> 3
#[cfg(test)]
fn test_trie() -> Node<u32> {
    Node::interior("foo", vec![
        Node::interior("bar", vec![
            Node::leaf("", 0),
            Node::leaf("qux", 1),
        ]),
        Node::leaf("qux", 2),
        Node::leaf("", 3),
    ])
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
    Inserted,
    Replaced { old_value: T },
    NoPrefix { value: T }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InsertOrUpdateResult<T, U> {
    Inserted,
    Updated { result: U },
    NoPrefix { value: T },
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Entry<'trie, T> {
    Present(&'trie mut T),
    Vacant {
        node: &'trie mut Node<T>,
        insert_key_rest: &'trie str,
        insert_action: InsertAction,
    },
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum InsertAction {
    ReplaceEmptyRoot,
    AddChild,
    SplitNode,
}

// #[cfg(test)]
const TEST_INDENT: &str = "  ";
// #[cfg(test)]
const TEST_DELIM: &str = ":";

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
        let root: Node<u32> = Node::empty_root();
        assert_eq!(root.len(), 0);
        assert!(root.is_empty());

        let root = Node::leaf("foobar", 42);
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

        assert_eq!(root.get_all_with_prefix("fooqux"), Some(("foo", (&Node::leaf("qux", 2)))));
        assert_eq!(root.get_all_with_prefix("foobarqux"), Some(("foobar", (&Node::leaf("qux", 1)))));
        
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
        let root: Node<i32> = Node::empty_root();
        assert_eq!(root, Node::interior("", Vec::new()));
    }

    #[test]
    fn test_insert_into_empty_leaf() {
        let mut root = Node::from_test_string(r#""":1"#);
        assert_matches!(root.insert::<true>("foo", 2), InsertResult::Inserted);
        assert_eq!(root, Node::from_test_string(r#"""
  "":1
  "foo":2"#));
    }

    #[test]
    fn test_insert_empty_key() {
        let mut root = Node::from_test_string(r#""foo":1"#);
        assert_matches!(root.insert::<true>("", 2), InsertResult::Inserted);
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
        assert_matches!(root.insert::<true>("foobar", 2), InsertResult::Inserted);
        assert_eq!(root, Node::from_test_string(r#""foo"
  "":1
  "bar":2"#));

        let mut root = Node::from_test_string(r#""foobar":1"#);
        assert_matches!(root.insert::<true>("foo", 2), InsertResult::Inserted);
        assert_eq!(root, Node::from_test_string(r#""foo"
  "bar":1
  "":2"#));

        let mut root = Node::from_test_string(r#""foo":1"#);
        assert_matches!(root.insert::<true>("bar", 2), InsertResult::Inserted);
        assert_eq!(root, Node::from_test_string(r#"""
  "foo":1
  "bar":2"#));
    }

    #[test]
    fn test_insert_into_empty_root() {
        let mut root: Node<i32> = Node::empty_root();
        assert_matches!(root.insert::<true>("foo", 1), InsertResult::Inserted);
        // The empty interior node shall be replaced by a leaf node.
        assert_eq!(root, Node::from_test_string(r#""foo":1"#));

        let mut root: Node<i32> = Node::empty_root();
        assert_matches!(root.insert::<true>("", 1), InsertResult::Inserted);
        assert_eq!(root, Node::from_test_string(r#""":1"#));
    }

    #[test]
    fn test_insert_interior() {
        let mut root = Node::from_test_string(r#""foo"
  "bar":1
  "qux":2"#);
        assert_matches!(root.insert::<true>("foozaz", 3), InsertResult::Inserted);
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
        assert_matches!(root.insert::<true>("foobaz", 3), InsertResult::Inserted);
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
        let mut root = Node::empty_root();
        let mut hashmap_reference = HashMap::new();

        for (str, value) in random_values(20, 5, 'A'..='C') {
            println!("{}", root.to_test_string());

            print!("insert {str:?}:{value}");
            let result = root.insert::<true>(&str, value);
            println!(" ... {result:?}");

            let result_reference = hashmap_reference.insert(str, value);
            match (&result, result_reference) {
                (InsertResult::Inserted, None) => {},
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
        let mut root = Node::empty_root();
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
        root.sort_by_func(|node| match &node.data {
            // Normally, None is sorted before Some, but we want it the other way around.
            NodeData::Leaf(value) => Reverse(Some(Reverse(*value))),
            NodeData::Interior(_) => Reverse(None),
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
        let mut root: Node<()> = Node::empty_root();

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
