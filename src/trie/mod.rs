// see https://github.com/michaelsproul/rust_radix_trie/blob/master/examples/string_frequency.rs
// and https://github.com/miedzinski/prefix-tree
// and https://en.wikipedia.org/wiki/Radix_tree

mod iteration;

#[cfg(test)]
mod test;

use crate::longest_common_prefix::*;

// TODO: generalize over generic sequences of K (e.g., bytes) instead of just `&str`.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trie<T, F> {
    // TODO: Hide this better, provide iterator accessors
    pub(crate) root: TrieNode<T>,

    /// Function for determining where to split the key string, e.g., only at specific characters
    /// such as '/', only at unicode grapheme cluster boundaries, or at any character.
    key_split_function: F,
}

impl<T, F> Trie<T, F>
where
    F: for <'any> SplitFunction<'any>,
{
    pub fn with_key_splitter(key_split_function: F) -> Self {   
        Self {
            root: TrieNode::empty_root(),
            key_split_function,
        }
    }

    pub fn len(&self) -> usize {
        self.root.len()
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_empty()
    }

    pub fn insert_or_update(&mut self, key: &str, value: T, update: impl Fn(&mut T)) {
        self.root.insert_or_update::<true, ()>(key, value, &update, self.key_split_function);
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TrieNode<T> {
    key_part: Box<str>,
    data: NodeData<T>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum NodeData<T> {
    Leaf(T),
    Interior(Vec<TrieNode<T>>),
}

impl<T> TrieNode<T> {

    // Constructors:

    fn leaf(str: &str, value: T) -> Self {
        TrieNode {
            key_part: str.into(),
            data: NodeData::Leaf(value),
        }
    }

    fn interior(str: &str, children: Vec<TrieNode<T>>) -> Self {
        TrieNode {
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

    pub fn value_mut(&mut self) -> Option<&mut T> {
        match &mut self.data {
            NodeData::Leaf(value) => Some(value),
            NodeData::Interior(_) => None,
        }
    }

    pub fn key_part(&self) -> &str {
        &self.key_part
    }

    pub fn children(&self) -> std::slice::Iter<TrieNode<T>> {
        match &self.data {
            NodeData::Leaf(_) => [].iter(),
            NodeData::Interior(children) => children.iter(),
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
    pub fn get_first_with_prefix<'trie>(&'trie self, key_query: &'_ str, key_split_function: impl for <'any> SplitFunction<'any>) -> Option<(/* key */ String, &'trie T)> {
        if let Some((key_matched, subtrie)) = self.get_all_with_prefix(key_query, key_split_function) {
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
    pub fn get_all_with_prefix<'trie, 'query>(&'trie self, key_query: &'query str, key_split_function: impl for <'any> SplitFunction<'any>)
    -> Option<(/* key_matched */ &'query str, /* matching_subtrie */ &'trie TrieNode<T>)> {
        fn get_all_with_prefix<'trie, T>(cur_node: &'trie TrieNode<T>, key_query: &'_ str, key_matched_len: usize, key_split_function: impl for <'any> SplitFunction<'any>) 
        -> Option<(/* key_matched_len */ usize, /* matching_subtrie */ &'trie TrieNode<T>)> {
            match &cur_node.data {
                NodeData::Leaf(_) =>
                    if cur_node.key_part.starts_with(key_query) {
                        return Some((key_matched_len, cur_node))
                    },
                NodeData::Interior(children) =>
                    // FIXME generify SplitAtAllChars
                    match longest_common_prefix(key_query, &cur_node.key_part, key_split_function) {
                        // The queried key was fully a prefix of the current node, so return the whole subtrie.
                        LcpResult { common_prefix: _, left_rest: "", right_rest: _ } =>
                            return Some((key_matched_len, cur_node)),
                        // The current node "consumed" a prefix of the queried key, so search further in the children.
                        LcpResult { common_prefix, left_rest: key_query, right_rest: "" } =>
                            for child in children {
                                if let Some((key_matched_len, node)) = get_all_with_prefix(child, key_query, key_matched_len + common_prefix.len(), key_split_function) {
                                    return Some((key_matched_len, node));
                                }
                            },
                        // Both have a non-empty rest after splitting off the `common_prefix`, 
                        // so neither was a prefix of the other, hence stop the search.
                        LcpResult { .. } => return None
                    }
            }
            None
        }
        get_all_with_prefix(self, key_query, 0, key_split_function)
            .map(|(key_matched_len, subtrie)| (&key_query[..key_matched_len], subtrie))
    }

    pub fn insert<const IS_ROOT: bool>(
        &mut self,
        insert_key: &str,
        insert_value: T,
        key_split_function: impl for <'any> SplitFunction<'any>
    ) -> InsertResult<T>
    // TODO: Relax the `Clone` requirement, which requires an "Entry API" of some sort.
    where T: Clone
    {
        match self.insert_or_update::<IS_ROOT, T>(
            insert_key,
            insert_value.clone(),
            &|old_value| std::mem::replace(old_value, insert_value.clone()),
            key_split_function
        ) {
            InsertOrUpdateResult::Inserted => InsertResult::Inserted,
            InsertOrUpdateResult::Updated { result } => InsertResult::Replaced { old_value: result },
            InsertOrUpdateResult::NoPrefix { value } => InsertResult::NoPrefix { value },
        }
    }

    // TODO: Replace with `entry` API, using `Entry` and `InsertAction`.
    pub fn insert_or_update<const IS_ROOT: bool, U>(
        &mut self,
        insert_key: &str,
        insert_value: T,
        update: &impl Fn(&mut T) -> U,
        key_split_function: impl for <'any> SplitFunction<'any>
    ) -> InsertOrUpdateResult<T, U> {
        let split_result = longest_common_prefix(insert_key, &self.key_part, key_split_function);
        match (&mut self.data, split_result) {
            // This is a leaf and its key is exactly equal to the insertion key.
            // -> Replace the value.
            (NodeData::Leaf(value), LcpResult { common_prefix: _, left_rest: "", right_rest: "" }) => {
                let result = update(value);
                InsertOrUpdateResult::Updated { result }
            }

            // This is the "initial" empty root (an interior node with an empty key and no children).
            // -> Replace with a single new leaf.
            (NodeData::Interior(children), LcpResult { common_prefix, left_rest: insert_key, right_rest }) if IS_ROOT && children.is_empty() => {
                debug_assert!(common_prefix.is_empty());
                debug_assert!(right_rest.is_empty());

                *self = TrieNode::leaf(insert_key, insert_value);
                InsertOrUpdateResult::Inserted
            }

            // This is an interior node and its key is a prefix of the `insert_key`.
            // -> This is the right subtrie to (recursively) try to insert.
            (NodeData::Interior(children), LcpResult { common_prefix: _stripped, left_rest: insert_key_rest, right_rest: "" }) => {
                // Try to insert into the children.
                let mut insert_value = insert_value;
                for child in children.iter_mut() {
                    match child.insert_or_update::<false, U>(insert_key_rest, insert_value, update, key_split_function) {
                        // Not successful, so try the next child.
                        InsertOrUpdateResult::NoPrefix { value } => insert_value = value,
                        // Successful (either replaced or inserted a new leaf node), so return.
                        insert_result => return insert_result
                    }
                }

                // No child could be found where the insert could take place,
                // so we must create a new leaf node.
                let insert_new_leaf = TrieNode::leaf(insert_key_rest, insert_value);
                children.push(insert_new_leaf);
                InsertOrUpdateResult::Inserted
            }

            // The insertion key and the current node's key don't have a common prefix,
            // so insertion in this subtrie is not possible, with one exception:
            // The root node is allowed to have an empty key (in case there is no common prefix
            // among all strings in the trie). In this case, we fall through to the next match arm
            // which will split the root into a new root with an empty key.
            (_, LcpResult { common_prefix: "", left_rest: _insert_key, right_rest: _self_key }) if !IS_ROOT => {
                InsertOrUpdateResult::NoPrefix { value: insert_value }
            }

            // General case: The insertion key and the current node's key have a non-empty common prefix.
            // -> Split this node into an interior node with the common prefix as key,
            // and two leaf nodes as children, one for the old self's subtrie and one for the newly inserted value.
            (_, LcpResult { common_prefix, left_rest: insert_key_rest, right_rest: self_key_rest }) => {
                let new_leaf = TrieNode::leaf(insert_key_rest, insert_value);
                let new_interior = TrieNode::interior(common_prefix, Vec::with_capacity(2));
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

    /// Sorts the trie by the result of the given function applied to each node.
    pub fn sort_by_func<F, O>(&mut self, mut f: F)
    where
        F: FnMut(&TrieNode<T>) -> O,
        O: Ord,
    {
        fn sort_by_func<T, F, O>(cur_node: &mut TrieNode<T>, f: &mut F)
        where
            F: FnMut(&TrieNode<T>) -> O,
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

// TODO: Entry API for insert_or_update.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Entry<'trie, T> {
    Present(&'trie mut T),
    Vacant {
        node: &'trie mut TrieNode<T>,
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
