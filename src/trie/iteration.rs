use std::borrow::Borrow;
use std::marker::PhantomData;

use super::Node;

/// Trait for abstracting over the tracking of keys in the iteratior:
/// Either the keys are tracked (and the current `KeyParts` stored in the `KeyStack`),
/// or not tracked at all (in which case `KeyParts` is `()`).
pub trait KeyStack<'trie>: Borrow<Self::KeyParts> {
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
pub trait Value<'trie, T>: Sized {
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
    /// Generic interior pre-order depth-first traversal of the trie, configurable by `K` and `V`.
    fn internal_iter_generic<'trie, KS, V, F>(&'trie self, key_parts_stack: &mut KS, f: &mut F)
    where
        KS: KeyStack<'trie>,
        V: Value<'trie, T>,
        F: FnMut(&KS::KeyParts, V),
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
    pub fn internal_iter_items(
        &self,
        mut f: impl FnMut(/* key_parts */ &[&str], /* value */ Option<&T>),
    ) {
        self.internal_iter_generic(&mut Vec::new(), &mut f);
    }

    /// Depth-first traversal of the trie, _not_ including interior nodes, and with key parts.
    /// Since `f` is only called for leafs, the passed value is always a valid `&T`.
    pub fn internal_iter_items_leafs(
        &self,
        mut f: impl FnMut(/* key_parts */ &[&str], /* value */ &T),
    ) {
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
}
