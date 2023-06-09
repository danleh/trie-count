use std::{cmp::Reverse, collections::HashMap, ops::RangeInclusive};

use super::*;

impl<T> Node<T> {
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

    #[cfg(test)]
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
    fn assert_invariants<const IS_ROOT: bool>(&self, key_split_function: impl for <'any> SplitFunction<'any>)
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
                    let split_result = longest_common_prefix(&child1.key_part, &child2.key_part, key_split_function);
                    assert!(split_result.common_prefix.is_empty(), "invariant violated: children of interior nodes must not have a common prefix\n{self:?}");
                }
            }
            for child in children {
                child.assert_invariants::<false>(key_split_function);
            }
        }
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

const TEST_INDENT: &str = "  ";
const TEST_DELIM: &str = ":";


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
fn test_get_all_with_prefix() {
    let root = test_trie();

    assert_eq!(root.get_all_with_prefix("fooqux", SplitAtAllChars), Some(("foo", (&Node::leaf("qux", 2)))));
    assert_eq!(root.get_all_with_prefix("foobarqux", SplitAtAllChars), Some(("foobar", (&Node::leaf("qux", 1)))));
    
    assert_eq!(root.get_all_with_prefix("xyz", SplitAtAllChars), None);
    
    assert_eq!(root.get_all_with_prefix("foobarqXYZ", SplitAtAllChars), None);
    assert_eq!(root.get_all_with_prefix("fooo", SplitAtAllChars), None);
    assert_eq!(root.get_all_with_prefix("fo", SplitAtAllChars), Some(("", &root)));
    assert_eq!(root.get_all_with_prefix("", SplitAtAllChars), Some(("", &root)));
}

#[test]
fn test_get_first_with_prefix() {
    let root = test_trie();

    assert_eq!(root.get_first_with_prefix("", SplitAtAllChars), Some(("foobar".into(), &0)));
    assert_eq!(root.get_first_with_prefix("fo", SplitAtAllChars), Some(("foobar".into(), &0)));
    assert_eq!(root.get_first_with_prefix("foob", SplitAtAllChars), Some(("foobar".into(), &0)));
    assert_eq!(root.get_first_with_prefix("foobar", SplitAtAllChars), Some(("foobar".into(), &0)));
    assert_eq!(root.get_first_with_prefix("foobarxyz", SplitAtAllChars), None);
    assert_eq!(root.get_first_with_prefix("foobarqux", SplitAtAllChars), Some(("foobarqux".into(), &1)));
    assert_eq!(root.get_first_with_prefix("fooqux", SplitAtAllChars), Some(("fooqux".into(), &2)));
    assert_eq!(root.get_first_with_prefix("fooxyz", SplitAtAllChars), None);
}

#[test]
fn test_empty_trie() {
    let root: Node<i32> = Node::empty_root();
    assert_eq!(root, Node::interior("", Vec::new()));
}

#[test]
fn test_insert_into_empty_leaf() {
    let mut root = Node::from_test_string(r#""":1"#);
    assert_eq!(root.insert::<true>("foo", 2, SplitAtAllChars), InsertResult::Inserted);
    assert_eq!(root, Node::from_test_string(r#"""
  "":1
  "foo":2"#));
}

#[test]
fn test_insert_empty_key() {
    let mut root = Node::from_test_string(r#""foo":1"#);
    assert_eq!(root.insert::<true>("", 2, SplitAtAllChars), InsertResult::Inserted);
    assert_eq!(root, Node::from_test_string(r#"""
  "foo":1
  "":2"#));
}

#[test]
fn test_insert_duplicate_leaf() {
    let mut root = Node::from_test_string(r#""foo":1"#);
    assert_eq!(root.insert::<true>("foo", 2, SplitAtAllChars), InsertResult::Replaced { old_value: 1 });
    assert_eq!(root, Node::from_test_string(r#""foo":2"#));
}

#[test]
fn test_insert_split_leaf() {
    let mut root = Node::from_test_string(r#""foo":1"#);
    assert_eq!(root.insert::<true>("foobar", 2, SplitAtAllChars), InsertResult::Inserted);
    assert_eq!(root, Node::from_test_string(r#""foo"
  "":1
  "bar":2"#));

    let mut root = Node::from_test_string(r#""foobar":1"#);
    assert_eq!(root.insert::<true>("foo", 2, SplitAtAllChars), InsertResult::Inserted);
    assert_eq!(root, Node::from_test_string(r#""foo"
  "bar":1
  "":2"#));

    let mut root = Node::from_test_string(r#""foo":1"#);
    assert_eq!(root.insert::<true>("bar", 2, SplitAtAllChars), InsertResult::Inserted);
    assert_eq!(root, Node::from_test_string(r#"""
  "foo":1
  "bar":2"#));
}

#[test]
fn test_insert_into_empty_root() {
    let mut root: Node<i32> = Node::empty_root();
    assert_eq!(root.insert::<true>("foo", 1, SplitAtAllChars), InsertResult::Inserted);
    // The empty interior node shall be replaced by a leaf node.
    assert_eq!(root, Node::from_test_string(r#""foo":1"#));

    let mut root: Node<i32> = Node::empty_root();
    assert_eq!(root.insert::<true>("", 1, SplitAtAllChars), InsertResult::Inserted);
    assert_eq!(root, Node::from_test_string(r#""":1"#));
}

#[test]
fn test_insert_interior() {
    let mut root = Node::from_test_string(r#""foo"
  "bar":1
  "qux":2"#);
    assert_eq!(root.insert::<true>("foozaz", 3, SplitAtAllChars), InsertResult::Inserted);
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
    assert_eq!(root.insert::<true>("foobaz", 3, SplitAtAllChars), InsertResult::Inserted);
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
        let result = root.insert::<true>(&str, value, SplitAtAllChars);
        println!(" ... {result:?}");

        let result_reference = hashmap_reference.insert(str, value);
        match (&result, result_reference) {
            (InsertResult::Inserted, None) => {},
            (InsertResult::Replaced { old_value }, Some(old_value_reference)) if *old_value == old_value_reference => {},
            _ => panic!("mismatch between reference HashMap and trie result\nHashMap: {result_reference:?}\ntrie:{result:?}"),
        }

        root.assert_invariants::<true>(SplitAtAllChars);
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
        root.insert::<true>(&str, value, SplitAtAllChars);
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
        root.insert::<true>(&str, (), SplitAtAllChars);
    }

    root.sort_by_key();
    println!("sorted trie:{}", root.to_test_string());

    println!("entries:");
    let mut trie_iter = root.external_iter_items_leafs();
    while let Some((str, _)) = trie_iter.next() {
        println!("  {}", str.join(""));
    }
}
