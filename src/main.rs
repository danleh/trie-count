use std::io::Read;

use std::io::{self, BufRead};

use main_error::MainError;

use crate::trie::Trie;

mod trie;
mod unicode_bar_chart;

const BAR_WIDTH: usize = 10;

fn main() -> Result<(), MainError> {
    // test_order();

    let mut trie = Trie::new();

    let stdin  = io::stdin();
    for line in stdin.lock().lines() {
        trie.insert(&line?);
    }

    trie.sort_by_count();

    // TODO align sizes
    // let max_size_width = trie.len().to_string().len();

    let total = trie.len();

    for (prefix, level, count) in trie.by_levels_with_count() {
        let indent = "  ".repeat(level);
        let bar = unicode_bar_chart::bar_str(count as f64 / total as f64, BAR_WIDTH);
        println!("{:<15} {} {}", format!("{}{}", indent, count), bar, prefix);
    }

    Ok(())
}

// TODO test double inserts
// TODO test empty "" inserts

fn test_basics() {
    let mut trie = Trie::new();
    print_trie(&trie);

    trie.insert("foo");
    print_trie(&trie);

    trie.insert("bar");
    print_trie(&trie);

    trie.insert("baz");
    print_trie(&trie);

    trie.insert("fin");
    print_trie(&trie);

    trie.insert("foobar");
    print_trie(&trie);
}

fn test_interior_leaf() {
    let mut trie = Trie::new();
    print_trie(&trie);

    trie.insert("foo");
    print_trie(&trie);

    trie.insert("foobar");
    print_trie(&trie);

    // FIXME don't know anymore that "foo" was it's own insertion
    // TODO make Node an enum { Leaf, Interior }?
}

fn test_order() {
    let mut trie = Trie::new();

    trie.insert("/home/daniel/wapm/bla.wasm");
    trie.insert("/home/daniel/github/blub.wasm");
    trie.insert("/home/daniel/github/foo.wasm");
    trie.insert("/home/daniel/github/baz.wasm");
    trie.insert("/home/daniel/github/wohoo.wasm");
    trie.insert("/home/daniel/wapm/yipee.wasm");

    print_trie(&trie);

    return;

    println!("size: {}", trie.len());

    trie.sort_by_count();
    print_trie(&trie);
}

fn print_trie(trie: &Trie) {
    println!("{:?}", trie);
    for (prefix, level) in trie.by_levels() {
        println!("{}{:?}", "  ".repeat(level), prefix);
    }
}