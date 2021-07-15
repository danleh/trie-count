use std::io::{self, BufRead};
use std::path::PathBuf;

use main_error::MainError;
use clap::Clap;

use crate::trie::Trie;

mod trie;
mod unicode_bar_chart;

const BAR_WIDTH: usize = 20;

#[derive(Clap, Debug)]
#[clap(
    author = clap::crate_authors!(),
    version = clap::crate_version!(),
    about = clap::crate_description!(),
)]
/// Organizes the input lines in a prefix tree (i.e., merging all equal prefixes into a single node)
/// and counts transitive elements in the tree. Useful
struct Options {
    /// Input file to read lines from. [default: stdin]
    #[clap(short, long, value_name = "file")]
    input: Option<PathBuf>,

    /// Split only at the given character, e.g., use '/' for splitting paths by directories and file.
    /// [default: split at every character]
    #[clap(short, long, value_name = "character")]
    tokenize_at: Option<char>,

    /// Sort the trie nodes by number of contained elements, i.e., largest subtrees come first.
    /// [default: true]
    #[clap(short, long)]
    sort_by_count: bool,

    /// Show a bar of percent next to the count. [default: false]
    #[clap(short, long)]
    bar: bool,
}

fn main() -> Result<(), MainError> {
    // test_order();

    let options = Options::parse();
    // println!("{:?}", options);

    let mut trie = if let Some(token) = options.tokenize_at {
        Trie::with_split_token(token)
    } else  {
        Trie::new()
    };

    let stdin  = io::stdin();
    for line in stdin.lock().lines() {
        trie.insert(&line?);
    }

    if options.sort_by_count {
        trie.sort_by_count();
    }

    let max_size_width = trie.len().to_string().len();
    let total_inv = 1.0 / trie.len() as f64;

    for (prefix, level, count) in trie.by_levels_with_count() {
        let indent = "  ".repeat(level);
        print!("{}{:<width$} ", indent, count, width=max_size_width);
        if options.bar {
            let total_fraction = count as f64 * total_inv;
            let bar = unicode_bar_chart::unicode_bar_str(total_fraction, BAR_WIDTH);
            print!("{} ", bar);
        }
        println!("{}", prefix);
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