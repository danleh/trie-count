use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter};
use std::path::PathBuf;

use clap::Parser;
use main_error::MainError;

use crate::trie::Trie;

mod trie;
mod unicode_bar_chart;

const BAR_WIDTH: usize = 20;
const TARGET_MAX_LINE_WIDTH: usize = 100;

#[derive(Parser, Debug)]
#[clap(
    author = clap::crate_authors!(),
    version = clap::crate_version!(),
    about = clap::crate_description!(),
)]
struct Options {
    /// Input file to read lines from. [default: stdin]
    // #[clap(value_name = "file")]
    input: Option<PathBuf>,

    /// Output file to write trie to. [default: stdout]
    #[clap(short, long, value_name = "file")]
    output: Option<PathBuf>,

    /// Split only at the given character.
    /// For example, pass -t'/' to build a trie of paths, splitting across directories and files.
    /// [default: split at every character]
    #[clap(short, long, value_name = "character")]
    tokenize_at: Option<char>,

    /// Sort the trie nodes by number of contained elements, i.e., largest subtrees come first.
    /// [default: false]
    #[clap(short, long)]
    sort_by_count: bool,

    /// Character(s) with which to indent levels of the tree. [default: '  ']
    #[clap(
        short,
        long,
        default_value = "  ",
        value_name = "characters",
        hide_default_value = true
    )]
    indent_with: String,

    /// Show a bar of percent next to the count. [default: false]
    #[clap(short, long)]
    bar: bool,
}

fn main() -> Result<(), MainError> {
    let options = Options::parse();
    // DEBUG
    // println!("{:?}", options);

    // Create empty trie.
    let mut trie = if let Some(token) = options.tokenize_at {
        Trie::with_split_token(token)
    } else {
        Trie::new()
    };

    // Read lines from input and insert intro trie.
    let input: Box<dyn io::BufRead> = if let Some(file) = options.input {
        Box::new(BufReader::new(File::open(file)?))
    } else {
        let stdin = Box::leak(Box::new(io::stdin()));
        Box::new(stdin.lock())
    };
    for line in input.lines() {
        trie.insert(&line?);
    }

    // Optionally sort trie by subtree sizes.
    if options.sort_by_count {
        trie.sort_by_count();
    }

    // Write trie to output.
    let mut output: Box<dyn io::Write> = if let Some(file) = options.output {
        Box::new(BufWriter::new(File::create(file)?))
    } else {
        Box::new(io::stdout())
    };

    let max_size_width = trie.len().to_string().len();
    let total_inv = 1.0 / trie.len() as f64;

    for (prefix, level, count) in trie.by_levels_with_count() {
        let indent = options.indent_with.repeat(level);
        let line = format!("{indent}{count:<max_size_width$} {prefix}");
        if options.bar {
            let total_fraction = count as f64 * total_inv;
            let bar = unicode_bar_chart::unicode_bar_str(total_fraction, BAR_WIDTH);
            // Put bar right of the other information and align such that total width is not exceeded.
            writeln!(output, "{:width$}{}", line, bar, width = TARGET_MAX_LINE_WIDTH - BAR_WIDTH)?;
        } else {
            writeln!(output, "{line}")?;
        }
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
