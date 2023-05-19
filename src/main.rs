#![feature(assert_matches)]
#![feature(new_uninit)]
#![feature(generators, generator_trait)]

// #![allow(dead_code, unused_imports, unused_variables, unused_mut)]

// use mimalloc::MiMalloc;

// #[global_allocator]
// static GLOBAL: MiMalloc = MiMalloc;

use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter};

use clap::Parser;

use crate::trie::Trie;

mod options;
mod unicode_bar_chart;

mod count_tree;

pub mod trie;

const BAR_WIDTH: usize = 20;
const TARGET_MAX_LINE_WIDTH: usize = 100;

fn main() -> anyhow::Result<()> {
    let options = options::Options::parse();
    // DEBUG
    println!("{options:#?}");

    // Create empty trie.
    // FIXME
    // let mut trie = if let Some(token) = options.split_delimiter.first() {
    //     Trie::with_split_token(*token)
    // } else {
    //     Trie::new()
    // };

    // Read lines from input and insert intro trie.
    let input: Box<dyn io::BufRead> = if let Some(file) = options.input {
        Box::new(BufReader::new(File::open(file)?))
    } else {
        let stdin = Box::leak(Box::new(io::stdin()));
        Box::new(stdin.lock())
    };
    let mut trie = Trie::new();
    for line in input.lines() {
        let line = line?;
        let (count, line) = if options.counted_input {
            // split line once into count and rest of line.
            let (count, rest) = line.split_once(|c: char| c.is_whitespace()).expect("line must begin with count, followed by whitespace");
            let count: u64 = count.parse()?;
            (count, rest)
        } else {
            (1, line.as_str())
        };
        trie.insert_or_update(line, count, |current| *current += count);
    }

    // Convert the trie to a tree, where each subtree contains the count of all its children.
    let mut count_tree = count_tree::Node::from(&trie);

    // Optionally sort by subtree sizes.
    match options.sort {
        Some(options::SortOrder::Count) => count_tree.sort_by_count_desc(),
        Some(options::SortOrder::Alphabetical) => count_tree.sort_by_str(),
        None => {}
    };

    // Write trie to output.
    let mut output: Box<dyn io::Write> = if let Some(file) = options.output {
        Box::new(BufWriter::new(File::create(file)?))
    } else {
        Box::new(io::stdout())
    };

    // let max_size_width = trie.len().to_string().len();
    // let total_inv = 1.0 / trie.len() as f64;

    // for (prefix, level, count) in trie.by_levels_with_count() {
    //     let indent = options.indent_with.repeat(level);
    //     let line = format!("{indent}{count:<max_size_width$} {prefix}");
    //     if options.bar {
    //         let total_fraction = count as f64 * total_inv;
    //         let bar = unicode_bar_chart::unicode_bar_str(total_fraction, BAR_WIDTH);
    //         // Put bar right of the other information and align such that total width is not exceeded.
    //         writeln!(output, "{:width$}{}", line, bar, width = TARGET_MAX_LINE_WIDTH - BAR_WIDTH)?;
    //     } else {
    //         writeln!(output, "{line}")?;
    //     }
    // }

    // trie.root.internal_iter_items(|key_parts, value| {
    //     let (first, rest) = key_parts.split_first().expect("must be at least one key part");
    //     if !first.is_empty() {
    //         write!(output, "{}", options.indent_with).unwrap();
    //     }
    //     for _ in rest {
    //         write!(output, "{}", options.indent_with).unwrap();
    //     }
    //     write!(output, "'{}'", key_parts.last().expect("must be at least one key part")).unwrap();
    //     if let Some(value) = value {
    //         write!(output, ": {value}").unwrap();
    //     }
    //     writeln!(output).unwrap();
    // });

    fn print_tree(output: &mut impl io::Write, node: &count_tree::Node, level: usize, indent_with: &str) -> io::Result<()> {
        write!(output, "{}", indent_with.repeat(level))?;
        writeln!(output, "{} '{}'", node.count, node.str)?;
        for child in node.children.iter() {
            print_tree(output, child, level + 1, indent_with)?;
        }
        Ok(())
    }
    print_tree(&mut output, &count_tree, 0, &options.indent_with)?;

//     let root = trie::Node::from_test_string(r#""foo"
//   "bar"
//     "":0
//     "qux":1
//   "qux":2
//   "":3"#);
//     let sum = test_internal_iter_values(&root);
//     println!("{sum}");

//     let sum2 = test_external_iter_values(&root);
//     println!("{sum2}");

    Ok(())
}

#[inline(never)]
fn test_internal_iter_values(root: &trie::Node<i32>) -> i32 {
    let mut sum = 0;
    root.internal_iter_values(|_value| sum += 17);
    sum
}

#[inline(never)]
fn test_external_iter_values(root: &trie::Node<i32>) -> i32 {
    let mut sum = 0;
    let mut iter = root.external_iter_values();
    while let Some((_key, _value)) = iter.next() {
        sum += 17;
    }
    sum
}
