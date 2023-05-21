use std::fmt::Write;
use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter};

use anyhow::Context;
use clap::Parser;

use crate::options::{Options, ProperFraction, Threshold};
use crate::trie::Trie;
use crate::unicode_bar::unicode_bar;

mod count_tree;
mod options;
mod trie;
mod unicode_bar;

const BAR_WIDTH: usize = 10;

fn main() -> anyhow::Result<()> {
    let options = options::Options::parse();
    // DEBUG
    eprintln!("{options:#?}");

    fn monomorphize_trie_splitter<'a, F, I>(key_splitter: F, options: &Options) -> anyhow::Result<()>
    where
        F: Fn(&'a str) -> I,
        I: Iterator<Item = &'a str>,
    {
        let mut trie = Trie::with_key_splitter(key_splitter);

        // Read lines from input and insert intro trie.
        let input: Box<dyn io::BufRead> = if let Some(file) = &options.input {
            Box::new(BufReader::new(File::open(file)?))
        } else {
            let stdin = Box::leak(Box::new(io::stdin()));
            Box::new(stdin.lock())
        };

        for (i, line) in input.lines().enumerate() {
            let line = line?;
            let mut line = line.as_str();

            // Optionally trim leading and trailing whitespace.
            if options.trim_input {
                line = line.trim();
            }

            // Optionally use counts from beginning of line.
            let CountedLine(count, line) = if options.counted_input {
                CountedLine::parse(line).with_context(|| {
                    format!("input line {}: expected integer count, got '{line}'", i + 1)
                })?
            } else {
                CountedLine(1, line)
            };

            trie.insert_or_update(line, count, |current| *current += count);
        }

        // Convert the trie to a tree, where each subtree contains the count of all its children.
        let mut count_tree = count_tree::Node::from(&trie);

        // Filter out nodes that are below the threshold.
        let total_count = count_tree.count;
        match options.min {
            Some(Threshold::Count(threshold)) => count_tree.retain(|node| node.count >= threshold),
            Some(Threshold::Fraction(threshold)) => count_tree.retain(|node| ProperFraction::new(node.count, total_count).unwrap() >= threshold),
            None => {}
        };

        // Optionally sort by subtree sizes.
        match options.sort {
            Some(options::SortOrder::Count) => count_tree.sort_by_key(|node| std::cmp::Reverse(node.count)),
            Some(options::SortOrder::Alphabetical) => count_tree.sort_by_key(|node| node.str),
            None => {}
        };

        // Write trie to output.
        let mut output: Box<dyn io::Write> = if let Some(file) = &options.output {
            Box::new(BufWriter::new(File::create(file)?))
        } else {
            Box::new(io::stdout())
        };

        fn print_tree(
            output: &mut impl io::Write,
            node: &count_tree::Node,
            level: usize,
            options: &Options,
            total_count: u64,
            max_width: usize,
        ) -> anyhow::Result<()> {
            let fraction = ProperFraction::new(node.count, total_count).unwrap();

            let mut line = options.indent_with.repeat(level);
            write!(line, "{} ", node.count)?;
            if options.percent {
                write!(line, "({:.1}%) ", fraction.0 * 100.0)?;
            }
            if options.quote {
                write!(line, "'{}'", node.str)?;
            } else {
                write!(line, "{}", node.str)?;
            }
            // Put the bar right of the other information and align it.
            if options.bar {
                writeln!(output, "{line:max_width$} {}", unicode_bar(fraction, BAR_WIDTH))?;
            } else {
                writeln!(output, "{line}")?;
            }

            for child in node.children.iter() {
                print_tree(output, child, level + 1, options, total_count, max_width)?;
            }
            Ok(())
        }

        // Calculate maximum width of a line for indentation of the bar chart.
        let mut max_width = 0;
        max_width += count_tree.height() * options.indent_with.len(); // Indentation.
        max_width += total_count.to_string().len() + 1; // Count and space.
        max_width += if options.percent { 8 } else { 0 }; // Percentage, parenthesis etc. and space.
        let max_str_len = count_tree.fold(0, |max_str_len, node| max_str_len.max(node.str.len()));
        max_width += max_str_len;
        max_width += if options.quote { 2 } else { 0 };

        print_tree(&mut output, &count_tree, 0, &options, total_count, max_width)
    }
    
    // Create empty trie.
    // Use provided delimiter pattern to split lines into parts.
    if let Some(regex) = &options.split_delimiter {
        let regex = regex.clone();
        monomorphize_trie_splitter(|str: &str| {
            // str.matches(regex)
            str.split_inclusive(" ")
        }, &options)
    } else {
        monomorphize_trie_splitter(chars, &options)
    }

}

#[derive(Debug, Clone)]
pub struct CountedLine<'a>(pub u64, pub &'a str);

impl<'a> CountedLine<'a> {
    pub fn parse(line: &'a str) -> anyhow::Result<Self> {
        let (count, line) = line
            .split_once(char::is_whitespace)
            .ok_or(anyhow::Error::msg(
                "could not split count from rest of line",
            ))?;
        let count: u64 = count.parse()?;
        Ok(CountedLine(count, line))
    }
}

// FIXME Remove
pub fn chars(s: &str) -> impl Iterator<Item = &str> {
    let mut chars = s
        .char_indices()
        .map(|(i, _c)| i)
        .chain(std::iter::once(s.len()));
    let mut begin = chars.next().unwrap();
    std::iter::from_fn(move || {
        if let Some(index) = chars.next() {
            let chars = unsafe { s.get_unchecked(begin..index) };
            begin = index;
            Some(chars)
        } else {
            None
        }
    })
}

#[test]
fn test_chars() {
    let mut chars = chars("foo");
    assert_eq!(chars.next(), Some("f"));
    assert_eq!(chars.next(), Some("o"));
    assert_eq!(chars.next(), Some("o"));
    assert_eq!(chars.next(), None);
}
