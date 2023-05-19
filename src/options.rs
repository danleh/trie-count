use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::str::FromStr;

use clap::Parser;
use clap::ValueHint;

#[derive(Parser, Debug)]
#[clap(
    author = clap::crate_authors!(),
    version = clap::crate_version!(),
    about = clap::crate_description!(),
)]
pub struct Options {
    /// Input file to read the lines from. [default: stdin]
    #[clap(value_hint = ValueHint::FilePath)]
    pub input: Option<PathBuf>,

    /// Output file to write the trie to. [default: stdout]
    #[clap(short, long = "out")]
    pub output: Option<PathBuf>,

    /// Sort the trie either by the count of contained elements, i.e., largest subtrees come first,
    /// or alphabetically.
    /// [default: false, i.e., insertion order]
    #[clap(short, long, value_name = "c[ount]|a[lpha]")]
    pub sort: Option<SortOrder>,

    /// Each input line starts with a count of how often to count the following string.
    /// Example: "42 foo" counts the string "foo" 42 times.
    /// [default: false]
    #[clap(short, long)]
    pub counted_input: bool,

    /// Split only at the given character(s). Can be given multiple times.
    /// For example, -d'/' -d'.' is useful to build a trie of paths, splitting only at directories and file extensions.
    /// [default: split at every character]
    /// TODO: Make this a string, not a single character.
    #[clap(short = 'd', long, value_name = "CHAR")]
    pub split_delimiter: Vec<char>,

    /// Character(s) with which to indent levels of the tree. [default: '  ']
    #[clap(
        short,
        long,
        default_value = "  ",
        value_name = "STRING",
        hide_default_value = true
    )]
    pub indent_with: String,

    /// Show a percentage next to the count. [default: false]
    #[clap(short, long)]
    pub percent: bool,

    /// Show a textual barchart next to the count. [default: false]
    #[clap(short, long)]
    pub bar: bool,

    /// Do not show subtries below an integer COUNT or that account for less than FRACTION of the total count. [default: disabled]
    /// TODO: Or limit depth of trie.
    #[clap(short, long, value_name = "COUNT|FRACTION")]
    pub min: Option<Threshold>,
}

#[derive(Debug, Clone, Copy)]
pub enum SortOrder {
    Count,
    Alphabetical,
}

impl FromStr for SortOrder {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "c" | "count" => Ok(SortOrder::Count),
            "a" | "alpha" | "alphabetical" => Ok(SortOrder::Alphabetical),
            _ => Err("sort order must be either 'count' or 'alpha'"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Threshold {
    Count(NonZeroUsize),
    Fraction(Fraction),
}

impl FromStr for Threshold {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Ok(count) = s.parse() {
            Ok(Threshold::Count(count))
        } else {
            let fraction = s.parse()?;
            Ok(Threshold::Fraction(fraction))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Fraction(f32);

impl FromStr for Fraction {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let fraction = s
            .parse()
            .map_err(|_| "fraction must be a decimal value, e.g., 0.1 or .5")?;
        if !(0.0..1.0).contains(&fraction) {
            return Err("fraction must be in range [0, 1]");
        }
        Ok(Fraction(fraction))
    }
}
