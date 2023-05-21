use std::path::PathBuf;
use std::str::FromStr;

use clap::Parser;
use clap::ValueHint;
use regex::Regex;

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
    #[clap(short, long = "out", value_name = "file", value_hint = ValueHint::FilePath)]
    pub output: Option<PathBuf>,

    /// Trim leading and trailing whitespace from each line.
    /// [default: false]
    #[clap(short, long)]
    pub trim_input: bool,

    /// Split only at the given regex pattern.
    /// For example, -d'/|\.' is useful to build a trie of paths, splitting only at directories and file extensions.
    /// [default: split at every character]
    #[clap(short = 'd', long, value_name = "regex")]
    pub split_delimiter: Option<Regex>,

    // TODO: Option to remove the split delimiter from the output.

    /// Each input line starts with a count of how often to count the following string.
    /// Example: "42 foo" counts the string "foo" 42 times.
    /// [default: false]
    #[clap(short, long)]
    pub counted_input: bool,

    /// Sort the trie either by the count of contained elements, i.e., largest subtrees come first,
    /// or alphabetically.
    /// [default: false, i.e., insertion order]
    #[clap(short, long, value_name = "c[ount]|a[lpha]")]
    pub sort: Option<SortOrder>,

    /// Character(s) with which to indent levels of the tree. [default: "  "]
    #[clap(short, long, default_value = "  ", value_name = "string", hide_default_value = true)]
    pub indent_with: String,

    /// Quote the strings in the output. [default: false]
    #[clap(short, long)]
    pub quote: bool,

    /// Do not show subtries below an integer <count> or that account for less than <fraction> of the total count. [default: disabled]
    #[clap(short, long, value_name = "count|fraction")]
    pub min: Option<Threshold>,

    /// Show a percentage next to the count. [default: false]
    #[clap(short, long)]
    pub percent: bool,

    /// Show a textual barchart next to the count. [default: false]
    #[clap(short, long)]
    pub bar: bool,
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
            "a" | "alpha" => Ok(SortOrder::Alphabetical),
            _ => Err("sort order must be either 'count' or 'alpha'"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Threshold {
    Count(u64),
    Fraction(ProperFraction),
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
pub struct ProperFraction(pub f64);

impl ProperFraction {
    pub fn new(nominator: u64, denominator: u64) -> Option<Self> {
        if nominator > denominator {
            None
        } else if denominator == 0 {
            Some(ProperFraction(1.0))
        } else {
            Some(ProperFraction(nominator as f64 / denominator as f64))
        }
    }

    pub fn from(f: f64) -> Option<Self> {
        if !(0.0..1.0).contains(&f) {
            None
        } else {
            Some(ProperFraction(f))
        }
    }
}

impl FromStr for ProperFraction {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let fraction: f64 = s
            .parse()
            .map_err(|_| "fraction must be a decimal value, e.g., 0.1 or .5")?;
        ProperFraction::from(fraction).ok_or("fraction must be in range [0, 1]")
    }
}
