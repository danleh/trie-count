# `tc`: Trie Count Utility

A command line utility that takes a list of strings as input and produces a [trie (prefix tree)](https://en.wikipedia.org/wiki/Trie) as output.
The trie associates with each prefix in the input lines a count (how often it occurred).

I find it useful for quick data exploration.

## Usage

```
$ tc --help
Usage: tc [OPTIONS] [INPUT]

Arguments:
  [INPUT]  Input file to read the lines from. [default: stdin]

Options:
  -o, --out <file>               Output file to write the trie to. [default: stdout]
  -t, --trim-input               Trim leading and trailing whitespace from each line. [default: false]
  -d, --split-delimiter <regex>  Split only at the given regex pattern. For example, -d'/|\.' is useful to build a trie of paths, splitting only at directories and file extensions. [default: split at every character]
  -c, --counted-input            Each input line starts with a count of how often to count the following string. Example: "42 foo" counts the string "foo" 42 times. [default: false]
  -s, --sort <c[ount]|a[lpha]>   Sort the trie either by the count of contained elements, i.e., largest subtrees come first, or alphabetically. [default: false, i.e., insertion order]
  -i, --indent-with <string>     Character(s) with which to indent levels of the tree. [default: "  "]
  -q, --quote                    Quote the strings in the output. [default: false]
  -m, --min <count|fraction>     Do not show subtries below an integer <count> or that account for less than <fraction> of the total count. [default: 
false]
  -p, --percent                  Show a percentage next to the count. [default: false]
  -b, --bar                      Show a textual barchart next to the count. [default: false]
  -h, --help                     Print help
  -V, --version                  Print version
```

## Examples

Quickly determine that there are 4 strings in the input file that start with `a`, 3 strings that start with `ab`, etc.:

```
$ cat tests/inputs/simple.txt
abc
abd
abe
a

$ tc --quote tests/inputs/simple.txt
4 'a'
  3 'b'
    1 'c'
    1 'd'
    1 'e'
  1 ''
```

A trie can be useful for exploring how many files are in which part of a directory tree:

```
$ find -type f
./Cargo.toml
./Cargo.lock
./src/main.rs
./src/options.rs

$ find -type f | tc --split-delimiter='/' --sort=count
4 ./
  2 src/
    1 main.rs
    1 options.rs
  1 Cargo.toml
  1 Cargo.lock
```

In combination with other UNIX tools one can, e.g., determine which parts of a directory tree contains the most words:

```
$ find -type f | xargs wc -w | head -n-1
42 src/options.rs
1337 src/main.rs

$ find -type f | xargs wc -w | head -n-1 | tc --counted-input -d'/' -sc
1379 src/
  1337 main.rs
  42 options.rs
```

## Installation

(Currently requires a nightly Rust toolchain, because of the unstable `pattern` feature of the `regex` crate. Feel free to contribute a stable replacement.)

```
rustup toolchain install nightly

git clone https://github.com/danleh/trie-count.git
cd trie-count
cargo +nightly install --path .

# Should now be installed per user:
tc --help
```

## License: MIT