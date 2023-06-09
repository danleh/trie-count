# `tc`: Trie Count Utility

A small command line utility that takes a list of strings as input and produces a [trie (prefix tree)](https://en.wikipedia.org/wiki/Trie) as output.
The trie associates a count with each prefix in the input lines (i.e., shows how common a particular prefix is).
I find it useful for quick data exploration.

## Usage Examples

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

For more options (e.g., filtering out subtries with a count below a threshold) see `tc --help`.

## Installation / Building from Source

(Currently requires a nightly Rust toolchain because of the unstable `pattern` feature of the `regex` crate.
Feel free to contribute a stable replacement.)

```
rustup toolchain install nightly
```
```
git clone https://github.com/danleh/trie-count.git
cd trie-count
cargo +nightly install --path .
```
```
# Should now be installed per user:
tc --help
```

## License

MIT. See [LICENSE](LICENSE).
