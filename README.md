# Trie Count Utility

This is a simple command line utility that takes a list of strings as input and produces a trie data structure as output.
The trie gives a count for each prefix of the input strings.

Example:

    $ cat input.txt
    abc
    abd
    abe
    f
    
    $ tc input.txt
    3 ab
      1 c
      1 d
      1 e
    1 f

Example for paths:

    $ find -type f
    ./Cargo.toml
    ./Cargo.lock
    ./src/main.rs
    ./src/options.rs

    $ find -type f | tc -d'/' -s
    4 ./
      2 src/
        1 main.rs
        1 options.rs
      1 Cargo.toml
      1 Cargo.lock

Advanced example, combining with other UNIX tools, e.g., summing words in a directory tree:

    $ find -type f | xargs wc -w | head -n-1
      42 src/main.rs
    1337 src/options.rs

    $ find -type f | xargs wc -w | head -n-1 | tc -c -d'/' -s
    1379 src/
      1337 options.rs
      42   main.rs
