# Trie Count Utility

This is a simple command line utility that takes a list of strings as input and produces a trie data structure as output.
The trie gives a count for each prefix of the input strings.

Example:

    $ cat tests/inputs/simple.txt
    abc
    abd
    abe
    f
    
    $ tc tests/inputs/simple.txt
    4
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

    $ find -type f | tc --split-delimiter='/' --sort=count
    4 ./
      2 src/
        1 main.rs
        1 options.rs
      1 Cargo.toml
      1 Cargo.lock

Advanced example, combining with other UNIX tools, e.g., summing words in a directory tree:

    $ find -type f | xargs wc -w | head -n-1
    42 src/options.rs
    1337 src/main.rs

    $ find -type f | xargs wc -w | head -n-1 | tc --counted-input -d'/' -sc
    1379 src/
      1337 main.rs
      42 options.rs
