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
    