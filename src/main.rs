use crate::trie::Trie;

mod trie;

fn main() {
    let mut trie = Trie::new();

    println!("{:?}", trie);
    print_trie(&trie);

    trie.insert("foo");
    println!("{:?}", trie);
    print_trie(&trie);

    trie.insert("foobar");
    println!("{:?}", trie);
    print_trie(&trie);

    // FIXME don't know anymore that "foo" was it's own insertion
    // TODO make Node an enum { Leaf, Interior }?

    // trie.insert("foo");

    // println!("{:?}", trie);
    // print_trie(&trie);

    // trie.insert("bar");

    // println!("{:?}", trie);
    // print_trie(&trie);

    // trie.insert("baz");

    // println!("{:?}", trie);
    // print_trie(&trie);

    // trie.insert("fin");

    // println!("{:?}", trie);
    // print_trie(&trie);

    // trie.insert("foobar");

    // println!("{:?}", trie);
    // print_trie(&trie);
}

// TODO test double inserts
// TODO test empty "" inserts

fn print_trie(trie: &Trie) {
    for (prefix, level) in trie.by_levels() {
        println!("{}{:?}", "  ".repeat(level), prefix);
    }
}