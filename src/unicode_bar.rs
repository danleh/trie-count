//! Display a fraction as a horizontal bar chart with "high" resolution by using Unicode block
//! characters.

use crate::options::ProperFraction;

// Use only two different levels of "fullness" since the other unicode characters may look slightly
// different depending on the font.
const PARTIAL_BLOCKS: [&str; 3] = [" ", "▌","█"];
// const PARTIAL_BLOCKS: [&str; 9] = [" " , "▏", "▎", "▍", "▌", "▋", "▊", "▉", "█"];

pub fn unicode_bar(fraction: ProperFraction, max_width: usize) -> String {
    let ideal_width = fraction.0 * max_width as f64;

    let full_width = ideal_width.floor();
    let mut bar = PARTIAL_BLOCKS.last().unwrap().repeat(full_width as usize);

    let partial_width = ideal_width - full_width;
    if partial_width > 0.0 {
        let block_index = (partial_width * (PARTIAL_BLOCKS.len() - 1) as f64).floor() as usize;
        bar.push_str(PARTIAL_BLOCKS[block_index]);
    }

    let empty_width = max_width - bar.chars().count();
    for _ in 0..empty_width {
        bar.push_str(PARTIAL_BLOCKS.first().unwrap())
    }
    
    debug_assert_eq!(bar.chars().count(), max_width);
    bar
}

#[test]
fn test_bar() {
    for i in 0..=100 {
        let fraction = ProperFraction::new(i, 100).unwrap();
        println!("{:3}: {}", i, unicode_bar(fraction, 10));
    }
}