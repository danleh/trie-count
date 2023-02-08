//! Display a fraction as a horizontal bar chart with "high" resolution by using Unicode block
//! characters.

const PARTIAL_BLOCKS: [char; 9] = [' ' , '▏', '▎', '▍', '▌', '▋', '▊', '▉', '█'];

pub fn unicode_bar_str(fraction: f64, max_width: usize) -> String {
    assert!((0.0..=1.0).contains(&fraction));

    let ideal_width = fraction * max_width as f64;

    let full_width = ideal_width.floor();
    let mut bar = "█".repeat(full_width as usize);

    let partial_width = ideal_width - full_width;
    if partial_width > 0.0 {
        let block_index = (partial_width * PARTIAL_BLOCKS.len() as f64).floor() as usize;
        bar.push(PARTIAL_BLOCKS[block_index]);
    }

    let empty_width = max_width - bar.chars().count();
    for _ in 0..empty_width {
        bar.push(' ')
    }
    
    assert_eq!(bar.chars().count(), max_width);
    bar
}
