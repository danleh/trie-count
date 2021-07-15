const BLOCKS: [char; 9] = [' ' , '▏', '▎', '▍', '▌', '▋', '▊', '▉', '█'];

pub fn bar_str(fraction: f64, max_width: usize) -> String {
    assert!(fraction >= 0.0 && fraction <= 1.0);
    let total_width = fraction * max_width as f64;
    let full_width = total_width.floor();
    let partial_width = total_width - full_width;
    let block_index = (partial_width * BLOCKS.len() as f64).floor() as usize;
    let mut bar = "█".repeat(full_width as usize);
    bar.push(BLOCKS[block_index]);
    if let Some(rest) = max_width.checked_sub(bar.chars().count()) {
        bar.push_str(&" ".repeat(rest));
    }
    // FIXME some bug in total length
    assert_eq!(bar.chars().count(), max_width);
    bar
}