
#[derive(Debug, PartialEq, Eq)]
pub struct LcpResult<'a> {
    pub common_prefix: &'a str,
    pub left_rest: &'a str,
    pub right_rest: &'a str,
}

pub fn longest_common_prefix<'a, F, I>(left: &'a str, right: &'a str, split_inclusive: F) -> LcpResult<'a>
where
    F: Fn(&'a str) -> I,
    I: Iterator<Item = &'a str>,
{
    let left_iter = split_inclusive(left);
    let right_iter = split_inclusive(right);

    let (mut left_last, mut right_last) = (left.as_ptr(), right.as_ptr());
    let mut difference_start_index = 0;
    for (left_part, right_part) in left_iter.zip(right_iter) {
        debug_assert_eq!(left_last, left_part.as_ptr());
        debug_assert_eq!(right_last, right_part.as_ptr());
        left_last = unsafe { left_last.add(left_part.len()) };
        right_last = unsafe { right_last.add(right_part.len()) };

        if left_part != right_part {
            break;
        }
        difference_start_index += left_part.len();
    }
    
    LcpResult { 
        common_prefix: unsafe { left.get_unchecked(..difference_start_index) },
        left_rest: unsafe { left.get_unchecked(difference_start_index..) },
        right_rest: unsafe { right.get_unchecked(difference_start_index..) },
    }
}

// pub fn chars(s: &str) -> impl Iterator<Item = usize> + '_ {
//     s.char_indices().map(|(i, _c)| i)
// }

// pub fn graphemes(s: &str) -> impl Iterator<Item = usize> +'_ {
//     use unicode_segmentation::UnicodeSegmentation;
//     s.grapheme_indices(true).map(|(i, _c)| i)
// }

// #[inline(never)]
// pub fn check_asm<'a>(a: &'a str, b: &'a str) -> LcpResult<'a> {
//     longest_common_prefix(a, b, chars)
// }

// pub fn chars(s: char) -> bool { true }
// pub fn graphemes()

pub fn chars(s: &str) -> impl Iterator<Item = &str> {
    s.split_inclusive(|_| true)
}

pub fn graphemes(s: &str) -> impl Iterator<Item = &str> {
    use unicode_segmentation::UnicodeSegmentation;
    s.graphemes(true)
}

#[test]
fn test() {
    let result = longest_common_prefix("", "", chars);
    assert_eq!(result, LcpResult {
        common_prefix: "",
        left_rest: "",
        right_rest: "",
    }, "empty strings");

    let result = longest_common_prefix("foo", "foo", chars);
    assert_eq!(result, LcpResult {
        common_prefix: "foo",
        left_rest: "",
        right_rest: "",
    }, "equal strings");

    let result = longest_common_prefix("foo", "foobar", chars);
    assert_eq!(result, LcpResult {
        common_prefix: "foo",
        left_rest: "",
        right_rest: "bar",
    }, "left is prefix of right");

    let result = longest_common_prefix("foobar", "foo", chars);
    assert_eq!(result, LcpResult {
        common_prefix: "foo",
        left_rest: "bar",
        right_rest: "",
    }, "right is prefix of left");

    let result = longest_common_prefix("foo", "bar", chars);
    assert_eq!(result, LcpResult {
        common_prefix: "",
        left_rest: "foo",
        right_rest: "bar",
    }, "no common prefix");

    let result = longest_common_prefix("foo", "föö", graphemes);
    assert_eq!(result, LcpResult {
        common_prefix: "f",
        left_rest: "oo",
        right_rest: "öö",
    }, "unicode umlauts");

    let result = longest_common_prefix("🇩🇪", "🇩🇪🇪🇺", graphemes);
    assert_eq!(result, LcpResult {
        common_prefix: "🇩🇪",
        left_rest: "",
        right_rest: "🇪🇺",
    }, "unicode country flags");

    // TODO: unicode tests: smileys, German umlauts, etc.

    let result = longest_common_prefix("foo bar", "foo baz", |s| s.split_inclusive(' '));
    assert_eq!(result, LcpResult {
        common_prefix: "foo ",
        left_rest: "bar",
        right_rest: "baz",
    }, "split on space");

    let result = longest_common_prefix("please don't split inside words", "please do not split inside words", |s| s.split_inclusive(' '));
    assert_eq!(result, LcpResult {
        common_prefix: "please ",
        left_rest: "don't split inside words",
        right_rest: "do not split inside words",
    }, "split on space");

}
