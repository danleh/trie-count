use regex::Regex;

use crate::RegexSplitter;

#[derive(Debug, PartialEq, Eq)]
pub struct LcpResult<'a> {
    pub common_prefix: &'a str,
    pub left_rest: &'a str,
    pub right_rest: &'a str,
}

pub trait SplitInclusive<'a> {
    type Iter: Iterator<Item = &'a str>;
    fn call(&self, str: &'a str) -> Self::Iter;
}

impl<'a, F, I> SplitInclusive<'a> for F
where
    F: Fn(&'a str) -> I,
    I: Iterator<Item = &'a str>,
{
    type Iter = I;
    fn call(&self, str: &'a str) -> Self::Iter {
        self(str)
    }
}

// TODO use split_points again, i.e., F returning an iterator of usize instead of &str.
pub fn longest_common_prefix<'a, F>(left: &'a str, right: &'a str, split_inclusive: &F) -> LcpResult<'a>
where
    F: SplitInclusive<'a>
{
    let left_iter: F::Iter = split_inclusive.call(left);
    let right_iter: F::Iter = split_inclusive.call(right);

    let mut difference_start_index = 0;

    let mut left_last = left.as_ptr();
    let mut right_last = right.as_ptr();
    for (left_part, right_part) in left_iter.zip(right_iter) {
        // Check that the split iterator decomposes the input without losing any parts.
        debug_assert_eq!(left_last, left_part.as_ptr());
        debug_assert_eq!(right_last, right_part.as_ptr());
        left_last = left_part.as_bytes().as_ptr_range().end;
        right_last = right_part.as_bytes().as_ptr_range().end;

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

pub fn split_at_all_chars<'str>(s: &'str str) -> impl Iterator<Item = &'str str> + '_ {
    s.split_inclusive(|_| true)
}

#[test]
fn test_ascii() {
    let result = longest_common_prefix("", "", &split_at_all_chars);
    assert_eq!(result, LcpResult {
        common_prefix: "",
        left_rest: "",
        right_rest: "",
    }, "empty strings");

    let result = longest_common_prefix("foo", "foo", &split_at_all_chars);
    assert_eq!(result, LcpResult {
        common_prefix: "foo",
        left_rest: "",
        right_rest: "",
    }, "equal strings");

    let result = longest_common_prefix("foo", "foobar", &split_at_all_chars);
    assert_eq!(result, LcpResult {
        common_prefix: "foo",
        left_rest: "",
        right_rest: "bar",
    }, "left is prefix of right");

    let result = longest_common_prefix("foobar", "foo", &split_at_all_chars);
    assert_eq!(result, LcpResult {
        common_prefix: "foo",
        left_rest: "bar",
        right_rest: "",
    }, "right is prefix of left");

    let result = longest_common_prefix("foo", "bar", &split_at_all_chars);
    assert_eq!(result, LcpResult {
        common_prefix: "",
        left_rest: "foo",
        right_rest: "bar",
    }, "no common prefix");
}

#[test]
fn test_unicode() {
    fn graphemes(s: &str) -> impl Iterator<Item = &str> {
        use unicode_segmentation::UnicodeSegmentation;
        s.graphemes(true)
    }

    let result = longest_common_prefix("foo", "föö", &graphemes);
    assert_eq!(result, LcpResult {
        common_prefix: "f",
        left_rest: "oo",
        right_rest: "öö",
    }, "unicode umlauts");

    let result = longest_common_prefix("🇩🇪", "🇩🇪🇪🇺", &graphemes);
    assert_eq!(result, LcpResult {
        common_prefix: "🇩🇪",
        left_rest: "",
        right_rest: "🇪🇺",
    }, "unicode country flags");

    // TODO: smileys, German umlauts, etc.
}

#[test]
fn test_custom_splitters() {
    let regex = Regex::new(r"\s+").unwrap();
    let result = longest_common_prefix("foo bar", "foo baz", &RegexSplitter(&regex));
    assert_eq!(result, LcpResult {
        common_prefix: "foo ",
        left_rest: "bar",
        right_rest: "baz",
    }, "split on space");

    let result = longest_common_prefix("please don't split inside words", "please do not split inside words", &RegexSplitter(&regex));
    assert_eq!(result, LcpResult {
        common_prefix: "please ",
        left_rest: "don't split inside words",
        right_rest: "do not split inside words",
    }, "split on space");
}
