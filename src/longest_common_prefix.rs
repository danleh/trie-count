use regex::Regex;

#[derive(Debug, PartialEq, Eq)]
pub struct LcpResult<'a> {
    pub common_prefix: &'a str,
    pub left_rest: &'a str,
    pub right_rest: &'a str,
}

// `Copy` such that the split function is cheap to pass around by value and copy (e.g. just a
// function pointer or a closure with a by-reference captured environment).
pub trait SplitFunction<'a> : Copy {
    type Iter: Iterator<Item = &'a str>;

    fn split(&self, str: &'a str) -> Self::Iter;
}

// Implementation for any closure that takes a `&str` slice and returns an iterator over subslices.
impl<'a, F, I> SplitFunction<'a> for F
where
    F: Copy,
    F: Fn(&'a str) -> I,
    I: Iterator<Item = &'a str>,
{
    type Iter = I;

    fn split(&self, str: &'a str) -> Self::Iter {
        self(str)
    }
}

// Trivial implementation for splitting at all characters.
#[derive(Clone, Copy)]
pub struct SplitAtAllChars;

impl<'a> SplitFunction<'a> for SplitAtAllChars {
    type Iter = std::str::SplitInclusive<'a, fn(char) -> bool>;

    fn split(&self, str: &'a str) -> Self::Iter {
        str.split_inclusive(|_| true)
    }
}

// Even faster implementation (about 1.5x!), but just for ASCII strings.
#[derive(Clone, Copy)]
pub struct SplitAtAllCharsAssumeAscii;

impl<'a> SplitFunction<'a> for SplitAtAllCharsAssumeAscii {
    type Iter = SplitAtAllCharsAssumeAsciiIter<'a>;

    fn split(&self, str: &'a str) -> Self::Iter {
        if str.is_ascii() {
            return SplitAtAllCharsAssumeAsciiIter(str.as_bytes().iter());
        } else {
            panic!("SplitAtAllCharsAssumeAscii only works on ASCII strings")
        }
    }
}

pub struct SplitAtAllCharsAssumeAsciiIter<'a>(std::slice::Iter<'a, u8>);

impl<'a> Iterator for SplitAtAllCharsAssumeAsciiIter<'a> {
    type Item = &'a str;
    
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: We know that the input is ASCII, so each byte is a valid UTF-8 codepoint.
        self.0.next().map(|byte| unsafe { std::str::from_utf8_unchecked(std::slice::from_ref(byte)) })
    }
}

// Implementation for splitting at a regex.
#[derive(Clone, Copy)]
pub struct RegexSplitter<'r>(pub &'r Regex);

impl<'a, 'r> SplitFunction<'a> for RegexSplitter<'r> {
    type Iter = std::str::SplitInclusive<'a, &'r Regex>;
    fn split(&self, str: &'a str) -> Self::Iter {
        str.split_inclusive(self.0)
    }
}

pub fn longest_common_prefix<'a>(left: &'a str, right: &'a str, splitter: impl SplitFunction<'a>) -> LcpResult<'a> {
    let left_iter = splitter.split(left);
    let right_iter = splitter.split(right);

    let mut difference_start_index = 0;

    let mut left_last = left.as_ptr();
    let mut right_last = right.as_ptr();
    for (left_part, right_part) in left_iter.zip(right_iter) {
        // Ensure that the split function decomposes the input without losing any parts.
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
        // SAFETY: We know that the `difference_start_index` is at a valid UTF-8 codepoint boundary,
        // because it comes from valid UTF-8 string subslices.
        common_prefix: unsafe { left.get_unchecked(..difference_start_index) },
        left_rest: unsafe { left.get_unchecked(difference_start_index..) },
        right_rest: unsafe { right.get_unchecked(difference_start_index..) },
    }
}

#[test]
fn test_split_at_all_chars() {
    let str = "foo";

    let mut iter = SplitAtAllChars.split(str);
    assert_eq!(iter.next(), Some("f"));
    assert_eq!(iter.next(), Some("o"));
    assert_eq!(iter.next(), Some("o"));
    assert_eq!(iter.next(), None);

    let mut iter = SplitAtAllCharsAssumeAscii.split(str);
    assert_eq!(iter.next(), Some("f"));
    assert_eq!(iter.next(), Some("o"));
    assert_eq!(iter.next(), Some("o"));
    assert_eq!(iter.next(), None);
}

#[test]
fn test_ascii() {
    let result = longest_common_prefix("", "", SplitAtAllChars);
    assert_eq!(result, LcpResult {
        common_prefix: "",
        left_rest: "",
        right_rest: "",
    }, "empty strings");

    let result = longest_common_prefix("foo", "foo", SplitAtAllChars);
    assert_eq!(result, LcpResult {
        common_prefix: "foo",
        left_rest: "",
        right_rest: "",
    }, "equal strings");

    let result = longest_common_prefix("foo", "foobar", SplitAtAllChars);
    assert_eq!(result, LcpResult {
        common_prefix: "foo",
        left_rest: "",
        right_rest: "bar",
    }, "left is prefix of right");

    let result = longest_common_prefix("foobar", "foo", SplitAtAllChars);
    assert_eq!(result, LcpResult {
        common_prefix: "foo",
        left_rest: "bar",
        right_rest: "",
    }, "right is prefix of left");

    let result = longest_common_prefix("foo", "bar", SplitAtAllChars);
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

    // TODO: smileys, German umlauts, etc.
}

#[test]
fn test_custom_splitters() {
    use crate::RegexSplitter;
    let regex = regex::Regex::new(r"\s+").unwrap();

    let result = longest_common_prefix("foo bar", "foo baz", RegexSplitter(&regex));
    assert_eq!(result, LcpResult {
        common_prefix: "foo ",
        left_rest: "bar",
        right_rest: "baz",
    }, "split on space");

    let result = longest_common_prefix("please don't split inside words", "please do not split inside words", RegexSplitter(&regex));
    assert_eq!(result, LcpResult {
        common_prefix: "please ",
        left_rest: "don't split inside words",
        right_rest: "do not split inside words",
    }, "split on space");
}
