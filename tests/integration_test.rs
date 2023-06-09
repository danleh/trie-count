#[test]
fn readme_examples() {
    testcase("simple", ["--quote"]);
    testcase("paths", ["--split-delimiter=/", "--sort=count"]);
    testcase("word-counts", ["--counted-input", "-d/", "-sc"]);
}

#[test]
fn counted_input() {
    testcase("counted-input", ["-c", "--sort=alpha", "--quote"]);
}

fn testcase<const N: usize>(name: &str, options: [&str; N]) {
    let output = std::process::Command::new("cargo")
        .arg("run")
        .arg("--")
        .args(options)
        .arg(format!("tests/inputs/{name}.txt"))
        .output()
        .unwrap();
    let stdout = String::from_utf8(&output.stdout).unwrap();
    let stderr = String::from_utf8(&output.stderr).unwrap();
    assert!(
        output.status.success(),
        "\nstdout:\n{stdout}stderr:\n{stderr}"
    );

    let expected = std::fs::read_to_string(format!("tests/expected_outputs/{name}.txt")).unwrap();

    // Ignore line ending differences, i.e., LF vs CRLF.
    let mut output_lines = stdout.lines();
    let mut expected_lines = expected.lines();
    loop {
        let output_line = output_lines.next();
        let expected_line = expected_lines.next();
        match (output_line, expected_line) {
            (None, None) => break,
            (output_line, expected_line) => assert_eq!(
                output_line, expected_line,
                "\noutput:\n{stdout}\nexpected:\n{expected}"
            ),
        }
    }
}
