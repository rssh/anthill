use crate::common::{anthill, Output};

fn query(pattern: &str, import_list: bool) -> Output {
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../anthill-core/tests/fixtures/wi7fp1m/words.anthill");
    let mut args = vec![
        "query",
        "-p",
        fixture.to_str().unwrap(),
        "-i",
        "wi7fp1m.*",
        "-i",
        "anthill.prelude.List.*",
        "--max-results",
        "8",
    ];
    if import_list {
        args.extend(["-i", "anthill.prelude.List"]);
    }
    args.push(pattern);
    anthill(&args)
}

#[test]
fn wi7fp1m_direct_query_matches_wrapper_enumeration() {
    // Controls: correct imports already worked before this diagnostic fix.
    let direct = query("domain(?w, List[T = Letter])", true);
    let wrapper = query("any_word(?w)", true);
    assert_eq!(direct.code, 0, "{}", direct.stderr);
    assert_eq!(wrapper.code, 0, "{}", wrapper.stderr);
    assert_eq!(direct.stdout, wrapper.stdout);
    assert!(
        direct.has_stdout_line("8 solution(s) shown — more exist, raise --max-results"),
        "{}",
        direct.stdout
    );
    let rows: Vec<_> = direct
        .stdout
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("?w ="))
        .collect();
    assert_eq!(
        &rows[..4],
        &[
            "?w = nil",
            "?w = cons(head: a, tail: nil)",
            "?w = cons(head: b, tail: nil)",
            "?w = cons(head: c, tail: nil)"
        ]
    );
    let ground = query("domain(nil(), List[T = Letter])", true);
    assert_eq!(ground.code, 0, "{}", ground.stderr);
    assert!(ground.has_stdout_line("1 solution(s)"), "{}", ground.stdout);
    let bare = query("domain(?x, Letter)", false);
    assert_eq!(bare.code, 0, "{}", bare.stderr);
    assert!(bare.has_stdout_line("3 solution(s)"), "{}", bare.stdout);
}

#[test]
fn wi7fp1m_missing_sort_is_a_diagnostic_not_no_solutions() {
    // Regression: both commands exited successfully with no solutions before the fix.
    for (pattern, import_list, missing) in [
        ("domain(nil(), List[T = Letter])", false, "List"),
        (
            "domain(nil(), List[T = MissingLetter])",
            true,
            "MissingLetter",
        ),
    ] {
        let out = query(pattern, import_list);
        assert_eq!(out.code, 1, "{}\n{}", out.stdout, out.stderr);
        assert!(out.has_diagnostic("error:", missing), "{}", out.stderr);
        assert!(out.stderr.contains("--pattern"), "{}", out.stderr);
        assert!(!out.has_stdout_line("no solutions"));
    }
}
