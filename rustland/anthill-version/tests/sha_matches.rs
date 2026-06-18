//! WI-160 regression: the SHA baked at build time must match the repo's
//! current HEAD (the `build.rs` `rerun-if-changed` on HEAD keeps it fresh
//! across commits). Skipped when built outside a git checkout, where the
//! embedded value is the literal `"unknown"`.

use std::process::Command;

#[test]
fn embedded_sha_matches_head() {
    let head = match Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
    {
        Ok(o) if o.status.success() => String::from_utf8(o.stdout).unwrap().trim().to_string(),
        _ => {
            eprintln!("not a git checkout — skipping SHA-match assertion");
            return;
        }
    };
    // Compare by common prefix rather than exact equality: git's `--short`
    // abbreviation length is repo-content-dependent and can lengthen over
    // time, so the same commit may render as `c4b469a` here and `c4b469ab`
    // there. A prefix match still denotes the same commit; a stale SHA (a
    // different commit) diverges in the prefix and is caught.
    let sha = anthill_version::GIT_SHA;
    assert!(
        head.starts_with(sha) || sha.starts_with(&head),
        "embedded GIT_SHA ({sha}) does not match HEAD ({head}); \
         build.rs must re-run when HEAD moves"
    );
}

#[test]
fn build_date_is_nonempty() {
    assert!(
        !anthill_version::BUILD_DATE.is_empty(),
        "build date must be populated"
    );
}

#[test]
fn format_version_carries_all_three_fields() {
    let v = anthill_version::format_version("anthill-demo", "9.9.9");
    assert!(v.contains("anthill-demo"));
    assert!(v.contains("9.9.9"));
    assert!(v.contains(anthill_version::GIT_SHA));
    assert!(v.contains(anthill_version::BUILD_DATE));
}
