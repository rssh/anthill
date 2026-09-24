//! WI-20260924-EJMW4: `init` wrote `language: "rust"`, `build: "cargo"`,
//! `tools: ["cargo-test"]` into EVERY project, with no way to say otherwise —
//! measured on a Scala/sbt tree. The three are now read from the one build file in the
//! project directory, each overridable by its flag (`--language` / `--build` /
//! `--tool`); a field neither gives is left out, except the tools, which `init` refuses
//! to guess.
//!
//! Each test that scaffolds DRIVES the configuration: it files an item with no
//! `--acceptance` and reads back the acceptance `add` took from `Project.tools`, since a
//! `project.anthill` that merely says the right words proves nothing about what the
//! tracker does with them. Each refusal asserts that nothing was created.
//!
//! CONTROL. Put back the hardcoded triple and the positional-only argv and every test
//! here fails — MEASURED, all of them: the Scala and Go projects read as Rust, even the
//! Rust one never says where its configuration came from, the flags are refused as "not
//! a project name", and the refusals scaffold a Rust project instead. What passes either
//! way BY DESIGN is every test that scaffolds a Rust project with a bare `init`
//! (`common::plant_cargo_toml`; the golden transcript among them): the hardcode was
//! right for Rust, and they are the witness that detection did not cost that case.

use std::path::Path;
use std::process::{Command, Output};

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn init(dir: &Path, args: &[&str]) -> Output {
    let mut argv = vec!["-d", dir.to_str().unwrap(), "init"];
    argv.extend_from_slice(args);
    Command::new(BIN).args(&argv).output().expect("run init")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

fn project_file(dir: &Path) -> String {
    std::fs::read_to_string(dir.join("anthill-todo/project.anthill")).expect("read project.anthill")
}

fn scaffolded(dir: &Path) -> bool {
    dir.join("anthill-todo").exists()
}

/// File one item WITHOUT `--acceptance` and return its `- acceptance:` line — the
/// acceptance `add` took from `Project.tools`.
fn default_acceptance(dir: &Path) -> String {
    let add = Command::new(BIN)
        .args(["-d", dir.to_str().unwrap(), "add", "acceptance probe"])
        .output()
        .expect("run add");
    assert!(add.status.success(), "add failed: {}", stderr(&add));
    let open = dir.join("anthill-todo/open");
    let files: Vec<_> = std::fs::read_dir(&open)
        .expect("read open/")
        .map(|e| e.expect("dir entry").path())
        .collect();
    assert_eq!(files.len(), 1, "expected the one probe item in {}", open.display());
    let item = std::fs::read_to_string(&files[0]).expect("read item");
    item.lines()
        .find(|l| l.starts_with("- acceptance:"))
        .unwrap_or_else(|| panic!("no acceptance line in:\n{item}"))
        .to_string()
}

#[test]
fn init_reads_each_build_file() {
    for (file, language, build, tool) in [
        ("Cargo.toml", "rust", "cargo", "cargo-test"),
        ("build.sbt", "scala", "sbt", "sbt-test"),
        ("go.mod", "go", "go", "go-test"),
    ] {
        let tmp = tempfile::tempdir().expect("tempdir");
        std::fs::write(tmp.path().join(file), "").unwrap();

        let out = init(tmp.path(), &["demo"]);
        assert!(out.status.success(), "{file}: init failed: {}", stderr(&out));
        let project = project_file(tmp.path());
        assert!(
            project.contains(&format!(
                "fact Project(\n  name: \"demo\",\n  language: \"{language}\",\n  \
                 build: \"{build}\",\n  tools: [\"{tool}\"])"
            )),
            "{file}: expected {language}/{build}/{tool}, got:\n{project}"
        );
        assert!(
            stdout(&out).contains(&format!("(read from {file})")),
            "{file}: init must say where the configuration came from, got:\n{}",
            stdout(&out)
        );
        assert_eq!(default_acceptance(tmp.path()), format!("- acceptance: {tool}"), "{file}");
    }
}

#[test]
fn init_refuses_a_directory_with_no_build_file() {
    let tmp = tempfile::tempdir().expect("tempdir");

    let out = init(tmp.path(), &[]);
    assert_eq!(out.status.code(), Some(1), "stdout:\n{}", stdout(&out));
    let err = stderr(&out);
    assert!(
        err.contains("cannot tell the language, build and tools")
            && err.contains("none of Cargo.toml, build.sbt, go.mod")
            && err.contains("--tool"),
        "the refusal must name the files it looked for and the flags, got:\n{err}"
    );
    assert!(!scaffolded(tmp.path()), "a refused init must create nothing");
}

#[test]
fn init_refuses_two_build_files_unless_every_field_is_given() {
    let two_builds = || {
        let tmp = tempfile::tempdir().expect("tempdir");
        crate::common::plant_cargo_toml(tmp.path());
        std::fs::write(tmp.path().join("build.sbt"), "").unwrap();
        tmp
    };

    // A field left to the build file: WHICH one would be a guess.
    for args in [&[][..], &["--tool", "t"][..]] {
        let tmp = two_builds();
        let out = init(tmp.path(), args);
        assert_eq!(out.status.code(), Some(1), "{args:?}: stdout:\n{}", stdout(&out));
        assert!(
            stderr(&out).contains("more than one build file (Cargo.toml, build.sbt)"),
            "{args:?}: the refusal must name both files, got:\n{}",
            stderr(&out)
        );
        assert!(!scaffolded(tmp.path()), "{args:?}: a refused init must create nothing");
    }

    // Every field given: no build file is read, so two of them are no obstacle.
    let tmp = two_builds();
    let out = init(tmp.path(), &["--language", "scala", "--build", "sbt", "--tool", "sbt-test"]);
    assert!(out.status.success(), "init failed: {}", stderr(&out));
    assert!(stdout(&out).contains("(as given)"), "stdout:\n{}", stdout(&out));
    assert_eq!(default_acceptance(tmp.path()), "- acceptance: sbt-test");
}

#[test]
fn init_flags_override_the_build_file_field_by_field() {
    // The tools are replaced, not appended to; language and build still come from
    // Cargo.toml — a flag for one field does not throw away what the file pins.
    let tmp = tempfile::tempdir().expect("tempdir");
    crate::common::plant_cargo_toml(tmp.path());

    let out = init(tmp.path(), &["demo", "--tool", "cargo-test", "--tool=clippy"]);
    assert!(out.status.success(), "init failed: {}", stderr(&out));
    let project = project_file(tmp.path());
    assert!(
        project.contains(
            "fact Project(\n  name: \"demo\",\n  language: \"rust\",\n  build: \"cargo\",\n  \
             tools: [\"cargo-test\", \"clippy\"])"
        ),
        "the tools must be the flags' and the rest Cargo.toml's, got:\n{project}"
    );
    assert!(
        stdout(&out).contains("(read from Cargo.toml, overridden by the flags)"),
        "stdout:\n{}",
        stdout(&out)
    );
    assert_eq!(default_acceptance(tmp.path()), "- acceptance: cargo-test, clippy");

    // And the other way round: a language flag keeps the file's build and tool.
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(tmp.path().join("build.sbt"), "").unwrap();
    let out = init(tmp.path(), &["demo", "--language=java"]);
    assert!(out.status.success(), "init failed: {}", stderr(&out));
    assert!(
        project_file(tmp.path()).contains(
            "fact Project(\n  name: \"demo\",\n  language: \"java\",\n  build: \"sbt\",\n  \
             tools: [\"sbt-test\"])"
        ),
        "got:\n{}",
        project_file(tmp.path())
    );
}

#[test]
fn init_tool_alone_leaves_language_and_build_unset() {
    // No build file at all: `--tool` is enough, and the two optional slots are left
    // OUT rather than written empty or defaulted.
    let tmp = tempfile::tempdir().expect("tempdir");

    let out = init(tmp.path(), &["notes", "--tool", "review"]);
    assert!(out.status.success(), "init failed: {}", stderr(&out));
    let project = project_file(tmp.path());
    assert!(
        project.contains("fact Project(\n  name: \"notes\",\n  tools: [\"review\"])"),
        "language and build must be omitted, got:\n{project}"
    );

    // The omitted slots load clean — no warning on a plain read …
    let status = Command::new(BIN)
        .args(["-d", tmp.path().to_str().unwrap(), "status"])
        .output()
        .expect("run status");
    assert!(status.status.success(), "status failed: {}", stderr(&status));
    assert_eq!(stderr(&status), "", "a fresh project must load without a word");
    // … and the tool is the default acceptance.
    assert_eq!(default_acceptance(tmp.path()), "- acceptance: review");
}

#[test]
fn init_without_a_tool_needs_a_build_file_of_that_build_to_read_one_from() {
    // No build file at all.
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = init(tmp.path(), &["--language", "scala", "--build", "sbt"]);
    assert_eq!(out.status.code(), Some(1), "stdout:\n{}", stdout(&out));
    assert!(
        stderr(&out).contains("`init` needs a --tool")
            && stderr(&out).contains("none of Cargo.toml, build.sbt, go.mod to read one from"),
        "the refusal must name the missing --tool, got:\n{}",
        stderr(&out)
    );
    assert!(!scaffolded(tmp.path()), "a refused init must create nothing");

    // A build file of ANOTHER build: its tool describes a different project. Reading
    // it here wrote `build: "sbt"` beside `tools: ["cargo-test"]` (found in review).
    let tmp = tempfile::tempdir().expect("tempdir");
    crate::common::plant_cargo_toml(tmp.path());
    let out = init(tmp.path(), &["--language", "scala", "--build", "sbt"]);
    assert_eq!(out.status.code(), Some(1), "stdout:\n{}", stdout(&out));
    assert!(
        stderr(&out).contains("`--build sbt` is not Cargo.toml's cargo"),
        "got:\n{}",
        stderr(&out)
    );
    assert!(!scaffolded(tmp.path()), "a refused init must create nothing");

    // CONTROL: the same flags where the build file IS that build.
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(tmp.path().join("build.sbt"), "").unwrap();
    let out = init(tmp.path(), &["--language", "scala", "--build", "sbt"]);
    assert!(out.status.success(), "init failed: {}", stderr(&out));
    assert_eq!(default_acceptance(tmp.path()), "- acceptance: sbt-test");
}

#[test]
fn init_escapes_a_quote_it_was_given() {
    // A given value is escaped into its string literal, not refused: the file must
    // still PARSE, or its store binding is silently dropped.
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = init(tmp.path(), &["say \"hi\"", "--language", "c\\d", "--tool", "t"]);
    assert!(out.status.success(), "init failed: {}", stderr(&out));
    assert!(
        project_file(tmp.path())
            .contains("fact Project(\n  name: \"say \\\"hi\\\"\",\n  language: \"c\\\\d\","),
        "got:\n{}",
        project_file(tmp.path())
    );
    let status = Command::new(BIN)
        .args(["-d", tmp.path().to_str().unwrap(), "status"])
        .output()
        .expect("run status");
    assert_eq!(stderr(&status), "", "the escaped file must load without a word");
    assert_eq!(default_acceptance(tmp.path()), "- acceptance: t");
}

#[test]
fn init_refuses_a_repeated_empty_or_dash_led_value() {
    for (args, expected) in [
        (&["--language", "a", "--language", "b"][..], "was given a language twice"),
        (&["foo", "--name", "bar"][..], "was given a project name twice"),
        (&["--tool", "t", "--tool=t"][..], "was given the tool `t` twice"),
        (&["--tool="][..], "`init --tool` expects a tool name, and it was empty"),
        (&[""][..], "`init` expects a project name, and it was empty"),
        // The `=` spelling must not smuggle in what the separate one refuses.
        (&["--name=--help"][..], "`init --name` expects a project name, got the flag `--help`"),
        (&["--tool", "a, b"][..], "a tool name cannot hold `,`"),
    ] {
        let tmp = tempfile::tempdir().expect("tempdir");
        crate::common::plant_cargo_toml(tmp.path());
        let out = init(tmp.path(), args);
        assert_eq!(out.status.code(), Some(2), "{args:?}: stdout:\n{}", stdout(&out));
        assert!(
            stderr(&out).contains(expected),
            "{args:?}: expected {expected:?}, got:\n{}",
            stderr(&out)
        );
        assert!(!scaffolded(tmp.path()), "{args:?}: a refused init must create nothing");
    }
}

#[test]
fn init_help_names_the_build_files_and_what_a_tool_is() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = init(tmp.path(), &["--help"]);
    assert!(out.status.success());
    let help = stdout(&out);
    for needle in [
        "Cargo.toml   rust, cargo, cargo-test",
        "build.sbt    scala, sbt, sbt-test",
        "go.mod       go, go, go-test",
        "free-form LABEL",
    ] {
        assert!(help.contains(needle), "help must say {needle:?}, got:\n{help}");
    }
}
