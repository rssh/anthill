//! `anthill check` verifies the scope axiom of a `requires` clause by re-reading the
//! clause, through the view: a requirement whose binding is written through a type alias
//! (`requires Show[T = Money]`) is held on another carrier than a term, and is checked as
//! the one written out is — under the name its type gives it.
//!
//! Backed out (the checker refusing a `SortRequiresInfo` row that is no term): exit 1,
//! "non-term SortRequiresInfo row is unsupported", for every `requires` record in the
//! program — the written one too, since the checker reads the whole relation.
//!
//! Run with its own cache (`ANTHILL_CACHE_DIR`) and working directory, as the other
//! `check` tests are: the witness directory is keyed by the working directory.

use std::process::Command;

use crate::common::write_temp;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

#[test]
fn a_requirement_written_through_an_alias_passes_its_scope_axiom() {
    let path = write_temp(
        "scope-axiom-requires.anthill",
        r#"
namespace test.chk
  import anthill.prelude.{Int64}
  sort Money = Int64
  sort Show[T]
    operation show(x: T) -> Int64
  end
  sort Aliased
    entity aliased
    requires Show[T = Money]
  end
  sort Written
    entity written
    requires Show[T = Int64]
  end
end
"#,
    );
    let dir = path.parent().expect("a file in a directory");
    let out = Command::new(ANTHILL_BIN)
        .args(["check", "scope-axiom-requires.anthill"])
        .current_dir(dir)
        .env("ANTHILL_CACHE_DIR", dir.join("cache"))
        .output()
        .expect("run anthill");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "stdout:\n{stdout}\nstderr:\n{stderr}");
    for sort in ["Aliased", "Written"] {
        let line = format!("✓ test.chk.{sort}.requires.Show_Int64");
        assert!(stdout.contains(&line), "wants {line}:\n{stdout}");
    }
}
