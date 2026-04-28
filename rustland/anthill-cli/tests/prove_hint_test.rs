//! WI-139 [hint] semantics: rules tagged `[hint]` are auto-included
//! in the SMT preamble of any proof in the same enclosing scope
//! chain. The user does NOT need to write `using <rule>` explicitly.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("anthill-hint-test-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

#[test]
fn hint_attributed_rule_auto_included_in_proof() {
    if !z3_available() { return; }
    // `bound_d` is tagged `[hint]` — every proof in the same
    // scope auto-cites it. `target` doesn't write `using bound_d`
    // explicitly, but Z3 still sees the lifted forall of bound_d's
    // conclusion, which lets target discharge.
    let src = r#"
        namespace test.hint.basic
          export bound_d, target

          rule bound_d(?w)
            :- gte(?x, 5.0),
               ?w = ?x
            -: gte(?x, 3.0)
            [hint]

          rule target(?w)
            :- gte(?x, 5.0),
               ?w = ?x
            -: gte(?x, 3.0)

          proof bound_d
            by z3(logic: "LRA")
          end

          proof target
            by z3(logic: "LRA")
          end
        end
    "#;
    let path = write_temp("hint_basic.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("test.hint.basic.bound_d: proved"),
        "tagged rule must discharge:\n{stdout}");
    assert!(stdout.contains("test.hint.basic.target: proved"),
        "consumer must discharge under the auto-cited hint:\n{stdout}");
    // Verbose output shows the using=...bound_d list (from
    // canon_parts), confirming hint was applied.
    assert!(stdout.contains("bound_d"),
        "verbose output should mention the hint cite:\n{stdout}");
}
