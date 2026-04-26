//! End-to-end `proof <rule> by derivation` exercise via the CLI.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("anthill-prove-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

#[test]
fn by_derivation_discharges_simple_horn_rule() {
    let src = r#"
        namespace test.derive.simple
          export Light, shines
          entity Light(state: String)
          fact Light(state: "bright")

          rule shines(?b) :- Light(state: ?b)
          proof shines by derivation end
        end
    "#;
    let path = write_temp("simple.anthill", src);

    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap()])
        .output()
        .expect("run anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(),
        "anthill prove failed:\nstdout:{stdout}\nstderr:{stderr}");
    assert!(stdout.contains("shines") && stdout.contains("proved"),
        "expected `shines: proved` in stdout, got:\n{stdout}");
}

#[test]
fn by_derivation_reports_unknown_when_unsatisfiable() {
    let src = r#"
        namespace test.derive.fail
          export Light, dark
          entity Light(state: String)
          fact Light(state: "bright")

          rule dark(?x) :- Light(state: ?x), eq(?x, "off")
          proof dark by derivation end
        end
    "#;
    let path = write_temp("fail.anthill", src);

    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap()])
        .output()
        .expect("run anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("dark") && stdout.contains("unknown"),
        "expected `dark: unknown`, got:\n{stdout}");
    assert!(!out.status.success(),
        "exit status should be non-zero on a failed obligation");
}
