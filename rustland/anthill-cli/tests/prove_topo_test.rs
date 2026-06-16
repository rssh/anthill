//! Phase γ.3 (proposal 030): proof discharge runs in dependency
//! order, not alphabetical, so cite chains work regardless of
//! how the user names rules.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("anthill-topo-test-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

#[test]
fn cite_chain_discharges_in_dependency_order_not_alphabetical() {
    if !z3_available() { return; }
    // `aaa_consumer` cites `zzz_lemma`. Alphabetically aaa_ comes
    // before zzz_, so under the old alphabetical sort the consumer
    // would dispatch first — and its cite-resolution would fail
    // because zzz_lemma isn't yet in `discharged_this_run` and
    // (with --no-cache) has no sidecar. Topo sort must put
    // zzz_lemma first.
    let src = r#"
        namespace test.topo

          rule zzz_lemma: gte(?x, 3.0)
            :- gte(?x, 5.0)

          rule aaa_consumer: gte(?x, 3.0)
            :- gte(?x, 5.0)

          proof zzz_lemma
            by z3(logic: "LRA")
          end

          proof aaa_consumer
            using zzz_lemma
            by z3(logic: "LRA")
          end
        end
    "#;
    let path = write_temp("topo_chain.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("test.topo.zzz_lemma: proved"),
        "lemma must discharge:\n{stdout}");
    assert!(stdout.contains("test.topo.aaa_consumer: proved"),
        "consumer must discharge after its cited lemma:\n{stdout}");
    // Crucial ordering check: zzz_lemma's "✓" must appear before
    // aaa_consumer's, otherwise topo sort isn't in effect.
    let pos_lemma = stdout.find("test.topo.zzz_lemma:").unwrap();
    let pos_consumer = stdout.find("test.topo.aaa_consumer:").unwrap();
    assert!(pos_lemma < pos_consumer,
        "zzz_lemma must discharge before aaa_consumer:\n{stdout}");
}
