//! Phase 5 — `ranking` meta-tactic (WI-100).
//!
//! `ranking(boundedness: <rule>, decrease: <rule>)` dispatches two
//! sub-queries through the standard SMT path and combines verdicts.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("anthill-ranking-test-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

const SRC_BOTH_UNSAT: &str = r#"
    namespace test.ranking.ok
      entity State(upc: Int64, upc_next: Int64)

      -- Ranking function: R(upc) = -upc. Post-armed invariant: -6 ≤ upc < 0.
      -- Boundedness violation: a state where R < 0 (i.e. upc > 0).
      rule bound_violation(?marker)
        :- State(upc: ?u, upc_next: ?_),
           gte(?u, -6),
           lt(?u, 0),
           lt(0, ?u),                 -- contradicts the post-armed bound
           eq(?marker, ?u)

      -- Decrease violation: a bad-step transition where R(s') >= R(s)
      -- (i.e. upc_next + upc >= 0 — would imply R does not decrease).
      -- For the bad-step model upc' = upc + 1, this is upc + 1 + upc >= 0,
      -- i.e. 2*upc + 1 >= 0, i.e. upc >= 0 — but upc < 0 in scope.
      rule decrease_violation(?marker)
        :- State(upc: ?u, upc_next: ?n),
           gte(?u, -6),
           lt(?u, 0),
           eq(?n, add(?u, 1)),
           gte(?n, ?u),               -- negate strict decrease
           lt(?n, ?u),                 -- which is impossible
           eq(?marker, ?u)

      rule rank_proof(?marker) :- eq(?marker, true)

      proof rank_proof
        by z3(tactic: ranking(boundedness: bound_violation,
                              decrease: decrease_violation),
              logic: "LIA")
      end
    end
"#;

#[test]
fn ranking_with_both_subqueries_unsat_proves() {
    if !z3_available() { return; }
    let path = write_temp("ok.anthill", SRC_BOTH_UNSAT);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("ranking sub-queries:"),
        "verbose must surface the meta-tactic dispatch: {stdout}");
    assert!(stdout.contains("rank_proof: proved"),
        "both unsat ⇒ proved: {stdout}");
}

#[test]
fn ranking_with_failing_decrease_disproves() {
    if !z3_available() { return; }
    // The decrease query is satisfiable here (there exists an x>0
    // making the body hold). The meta-tactic must surface the failing
    // sub-query name.
    let src = r#"
        namespace test.ranking.fail
          entity Cfg(scale: Int64)
          fact Cfg(scale: 5)

          -- Unsat: bound_ok body asserts gt(s, 999) with s = 5.
          rule bound_ok(?marker)
            :- Cfg(scale: ?s), gt(?s, 999), eq(?marker, ?s)

          -- Sat: decrease_bad body asserts gt(s, 0) with s = 5.
          rule decrease_bad(?marker)
            :- Cfg(scale: ?s), gt(?s, 0), eq(?marker, ?s)

          rule rank_proof_bad(?marker) :- eq(?marker, true)

          proof rank_proof_bad
            by z3(tactic: ranking(boundedness: bound_ok,
                                  decrease: decrease_bad),
                  logic: "LIA")
          end
        end
    "#;
    let path = write_temp("fail.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("ranking sub-query `test.ranking.fail.decrease_bad` failed"),
        "failing sub-query must surface in the diagnostic: {stdout}");
}
