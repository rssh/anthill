//! WI-419 — same-spec requirement forwarding must respect element identity.
//!
//! `build_dep_projection` Strategy 1 (typing.rs) forwards a caller `requires`
//! dictionary to a cross-sort callee by matching the callee's requirement dep
//! against the caller's `requires` entries via `entries_cover`. `entries_cover`
//! is wildcard-tolerant: a caller `Tag[A]` covers a dep `Tag[B]` whenever either
//! element is a type param. With a SINGLE covering entry that is correct, but a
//! caller declaring TWO `requires` of the SAME spec over DISTINCT element params
//! (`requires Tag[A], Tag[B]`) had BOTH cover a dep over one of them, and a blind
//! first-match forwarded the WRONG dictionary — a soundness bug (wrong runtime
//! dispatch).
//!
//! Repro: `Pair2 requires Tag[A], Tag[B]`; `runSecond(a, b) = Wrap.useTag(b)`
//! delegates to a cross-sort `Wrap requires Tag[W]` op over the SECOND param `B`.
//! At `Pair2.runSecond(red(), blue())` (A := Red, B := Blue) the forwarded dict
//! must be `B`'s (Blue ⇒ `tagval = 2`), not `A`'s (Red ⇒ `1`). Pre-fix Strategy 1
//! position-matched the first same-spec entry (`Tag[A]`) and returned `1`.
//!
//! The fix disambiguates by σ-class: when more than one entry covers, it prefers
//! the unique covering entry whose element resolves, through the call-site subst,
//! to the same unification variable as the dep's element. The control `runFirst`
//! (delegates over `A`) stays correct, proving the disambiguation is by identity,
//! not a blanket flip to last-match.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

const SRC: &str = r#"namespace test.wi419
  import anthill.prelude.Int64

  sort Tag
    sort T = ?
    operation tagval(x: T) -> Int64
  end

  sort Red
    entity red
    fact Tag[T = Red]
    operation tagval(x: Red) -> Int64 = 1
  end

  sort Blue
    entity blue
    fact Tag[T = Blue]
    operation tagval(x: Blue) -> Int64 = 2
  end

  sort Wrap
    sort W = ?
    requires Tag[W]
    operation useTag(x: W) -> Int64 = Tag.tagval(x)
  end

  sort Pair2
    sort A = ?
    sort B = ?
    requires Tag[A]
    requires Tag[B]
    operation runSecond(a: A, b: B) -> Int64 = Wrap.useTag(b)
    operation runFirst(a: A, b: B) -> Int64 = Wrap.useTag(a)
  end

  operation driveSecond() -> Int64 = Pair2.runSecond(red(), blue())
  operation driveFirst() -> Int64 = Pair2.runFirst(red(), blue())
end
"#;

fn load_errors() -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(SRC).expect("parse WI-419 repro"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

#[test]
fn repro_loads_clean() {
    let errs = load_errors();
    assert!(errs.is_empty(), "WI-419 repro must load clean: {errs:?}");
}

/// The bug: delegating over the SECOND same-spec requirement must forward THAT
/// param's dictionary. `runSecond` delegates `Wrap.useTag(b)` (dep over `B`);
/// with `B := Blue` the result must be `2` (`Blue.tagval`). Pre-fix it returned
/// `1` because Strategy 1 forwarded the FIRST same-spec slot (`A` = Red).
#[test]
fn forwards_second_same_spec_requirement() {
    let mut interp = crate::common::interp_for(SRC);
    match interp.call("test.wi419.driveSecond", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 2,
            "runSecond delegates over B (Blue); the forwarded dict must be B's \
             (tagval = 2), not the first same-spec slot A's (Red, 1); got {n}"
        ),
        other => panic!(
            "driveSecond should dispatch Wrap.useTag(b) via B's forwarded \
             requirement and return 2; got {other:?}"
        ),
    }
}

/// Control: delegating over the FIRST same-spec requirement stays correct.
/// `runFirst` delegates `Wrap.useTag(a)` (dep over `A`); with `A := Red` the
/// result is `1`. This guards against a naive "always pick the last/other slot"
/// fix — the disambiguation must be by element identity.
#[test]
fn forwards_first_same_spec_requirement() {
    let mut interp = crate::common::interp_for(SRC);
    match interp.call("test.wi419.driveFirst", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 1,
            "runFirst delegates over A (Red); the forwarded dict must be A's \
             (tagval = 1); got {n}"
        ),
        other => panic!(
            "driveFirst should dispatch Wrap.useTag(a) via A's forwarded \
             requirement and return 1; got {other:?}"
        ),
    }
}
