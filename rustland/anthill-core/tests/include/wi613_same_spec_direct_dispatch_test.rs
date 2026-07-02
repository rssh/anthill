//! WI-613 — direct-body spec-op dispatch must respect requirement element identity.
//!
//! Sibling of WI-419. WI-419 fixed same-spec requirement *forwarding*
//! (`build_dep_projection` → `entries_cover`, the cross-sort delegation path).
//! This is the same soundness hole in the *direct-body-dispatch* attribution
//! path: `find_requires_location` / `find_requires_slot` (typing.rs) match a
//! body spec-op call against the enclosing sort's `requires` chain via
//! `entry_matches_subst`, which is wildcard-tolerant — a call on element `B`
//! matches a `requires Eq[A]` entry whenever either element is a type param. A
//! sort declaring TWO `requires` of the SAME spec over DISTINCT element params
//! (`requires Tag[A], Tag[B]`) had BOTH entries match a body call, and the blind
//! first-match (`.position` / DFS-first) attributed the call to the WRONG slot,
//! reading the wrong `__req_*` dictionary at runtime.
//!
//! Repro: `Pair2 requires Tag[A], Tag[B]`; `runSecond(a, b) = Tag.tagval(b)`
//! dispatches the spec op DIRECTLY on the enclosing sort over the SECOND param
//! `B`. At `Pair2.runSecond(red(), blue())` (A := Red, B := Blue) the call must
//! read `B`'s dictionary (Blue ⇒ `tagval = 2`), not `A`'s (Red ⇒ `1`). Pre-fix
//! `find_requires_location` matched the first same-spec entry (`Tag[A]`, slot 0)
//! and returned `1`.
//!
//! Note the direct call routes through `find_requires_location` (the PRIMARY
//! defer path), which a fix touching only `find_requires_slot` (the fallback)
//! would miss — hence a distinct regression from WI-419.
//!
//! The fix disambiguates by σ-class: when more than one entry matches, prefer
//! the unique entry whose element resolves, through the call-site subst + the
//! enclosing rigids, to the same unification variable as the per-call element.
//! The control `runFirst` (dispatches over `A`) stays correct, proving the
//! disambiguation is by identity, not a blanket flip to last-match.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

const SRC: &str = r#"namespace test.wi613
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

  sort Pair2
    sort A = ?
    sort B = ?
    requires Tag[A]
    requires Tag[B]
    operation runSecond(a: A, b: B) -> Int64 = Tag.tagval(b)
    operation runFirst(a: A, b: B) -> Int64 = Tag.tagval(a)
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
    parsed.push(parse::parse(SRC).expect("parse WI-613 repro"));
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
    assert!(errs.is_empty(), "WI-613 repro must load clean: {errs:?}");
}

/// The bug: a direct body dispatch over the SECOND same-spec requirement must
/// read THAT param's dictionary. `runSecond` dispatches `Tag.tagval(b)` (call
/// over `B`); with `B := Blue` the result must be `2` (`Blue.tagval`). Pre-fix
/// it returned `1` because attribution picked the FIRST same-spec slot (`A` = Red).
#[test]
fn dispatches_second_same_spec_requirement() {
    let mut interp = crate::common::interp_for(SRC);
    match interp.call("test.wi613.driveSecond", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 2,
            "runSecond dispatches Tag.tagval over B (Blue); the read dict must be \
             B's (tagval = 2), not the first same-spec slot A's (Red, 1); got {n}"
        ),
        other => panic!(
            "driveSecond should dispatch Tag.tagval(b) via B's requirement and \
             return 2; got {other:?}"
        ),
    }
}

/// Control: a direct body dispatch over the FIRST same-spec requirement stays
/// correct. `runFirst` dispatches `Tag.tagval(a)` (call over `A`); with `A := Red`
/// the result is `1`. Guards against a naive "always pick the other slot" fix —
/// the disambiguation must be by element identity.
#[test]
fn dispatches_first_same_spec_requirement() {
    let mut interp = crate::common::interp_for(SRC);
    match interp.call("test.wi613.driveFirst", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 1,
            "runFirst dispatches Tag.tagval over A (Red); the read dict must be \
             A's (tagval = 1); got {n}"
        ),
        other => panic!(
            "driveFirst should dispatch Tag.tagval(a) via A's requirement and \
             return 1; got {other:?}"
        ),
    }
}
