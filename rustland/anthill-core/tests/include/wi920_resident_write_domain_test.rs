//! WI-920 — A RESIDENT PERSISTED FACT IS FILED UNDER ITS OWN DOMAIN.
//!
//! The two resident writers of proposal 057's write seam — `assert_persistent`'s
//! resident arm and `persist_mirrored`, the one every `Store.persist` reaches — stamped
//! every fact they asserted with a literal pair: sort `Fact`, domain `anthill.todo`. The
//! sort was right (it is the loader's own default for a `fact` with no `sort:`
//! annotation). The domain was one tool's namespace, applied to every embedder's writes.
//!
//! DRIVEN, a source `fact Widget920()` inside `namespace test.alpha` and then the SAME
//! fact persisted at runtime, beside one from `test.beta`, through a `ByDomain` store
//! (whose output FILE is the domain, so the domain is directly observable):
//!
//!     source fact (sort, domain) = [("Fact", "test.alpha")]
//!     after the runtime persist  = [("Fact", "test.alpha"), ("Fact", "anthill.todo")]
//!     files written              = ["anthill/todo.anthill"]
//!
//! Two readings of one fact — `assert_fact` dedups on `(term, sort, domain)`, so a
//! different domain is a different fact — and both namespaces' facts collapsed into one
//! file named for a tool neither program mentions. `by_domain` of their own namespaces
//! did not see them.
//!
//! Post-fix the same run gives one entry, `[("Fact", "test.alpha")]`, and
//! `["alpha.anthill", "beta.anthill"]`.
//!
//! THE DOMAIN IS A DECISION, NOT A DERIVATION, and the site says so: a runtime write has
//! no source position, and a source `fact` takes the scope it is WRITTEN in — which for
//! one functor may be any scope that can see it — so nothing reproduces that. Of the
//! scopes available, the functor's DECLARING scope is the only one that is about this
//! functor at all. Where the two coincide (a source fact written where its functor is
//! declared) the runtime write is then not merely similar to the source one but the
//! SAME fact, which is what the first test pins.
//!
//! The constant was not even right for the tool it named: anthill-todo declares
//! `WorkItem` in `anthill.stage0`, and its own persisted work items are loaded at file
//! top level, i.e. under `_global`. Three spellings, no two agreeing.
//!
//! A head that declares no scope at all — a bare-interned name, which `Store.persist`
//! accepts and `persistence_builtins_test` persists — takes `_global`, which is not a
//! stand-in but the domain the loader itself gives a TOP-LEVEL source `fact` (measured).
//! The last test pins that, because a first cut of this fix REFUSED that head and broke
//! two existing tests: an undeclared name has a right answer, so a refusal was the wrong
//! kind of loud.
//!
//! STDLIB LOADS: four, one per `#[test]`.

use anthill_core::eval::{Interpreter, Value};
use anthill_core::persistence::file_store::{FileConvention, FileStore};

use crate::common::interp_for;

/// `Widget920` is declared AND asserted inside `test.alpha`, so a runtime write of it
/// should meet the source fact exactly; `Gadget920` is a second namespace, so the two
/// cannot share an output file unless the domain is being ignored.
const SRC: &str = "namespace test.alpha\n  entity Widget920\n  fact Widget920()\nend\n\
                   namespace test.beta\n  entity Gadget920\nend\n";

/// A `FileStore(root, ByDomain)` value, registered as the mirror. `ByDomain` names each
/// output file after the fact's domain — the one convention that makes the domain
/// visible from outside the KB.
fn by_domain_store(interp: &mut Interpreter, root: &std::path::Path) -> Value {
    let fs = interp.kb_mut().intern("FileStore");
    let by_domain = interp.kb_mut().intern("ByDomain");
    let root_sym = interp.kb_mut().intern("root");
    let convention_sym = interp.kb_mut().intern("convention");
    let store_val = Value::Entity {
        functor: fs,
        pos: vec![].into(),
        named: vec![
            (root_sym, Value::Str(root.to_str().unwrap().to_string())),
            (
                convention_sym,
                Value::Entity {
                    functor: by_domain,
                    pos: vec![].into(),
                    named: vec![].into(),
                },
            ),
        ]
        .into(),
    };
    let key = interp
        .store_canonical_key(&store_val)
        .expect("canonical key");
    interp
        .register_mirror(
            key,
            Box::new(FileStore::new(root.to_path_buf(), FileConvention::ByDomain)),
        )
        .expect("a file store declares no intrinsic policy (WI-919)");
    store_val
}

/// A nullary `qname()` carrier — the fact to persist.
fn nullary(interp: &mut Interpreter, qname: &str) -> Value {
    let sym = interp
        .kb_mut()
        .try_resolve_symbol(qname)
        .unwrap_or_else(|| panic!("resolve `{qname}`"));
    Value::Entity {
        functor: sym,
        pos: vec![].into(),
        named: vec![].into(),
    }
}

fn persist(interp: &mut Interpreter, store: &Value, qname: &str) {
    let fact = nullary(interp, qname);
    interp
        .call(
            "anthill.persistence.Store.persist",
            &[store.clone(), fact, Value::Unit],
        )
        .expect("persist ok");
}

/// Every live rule for `qname`, as `(sort, domain)` QUALIFIED-name pairs. Qualified, not
/// short: `try_resolve_symbol` keys on the qualified name while `intern` mints a symbol
/// from the raw string, and a probe that mixes the two reads a namespace's domain as
/// absent — measured, on this fixture.
fn keys_of(interp: &mut Interpreter, qname: &str) -> Vec<(String, String)> {
    let sym = interp
        .kb_mut()
        .try_resolve_symbol(qname)
        .unwrap_or_else(|| panic!("resolve `{qname}`"));
    let kb = interp.kb();
    kb.rules_by_functor(sym)
        .iter()
        .map(|&rid| {
            (
                kb.rule_clause_kind(rid).to_string(),
                kb.qualified_name_of(kb.rule_domain(rid)).to_string(),
            )
        })
        .collect()
}

/// The `.anthill` files under `root`, relative and sorted.
fn files_written(root: &std::path::Path) -> Vec<String> {
    let mut out: Vec<String> = anthill_core::fs_util::collect_files(root, &["anthill"])
        .unwrap_or_default()
        .iter()
        .map(|f| f.strip_prefix(root).unwrap().display().to_string())
        .collect();
    out.sort();
    out
}

/// THE DEFECT, at its sharpest. `assert_fact` dedups on `(term, sort, domain)`, so
/// asserting a fact the source already declares is a no-op IF the seam agrees with the
/// loader about where the fact belongs — and a second, separately-filed copy of one fact
/// if it does not.
#[test]
fn a_runtime_persisted_fact_is_the_same_fact_as_its_source_twin() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut interp = interp_for(SRC);
    let store = by_domain_store(&mut interp, dir.path());
    let before = keys_of(&mut interp, "test.alpha.Widget920");
    assert_eq!(
        before,
        vec![("Fact".to_owned(), "test.alpha".to_owned())],
        "control: the source fact is filed under the namespace it is written in, with \
         the loader's unannotated-`fact` sort",
    );

    persist(&mut interp, &store, "test.alpha.Widget920");

    assert_eq!(
        keys_of(&mut interp, "test.alpha.Widget920"),
        before,
        "the runtime write must land on the SAME (sort, domain) and so dedup into the \
         same fact — pre-fix this was a second entry under `anthill.todo`",
    );
}

/// The same defect seen from OUTSIDE the KB: with a `ByDomain` store the domain picks
/// the output file, so a constant domain files every namespace's facts together.
#[test]
fn facts_from_two_namespaces_are_filed_under_their_own_domains() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut interp = interp_for(SRC);
    let store = by_domain_store(&mut interp, dir.path());

    persist(&mut interp, &store, "test.alpha.Widget920");
    persist(&mut interp, &store, "test.beta.Gadget920");
    interp
        .call(
            "anthill.persistence.Store.flush",
            &[store.clone(), Value::Unit],
        )
        .expect("flush ok");

    assert_eq!(
        files_written(dir.path()),
        vec!["alpha.anthill".to_owned(), "beta.anthill".to_owned()],
        "each fact goes to its own domain's file — pre-fix BOTH went to \
         `anthill/todo.anthill`, a file named for a tool neither namespace mentions",
    );
}

/// CONTROL, green on BOTH sides: `Store.persist` still works, still writes, and the
/// content is unchanged — the fix moves where a fact is FILED, not whether it persists.
/// Without this, the two tests above would also pass if persisting had stopped happening.
#[test]
fn the_persisted_content_is_unchanged() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut interp = interp_for(SRC);
    let store = by_domain_store(&mut interp, dir.path());

    persist(&mut interp, &store, "test.beta.Gadget920");
    interp
        .call(
            "anthill.persistence.Store.flush",
            &[store.clone(), Value::Unit],
        )
        .expect("flush ok");

    let written = files_written(dir.path());
    assert_eq!(written.len(), 1, "one fact, one file");
    let text = std::fs::read_to_string(dir.path().join(&written[0])).expect("read back");
    assert!(
        text.contains("Gadget920"),
        "the fact itself still reaches disk; only its FILE changed. Got: {text:?}",
    );
}

/// A head that DECLARES NOTHING — `intern`ed, never defined — is the shape
/// `persistence_builtins_test` persists, so the seam must still take it. It is filed
/// under `_global`, the domain a top-level source `fact` gets (measured on this tree),
/// rather than refused: an undeclared name has a right answer, and my first cut of this
/// fix refused it and broke those two tests.
#[test]
fn a_head_that_declares_no_scope_is_filed_under_global() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut interp = interp_for(SRC);
    let store = by_domain_store(&mut interp, dir.path());
    let undeclared = interp.kb_mut().intern("Undeclared920");
    let fact = Value::Entity {
        functor: undeclared,
        pos: vec![].into(),
        named: vec![].into(),
    };

    interp
        .call(
            "anthill.persistence.Store.persist",
            &[store.clone(), fact, Value::Unit],
        )
        .expect("an undeclared head still persists");

    let kb = interp.kb();
    let domains: Vec<String> = kb
        .rules_by_functor(undeclared)
        .iter()
        .map(|&rid| kb.qualified_name_of(kb.rule_domain(rid)).to_string())
        .collect();
    assert_eq!(
        domains,
        vec!["_global".to_owned()],
        "no declaring scope means `_global`, not a constant naming someone else's tool",
    );
}
