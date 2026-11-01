//! WI-20261017-1Y96B — an eponymous sort as a receiver that denotes it.
//!
//! The ticket's program, `(Ep).em()` and `let t = Ep` then `t.em()` over `sort Ep { entity
//! Ep(name: String); operation em() -> Int64 = 8 }`, was refused as a dot on `Type` with no
//! member `em`, where the same spellings over a sort with no constructor of its name called
//! the companion. It was closed before this file by WI-20260902-JB6RS step 5, which made a
//! constructor's bare name its INSTANCE in a body and wrote its type with the bracket,
//! `Ep[]` (kernel-language.md §4.4). So the type value is `Ep[]`, and every spelling of it
//! is the receiver that denotes the sort (§5.4); the bare `Ep` is a value of the sort, and a
//! dot on it is a dot on that value.
//!
//! CONTROLS. These rows pin the reading; nothing of the ticket changed it, so no back-out
//! fails them. The `Ep` spellings answered the same on 6fcc35a5, measured with a probe
//! binary before WI-20260824-PAPX0's change, and `(Ep).em()` was refused there for its
//! missing field.

use anthill_core::eval::Value;

use crate::common::{interp_for, load_errors_of, load_kb_with, query_unary};

const EPON: &str = r#"
  sort Ep
    entity Ep(name: String)
    operation em() -> Int64 = 8
    operation greet(self: Ep) -> Int64 = 5
  end
  sort Fl
    entity Fl
    operation em() -> Int64 = 9
  end
"#;

fn source(ns: &str, body: &str) -> String {
    format!("namespace test.{ns}\n  import anthill.prelude.{{Type, Int64, String}}\n{EPON}\n{body}\nend\n")
}

fn int(ns: &str, body: &str) -> i64 {
    let mut interp = interp_for(&source(ns, body));
    match interp.call(&format!("test.{ns}.go"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

fn refusal(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, body));
    assert!(!errs.is_empty(), "{ns}: must be refused, and loaded clean");
    format!("{errs:?}")
}

#[test]
fn an_eponymous_sorts_type_is_a_receiver_in_every_spelling() {
    let go = |expr: &str| format!("  operation go() -> Int64 = {expr}");
    assert_eq!(int("y96b1w", &go("Ep.em()")), 8);
    assert_eq!(int("y96b1b", &go("Ep[].em()")), 8);
    assert_eq!(int("y96b1p", &go("(Ep[]).em()")), 8);
    assert_eq!(int("y96b1q", &go("(test.y96b1q.Ep[]).em()")), 8);
    assert_eq!(
        int("y96b1l", "  operation go() -> Int64 =\n    let t = Ep[]\n    t.em()"),
        8
    );
    assert_eq!(int("y96b1f", &go("(Fl[]).em()")), 9);
    // A rule body reads it the same way.
    for (ns, expr) in [("y96b1r", "(Ep[]).em()"), ("y96b1rq", "(test.y96b1rq.Ep[]).em()")] {
        let mut kb = load_kb_with(&source(ns, &format!("  rule r(?x) :- ?x <=> {expr}")));
        let answers: Vec<Value> = query_unary(&mut kb, &format!("test.{ns}.r"))
            .into_iter()
            .map(|(v, _)| v)
            .collect();
        assert!(matches!(answers.as_slice(), [Value::Int(8)]), "{ns}: {answers:?}");
    }
}

/// The bare name is the instance: a construction that leaves `name` out, refused with the
/// type's spelling, and for a fieldless constructor a value whose dot passes it to `em`.
#[test]
fn a_bare_eponymous_name_is_the_instance() {
    for (ns, body) in [
        ("y96b2p", "  operation go() -> Int64 = (Ep).em()"),
        ("y96b2l", "  operation go() -> Int64 =\n    let t = Ep\n    t.em()"),
    ] {
        let said = refusal(ns, body);
        assert!(
            said.contains("`Ep` is constructed without its field `name`")
                && said.contains("TYPE is written `Ep[]`"),
            "{ns}: {said}"
        );
    }
    let said = refusal("y96b2f", "  operation go() -> Int64 = (Fl).em()");
    assert!(said.contains("expected 0 arguments"), "{said}");
}

/// A member taking the value: through the type it is the call with no argument for `self`,
/// refused naming it; on a constructed value the dot passes the value, as before.
#[test]
fn a_member_taking_the_value_is_called_on_a_value() {
    let said = refusal("y96b3t", "  operation go() -> Int64 = (Ep[]).greet()");
    assert!(said.contains("no argument fills parameter `self`"), "{said}");
    assert_eq!(int("y96b3v", "  operation go() -> Int64 = Ep(name: \"x\").greet()"), 5);
    let said = refusal("y96b3e", "  operation go() -> Int64 = Ep(name: \"x\").em()");
    assert!(said.contains("expected 0 arguments"), "{said}");
}
