//! WI-729 (WI-714 follow-up F1) — a METHOD CALL whose receiver is a BARE-QUALIFIED
//! rule reference (`Queen.find.where(λ)`, `ns.rule.where(λ)`).
//!
//! WI-714 landed all three CITATION positions of a rule-as-`Relation[T]`, including
//! the bare-qualified `Sort.rule` / `ns.rule` (the loader collapses the `field_access`
//! Ident-chain to the same `var_ref(Ref(rule))` the bare-unqualified name lowers to).
//! WI-723 landed the METHOD CALL on the bare-UNQUALIFIED form (`person_row.where(λ)`
//! re-routes to a dot call, so `where`'s row-lambda param types the binder).
//!
//! The two did not meet: the scope-blind converter flattens `Queen.find.where(λ)` into
//! the single dotted functor `"Queen.find.where"`, and `try_identifier_dot_call` only
//! probed the SINGLE-segment head (`Queen`) — a sort, so no re-route — leaving the
//! whole thing on the qualified-name path as a loud `UnresolvedName`. The receiver
//! probe now splits on the LAST dot, so the multi-segment prefix (`Queen.find`) reaches
//! the same read-only rule resolution the bare + applied halves use.
//!
//! Nothing was blocked before (`let r = Queen.find` + `r.where(λ)` works, WI-723) —
//! only the inline spelling. These tests pin the inline spelling to the let-bound one.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with, try_load_kb_with_files};

/// A `Sort.rule` receiver — the proposal's canonical `Queen.find`. The inline
/// `Queen.find.where(λ)` must LOAD, TYPE and EVALUATE identically to the let-bound
/// `let r = Queen.find; r.where(λ)` spelling that already worked.
const SORT_SRC: &str = r#"
namespace test.wi729sort
  import anthill.prelude.{Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}

  sort Queen
    entity queen(row: Int64, col: Int64)
    rule find(?row) :- queen(row: ?row, col: ?)
  end
  fact queen(row: 1, col: 1)
  fact queen(row: 2, col: 3)

  -- WI-729: the INLINE spelling — a method call on the bare-qualified rule ref.
  operation inlineRows() -> List[Int64] effects Error =
    let r = Queen.find.where(lambda c -> eq(c, 2))
    r.takeN(5)

  -- the let-bound spelling (WI-714 citation + WI-723 dot call), the reference answer.
  operation letBoundRows() -> List[Int64] effects Error =
    let q = Queen.find
    let r = q.where(lambda c -> eq(c, 2))
    r.takeN(5)

  -- unfiltered, to prove the guard above actually drops a row.
  operation allRows() -> List[Int64] effects Error =
    let r = Queen.find
    r.takeN(5)
end
"#;

/// ACCEPTANCE: `Queen.find.where(λ)` loads, types and evals equal to the let-bound
/// spelling — and the filter really constrains (row 1 is dropped from `[1, 2]`).
#[test]
fn wi729_sort_qualified_receiver_method_call_matches_let_bound() {
    let mut interp = interp_for(SORT_SRC);
    let inline = interp
        .call("test.wi729sort.inlineRows", &[])
        .expect("the inline `Queen.find.where(λ)` spelling runs");
    let let_bound = interp
        .call("test.wi729sort.letBoundRows", &[])
        .expect("the let-bound spelling runs");
    let all = interp
        .call("test.wi729sort.allRows", &[])
        .expect("the unfiltered relation runs");

    assert_eq!(
        collect_int_list(&inline),
        vec![2],
        "`Queen.find.where(c -> eq(c, 2))` keeps only row 2"
    );
    assert_eq!(
        collect_int_list(&inline),
        collect_int_list(&let_bound),
        "the inline spelling must evaluate exactly like `let q = Queen.find; q.where(λ)`"
    );
    let mut unfiltered = collect_int_list(&all);
    unfiltered.sort();
    assert_eq!(
        unfiltered,
        vec![1, 2],
        "the unfiltered relation has both rows — so the where above really dropped one"
    );
}

/// The other multi-segment prefix: a NAMESPACE-qualified rule from another file
/// (`test.wi729ns.data.person_row.where(λ)`, a 4-segment prefix). The prefix reaches
/// the same rule resolution regardless of how many segments it spans.
#[test]
fn wi729_namespace_qualified_receiver_method_call() {
    const DATA: &str = r#"
namespace test.wi729ns.data
  import anthill.prelude.{String, Int64}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
end
"#;
    const USE: &str = r#"
namespace test.wi729ns.use
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}

  operation aliceRows() -> List[(name: String, age: Int64)] effects Error =
    let r = test.wi729ns.data.person_row.where(lambda c -> eq(c.name, "alice"))
    r.takeN(5)
end
"#;
    let kb = try_load_kb_with_files(&[DATA, USE]).unwrap_or_else(|errs| {
        panic!("a namespace-qualified rule-ref method call must load; got: {errs:?}")
    });
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register builtins");
    let r = interp
        .call("test.wi729ns.use.aliceRows", &[])
        .expect("aliceRows drains the where-filtered bare-qualified relation");
    assert_eq!(
        collect_named_rows(&r),
        vec![("alice".to_string(), 30)],
        "the multi-segment prefix names the relation; `where` filters it to alice"
    );
}

/// The row binder is typed at the CONCRETE schema through the multi-segment receiver
/// too — `c.name` is `String`, so comparing it to an `Int64` literal is a real
/// mismatch. (An unresolved-var binder would absorb the demand and pass, so this is
/// what distinguishes "re-routed to a dot call" from "accidentally type-checked".)
#[test]
fn wi729_row_binder_schema_is_concrete_through_qualified_receiver() {
    const SRC: &str = r#"
namespace test.wi729schema
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
    rule rows(?name, ?age) :- person(name: ?name, age: ?age)
  end
  fact person(name: "alice", age: 30)

  operation probe() -> Bool effects Error =
    let r = Person.rows.where(lambda c -> eq(c.name, 42))
    r.isEmpty
end
"#;
    match try_load_kb_with(SRC) {
        Ok(_) => panic!(
            "eq(c.name, 42) must be rejected — `Person.rows`' schema types c.name as String"
        ),
        Err(errs) => {
            let joined = errs.join("\n");
            assert!(
                joined.contains("String") && joined.contains("Int64"),
                "expected a String-vs-Int64 mismatch on c.name; got:\n{joined}",
            );
        }
    }
}

/// NO REGRESSION: the VALUE-receiver re-route still wins. A let-local binding shadows
/// a same-named rule, so `person_row.takeN(5)` dispatches on the LOCAL list value, not
/// on the relation — the local-binder probe runs before the rule probe.
#[test]
fn wi729_value_receiver_still_reroutes_first() {
    const SRC: &str = r#"
namespace test.wi729shadow
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  -- a 2-row relation; the local binding below shadows it with a 1-element list.
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation shadowed() -> Int64 effects Error =
    let person_row = cons(7, nil())
    person_row.size
end
"#;
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi729shadow.shadowed", &[])
        .expect("the shadowed receiver runs");
    match r {
        Value::Int(n) => assert_eq!(
            n, 1,
            "a local binder shadows the same-named rule — `person_row.size` is the LIST's size"
        ),
        other => panic!("expected the local list's size, got {other:?}"),
    }
}

/// NO SILENT FALLBACK: a receiver naming neither a local value nor a rule keeps the
/// qualified-name flattening and its loud unknown-functor diagnostic — the widened
/// probe must not turn a miss into a quietly-unbound dot-call receiver. Three misses,
/// each still naming the flattened path it failed to resolve:
///   - a real sort with no such member (`Queen.nosuch`),
///   - a receiver nothing in scope answers at all,
///   - a LOCAL value CHAIN (`p.inner.abs()`) — WI-443 defers chained-receiver
///     synthesis, and a local ROOT must not fall through to the rule probe either.
#[test]
fn wi729_unresolvable_receiver_stays_loud() {
    const NO_SUCH_MEMBER: &str = r#"
namespace test.wi729loud1
  import anthill.prelude.{Int64, List}
  sort Queen
    entity queen(row: Int64)
    rule find(?row) :- queen(row: ?row)
  end
  fact queen(row: 1)
  operation bad() -> List[Int64] effects Error =
    Queen.nosuch.takeN(5)
end
"#;
    const NOTHING_IN_SCOPE: &str = r#"
namespace test.wi729loud2
  import anthill.prelude.{Int64, List}
  operation bad() -> List[Int64] effects Error =
    nosuchns.nosuchrule.takeN(5)
end
"#;
    const LOCAL_CHAIN: &str = r#"
namespace test.wi729loud3
  import anthill.prelude.{Int64}
  sort Box
    entity box(inner: Int64)
  end
  operation bad() -> Int64 effects Error =
    let p = box(inner: 3)
    p.inner.abs()
end
"#;
    for (src, flattened) in [
        (NO_SUCH_MEMBER, "Queen.nosuch.takeN"),
        (NOTHING_IN_SCOPE, "nosuchns.nosuchrule.takeN"),
        (LOCAL_CHAIN, "p.inner.abs"),
    ] {
        let errs = try_load_kb_with(src).err().unwrap_or_default();
        assert!(
            errs.iter().any(|e| e.contains(flattened) && e.contains("unknown functor")),
            "`{flattened}` must stay the loud unknown-functor error, got: {errs:?}"
        );
    }
}

/// NO REGRESSION: a receiver that resolves to a SORT (not a rule) keeps the
/// qualified-name path — `Queen.find(2)` is still the APPLIED citation form, whose
/// argument BINDS the relation's sole column (→ a `Relation[Unit]` membership test),
/// not a method call `find` on a `Queen` relation. The `Goal`/`Rule` kind gate on the
/// receiver is what separates the two.
#[test]
fn wi729_sort_receiver_keeps_the_applied_qualified_path() {
    const SRC: &str = r#"
namespace test.wi729applied
  import anthill.prelude.{Int64, List, Bool}

  sort Queen
    entity queen(row: Int64)
    rule find(?row) :- queen(row: ?row)
  end
  fact queen(row: 1)
  fact queen(row: 2)

  operation rowTwoPresent() -> Bool effects Error =
    let r = Queen.find(2)
    r.isEmpty

  operation rowNinePresent() -> Bool effects Error =
    let r = Queen.find(9)
    r.isEmpty
end
"#;
    let mut interp = interp_for(SRC);
    let present = interp
        .call("test.wi729applied.rowTwoPresent", &[])
        .expect("the applied `Sort.rule(arg)` form runs");
    assert_eq!(
        present.as_bool(),
        Some(false),
        "`Queen.find(2)` still APPLIES the rule — binding row=2, which is a fact"
    );
    let absent = interp
        .call("test.wi729applied.rowNinePresent", &[])
        .expect("the applied form runs for an absent row");
    assert_eq!(
        absent.as_bool(),
        Some(true),
        "`Queen.find(9)` binds row=9, which no fact matches → empty"
    );
}

// ── list decoders (cons-cell walkers over the drained results) ──

fn collect_int_list(v: &Value) -> Vec<i64> {
    collect_list(v, |head| match head {
        Value::Int(n) => Some(*n),
        _ => None,
    })
}

fn collect_named_rows(v: &Value) -> Vec<(String, i64)> {
    collect_list(v, |head| match head {
        Value::Tuple { named, .. } => {
            let name = named.iter().find_map(|(_, v)| match v {
                Value::Str(s) => Some(s.clone()),
                _ => None,
            })?;
            let age = named.iter().find_map(|(_, v)| match v {
                Value::Int(n) => Some(*n),
                _ => None,
            })?;
            Some((name, age))
        }
        _ => None,
    })
}

/// Walk a `cons`/`nil` list `Value`, decoding each head with `decode`. Each cons cell
/// is an `Entity` whose named slots are the head and the tail (the tail is the only
/// `Entity`-valued slot), so the head is "the slot `decode` accepts".
fn collect_list<T>(v: &Value, decode: impl Fn(&Value) -> Option<T>) -> Vec<T> {
    let mut out = Vec::new();
    let mut cur = v.clone();
    while let Value::Entity { named, .. } = &cur {
        let Some(head) = named.iter().find_map(|(_, val)| decode(val)) else {
            break;
        };
        let Some(tail) = named.iter().find_map(|(_, val)| match val {
            Value::Entity { .. } => Some(val.clone()),
            _ => None,
        }) else {
            break;
        };
        out.push(head);
        cur = tail;
    }
    out
}
