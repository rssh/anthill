//! WI-1127 (proposal 052) — the PARAMETER channel of a `where` / `join` row condition.
//!
//! A row-lambda condition is compiled AS SYNTAX at load time, so an operand that is
//! neither a column nor a literal has no value yet for the macro to fold — `eq(c.age, v)`
//! for a `let`-bound `v`, or `eq(c.age, thirty())`, used to be a LOAD error. But such an
//! operand is ROW-INDEPENDENT: one value for the whole restriction, exactly what `fix`
//! has always taken as an ordinary argument. So `compile_operand` now leaves a second
//! kind of HOLE — a PARAMETER — and hands the EXPRESSION to the runner as a captured
//! argument (`...params: P`, proposal 056), evaluated once in the CALLER's scope;
//! `where_run` / `join_run` fill it by the same interned-`Symbol` match a column hole
//! takes. A row-DEPENDENT operand (`bump(c.age)`) stays a loud rejection: there is no
//! single value to capture.
//!
//! One compiler serves both constructs (`compile_condition` is reached from `guarded_of`
//! → `where_run` AND `conjoin_of` → `join_run`), so every arm here is measured on BOTH.
//!
//! MEASURED BACK-OUT (`compile_operand`'s parameter arm restored to the literal-only
//! `macro_rejects`): 2 passed, 10 failed — the two literal controls pass, every other
//! test fails. The non-literal arms stop LOADING; the two rejection tests stop matching
//! because the refusal they assert is the row-DEPENDENT one this change introduced (the
//! old one refused every non-literal alike). The literal controls pass either way BY
//! DESIGN, and they live in their OWN knowledge base for exactly that reason: sharing one
//! namespace with the captured arms made a single load error fail all of them at once,
//! which cannot tell "the change is out" from "the fixture is broken".

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::{Interpreter, Value};

/// THE CONTROL FIXTURE, in its OWN knowledge base: only the literal spellings, so it
/// loads and answers whether or not the parameter channel exists. Every expectation in
/// this file is stated against these rows.
const LITERAL_SRC: &str = r#"
namespace test.wi1127lit
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where, join}
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.Bool.{and}

  sort Person
    entity person(name: String, age: Int64, rank: Int64)
  end
  fact person(name: "alice", age: 30, rank: 1)
  fact person(name: "bob", age: 25, rank: 2)
  fact person(name: "carol", age: 30, rank: 2)

  sort Membership
    entity member(who: String, dept: String)
  end
  fact member(who: "alice", dept: "eng")
  fact member(who: "bob", dept: "eng")
  fact member(who: "carol", dept: "sales")

  rule person_row(?name, ?age, ?rank) :- person(name: ?name, age: ?age, rank: ?rank)
  rule member_row(?who, ?dept) :- member(who: ?who, dept: ?dept)

  -- the age-30 rows (alice, carol)
  operation whereLiteral() -> List[(name: String, age: Int64, rank: Int64)] effects Error =
    person_row.where(lambda c -> eq(c.age, 30)).takeN(9)

  -- the joined rows whose dept is "eng" (alice, bob)
  operation joinLiteral()
    -> List[(name: String, age: Int64, rank: Int64, who: String, dept: String)] effects Error =
    person_row.join(member_row, lambda (c, q) -> and(eq(c.name, q.who), eq(q.dept, "eng"))).takeN(9)
end
"#;

/// The CAPTURED spellings — every operand here is a `let` binding, an operation result
/// or the enclosing operation's parameter, so the whole namespace fails to load without
/// the parameter channel.
const SRC: &str = r#"
namespace test.wi1127
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where, join}
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.Bool.{and}
  import anthill.prelude.List.{nil}

  sort Person
    entity person(name: String, age: Int64, rank: Int64)
  end
  fact person(name: "alice", age: 30, rank: 1)
  fact person(name: "bob", age: 25, rank: 2)
  fact person(name: "carol", age: 30, rank: 2)

  sort Membership
    entity member(who: String, dept: String)
  end
  fact member(who: "alice", dept: "eng")
  fact member(who: "bob", dept: "eng")
  fact member(who: "carol", dept: "sales")

  rule person_row(?name, ?age, ?rank) :- person(name: ?name, age: ?age, rank: ?rank)
  rule member_row(?who, ?dept) :- member(who: ?who, dept: ?dept)

  operation thirty() -> Int64 = 30
  operation eng() -> String = "eng"

  -- ── where ──────────────────────────────────────────────────
  operation whereLetBound() -> List[(name: String, age: Int64, rank: Int64)] effects Error =
    let target = 30
    person_row.where(lambda c -> eq(c.age, target)).takeN(9)

  operation whereComputed() -> List[(name: String, age: Int64, rank: Int64)] effects Error =
    person_row.where(lambda c -> eq(c.age, thirty())).takeN(9)

  -- A RUNTIME parameter: unknown until the call, so no compile-time fold could serve it.
  operation whereAt(target: Int64) -> List[(name: String, age: Int64, rank: Int64)] effects Error =
    person_row.where(lambda c -> eq(c.age, target)).takeN(9)

  -- TWO parameters of the SAME type on DIFFERENT columns, under an `and` spine: the
  -- holes must pair with their own operands, and the spine must carry the capture
  -- through the recursion.
  operation whereTwo(a: Int64, b: Int64) -> List[(name: String, age: Int64, rank: Int64)] effects Error =
    person_row.where(lambda c -> and(eq(c.age, a), eq(c.rank, b))).takeN(9)

  -- ── join ───────────────────────────────────────────────────
  operation joinLetBound()
    -> List[(name: String, age: Int64, rank: Int64, who: String, dept: String)] effects Error =
    let d = "eng"
    person_row.join(member_row, lambda (c, q) -> and(eq(c.name, q.who), eq(q.dept, d))).takeN(9)

  operation joinComputed()
    -> List[(name: String, age: Int64, rank: Int64, who: String, dept: String)] effects Error =
    person_row.join(member_row, lambda (c, q) -> and(eq(c.name, q.who), eq(q.dept, eng()))).takeN(9)

  operation joinAt(d: String)
    -> List[(name: String, age: Int64, rank: Int64, who: String, dept: String)] effects Error =
    person_row.join(member_row, lambda (c, q) -> and(eq(c.name, q.who), eq(q.dept, d))).takeN(9)
end
"#;

/// Each drained row's columns joined by `/`, in schema order, sorted. Same shape the
/// WI-730 condition tests read rows with: walk the `List` cons spine, each element the
/// row's named tuple.
fn rows(kb: &anthill_core::kb::KnowledgeBase, v: &Value) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = v.clone();
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break; // nil
        }
        let mut head: Option<Value> = None;
        let mut tail: Option<Value> = None;
        for (_k, x) in named.iter() {
            match x {
                Value::Tuple { .. } => head = Some(x.clone()),
                Value::Entity { .. } => tail = Some(x.clone()),
                _ => {}
            }
        }
        match (head, tail) {
            (Some(Value::Tuple { named: fields, .. }), Some(t)) => {
                out.push(
                    fields
                        .iter()
                        // WI-20260827-3ZNBC: a column is the bound value ON ITS OWN
                        // CARRIER, so read what it DENOTES rather than which `Value`
                        // variant carries it — the same `String`/`Int64` a native
                        // column held also arrives hash-consed or as an occurrence.
                        .map(|(_, x)| {
                            crate::common::scalar_display(kb, x)
                                .unwrap_or_else(|| panic!("unexpected column value {x:?}"))
                        })
                        .collect::<Vec<_>>()
                        .join("/"),
                );
                cur = t;
            }
            _ => break,
        }
    }
    out.sort();
    out
}

fn drain(interp: &mut Interpreter, ns: &str, op: &str, args: &[Value]) -> Vec<String> {
    let v = interp
        .call(&format!("{ns}.{op}"), args)
        .unwrap_or_else(|e| panic!("{op} runs the filtered relation: {e:?}"));
    rows(interp.kb(), &v)
}

/// The control answer, from the control KB — the rows the LITERAL spelling selects.
fn literal_rows(op: &str) -> Vec<String> {
    let mut interp = interp_for(LITERAL_SRC);
    drain(&mut interp, "test.wi1127lit", op, &[])
}

/// A captured-spelling answer, from the parameter KB.
fn param_rows(interp: &mut Interpreter, op: &str, args: &[Value]) -> Vec<String> {
    drain(interp, "test.wi1127", op, args)
}

/// THE CONTROL. The literal operand still folds into the recipe — it takes no parameter
/// slot — and selects the two age-30 rows. Every assertion below is stated against THIS
/// answer, so a fixture that had stopped selecting anything could not be mistaken for a
/// parameter arm that works.
#[test]
fn wi1127_literal_operand_still_folds() {
    assert_eq!(
        literal_rows("whereLiteral"),
        vec!["alice/30/1".to_string(), "carol/30/2".to_string()]
    );
}

/// A `let`-bound value as a `where` operand — the spelling the ticket measured as a LOAD
/// error — selects exactly the rows the literal spelling does.
#[test]
fn wi1127_where_operand_may_be_a_let_bound_value() {
    let mut interp = interp_for(SRC);
    assert_eq!(
        param_rows(&mut interp, "whereLetBound", &[]),
        literal_rows("whereLiteral")
    );
}

/// An operation RESULT as a `where` operand — the second spelling the ticket measured.
#[test]
fn wi1127_where_operand_may_be_an_operation_result() {
    let mut interp = interp_for(SRC);
    assert_eq!(
        param_rows(&mut interp, "whereComputed", &[]),
        literal_rows("whereLiteral")
    );
}

/// A RUNTIME parameter: ONE call site, two different filters. This is the arm no
/// compile-time constant folding could ever serve — the operand's value does not exist
/// until the call — so it is what pins the capture as a genuine runtime channel rather
/// than a cleverer fold.
#[test]
fn wi1127_where_operand_may_be_a_runtime_parameter() {
    let mut interp = interp_for(SRC);
    assert_eq!(
        param_rows(&mut interp, "whereAt", &[Value::Int(30)]),
        literal_rows("whereLiteral")
    );
    assert_eq!(
        param_rows(&mut interp, "whereAt", &[Value::Int(25)]),
        vec!["bob/25/2".to_string()]
    );
}

/// TWO parameters, same type, different columns, under an `and` spine. Each hole must
/// carry ITS OWN operand: `(30, 2)` selects carol and `(30, 1)` selects alice, so a pair
/// of holes filled in the wrong order — or from one shared slot — gives a different
/// answer rather than a type error. Also drives the capture through
/// `compile_condition`'s connective recursion, not just a bare atom.
#[test]
fn wi1127_where_two_parameters_pair_with_their_own_holes() {
    let mut interp = interp_for(SRC);
    assert_eq!(
        param_rows(&mut interp, "whereTwo", &[Value::Int(30), Value::Int(2)]),
        vec!["carol/30/2".to_string()]
    );
    assert_eq!(
        param_rows(&mut interp, "whereTwo", &[Value::Int(30), Value::Int(1)]),
        vec!["alice/30/1".to_string()]
    );
    // And the pair really does constrain: no row is (age 25, rank 1).
    assert!(param_rows(&mut interp, "whereTwo", &[Value::Int(25), Value::Int(1)]).is_empty());
}

/// `join`'s CONTROL — the literal `"eng"` in a two-row condition keeps alice and bob.
#[test]
fn wi1127_join_literal_operand_still_folds() {
    assert_eq!(
        literal_rows("joinLiteral"),
        vec![
            "alice/30/1/alice/eng".to_string(),
            "bob/25/2/bob/eng".to_string()
        ]
    );
}

/// The SAME two spellings on the OTHER caller of the shared operand compiler
/// (`conjoin_of` → `join_run`). The ticket's census: the restriction bound `where` and
/// `join` alike, so the lift must be measured on both — a fix threaded through
/// `guarded_of` alone would leave this half failing to load.
#[test]
fn wi1127_join_operand_may_be_let_bound_or_computed() {
    let mut interp = interp_for(SRC);
    let literal = literal_rows("joinLiteral");
    assert_eq!(param_rows(&mut interp, "joinLetBound", &[]), literal);
    assert_eq!(param_rows(&mut interp, "joinComputed", &[]), literal);
}

/// A RUNTIME parameter in a `join` condition — the join-side peer of the control above,
/// selecting a different row set per call.
#[test]
fn wi1127_join_operand_may_be_a_runtime_parameter() {
    let mut interp = interp_for(SRC);
    assert_eq!(
        param_rows(&mut interp, "joinAt", &[Value::Str("eng".into())]),
        literal_rows("joinLiteral")
    );
    assert_eq!(
        param_rows(&mut interp, "joinAt", &[Value::Str("sales".into())]),
        vec!["carol/30/2/carol/sales".to_string()]
    );
}

/// A ROW-DEPENDENT operand stays a LOUD rejection: `bump(c.age)` has no single value to
/// capture — it would have to be computed per row, which a query goal does not do.
///
/// The CONTROL is in the same source and the same shape: `bump(30)` is the identical
/// call with a row-independent argument, and it LOADS and filters. So this measures the
/// row-DEPENDENCE, not "a call in operand position is refused" — without it the
/// rejection would also be satisfied by a compiler that still refused every non-literal.
#[test]
fn wi1127_row_dependent_operand_is_a_loud_rejection() {
    const ROW_DEP: &str = r#"
namespace test.wi1127dep
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64, rank: Int64)
  end
  fact person(name: "alice", age: 30, rank: 30)
  rule person_row(?name, ?age, ?rank) :- person(name: ?name, age: ?age, rank: ?rank)
  operation bump(n: Int64) -> Int64 = n
  operation bad() -> List[(name: String, age: Int64, rank: Int64)] effects Error =
    person_row.where(lambda c -> eq(c.rank, bump(c.age))).takeN(9)
end
"#;
    const CONTROL: &str = r#"
namespace test.wi1127ok
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64, rank: Int64)
  end
  fact person(name: "alice", age: 30, rank: 30)
  rule person_row(?name, ?age, ?rank) :- person(name: ?name, age: ?age, rank: ?rank)
  operation bump(n: Int64) -> Int64 = n
  operation good() -> List[(name: String, age: Int64, rank: Int64)] effects Error =
    person_row.where(lambda c -> eq(c.rank, bump(30))).takeN(9)
end
"#;
    // CONTROL: the same call shape with a row-INDEPENDENT argument is captured and runs.
    let mut interp = interp_for(CONTROL);
    let got = interp
        .call("test.wi1127ok.good", &[])
        .expect("a call whose argument does not read the row is a capturable parameter");
    assert_eq!(rows(interp.kb(), &got), vec!["alice/30/30".to_string()]);

    let errs = match try_load_kb_with(ROW_DEP) {
        Err(e) => e,
        Ok(_) => panic!(
            "a row-DEPENDENT operand must not load: there is no single value to capture, \
             and a query goal does not evaluate an expression per row"
        ),
    };
    let joined = errs.join("\n");
    assert!(
        joined.contains("guarded_of") && joined.contains("row-INDEPENDENT operand"),
        "the rejection must name the macro and the reason; got: {joined}"
    );
}

/// The row-dependent rejection on the OTHER caller of the shared compiler — `join`'s
/// two-row lambda, where the operand reads the SECOND binder. The compiler is one, but
/// "one compiler" is a claim about the code; this measures it.
#[test]
fn wi1127_join_row_dependent_operand_is_a_loud_rejection() {
    const SRC_DEP: &str = r#"
namespace test.wi1127joindep
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{join}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  sort Membership
    entity member(who: String, rank: Int64)
  end
  fact person(name: "alice", age: 30)
  fact member(who: "alice", rank: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  rule member_row(?who, ?rank) :- member(who: ?who, rank: ?rank)
  operation bump(n: Int64) -> Int64 = n
  operation bad() -> List[(name: String, age: Int64, who: String, rank: Int64)] effects Error =
    person_row.join(member_row, lambda (c, q) -> eq(c.age, bump(q.rank))).takeN(9)
end
"#;
    let errs = match try_load_kb_with(SRC_DEP) {
        Err(e) => e,
        Ok(_) => panic!("a join operand reading the second row binder must not load"),
    };
    let joined = errs.join("\n");
    assert!(
        joined.contains("conjoin_of") && joined.contains("row-INDEPENDENT operand"),
        "the rejection must name `join`'s macro and the reason; got: {joined}"
    );
}

/// A BIGINT literal — the one `Literal` kind `compile_operand` does not fold. It used to
/// be refused outright ("an unsupported literal kind"); it now takes the parameter
/// channel, where it is evaluated as an ordinary `Expr::Const` like any other captured
/// expression. So the four folded kinds are an OPTIMIZATION (no runtime argument), not
/// the admissible set — and this is the arm that proves the fallthrough is live rather
/// than dead code.
///
/// CONTROL: the same relation filtered on the i64 column by a plain literal, so a load
/// failure here cannot be read as "BigInt columns do not work at all".
#[test]
fn wi1127_bigint_literal_takes_the_parameter_channel() {
    const BIG: &str = r#"
namespace test.wi1127big
  import anthill.prelude.{String, Int64, BigInt, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  sort Acct
    entity acct(name: String, balance: BigInt, rank: Int64)
  end
  fact acct(name: "alice", balance: 99999999999999999999, rank: 1)
  fact acct(name: "bob", balance: 88888888888888888888, rank: 2)
  rule acct_row(?name, ?balance, ?rank) :- acct(name: ?name, balance: ?balance, rank: ?rank)
  operation big() -> List[(name: String, balance: BigInt, rank: Int64)] effects Error =
    acct_row.where(lambda c -> eq(c.balance, 99999999999999999999)).takeN(9)
  operation control() -> List[(name: String, balance: BigInt, rank: Int64)] effects Error =
    acct_row.where(lambda c -> eq(c.rank, 1)).takeN(9)
end
"#;
    let mut interp = interp_for(BIG);
    let control = drain(&mut interp, "test.wi1127big", "control", &[]);
    assert_eq!(control.len(), 1, "the control selects alice's row: {control:?}");
    assert_eq!(
        drain(&mut interp, "test.wi1127big", "big", &[]),
        control,
        "the BigInt literal must select the same single row the i64 control does"
    );
}

/// BINDER MATCHING IS SYMBOL-EXACT, NOT BY NAME — the precision of the row-dependence
/// test, in both directions, driven with a nested lambda in operand position.
///
/// `apply1(lambda c -> c, 30)` SHADOWS the row binder's spelling: the inner `c` is a
/// different binding and reads nothing of the row, so the operand is row-independent and
/// must be CAPTURED. `apply1(lambda z -> c.age, 1)` reads the row from inside the nested
/// lambda's body, and must be REJECTED — so the walk descends into a lambda body rather
/// than stopping at the operand's top node.
///
/// Both arms are needed: matching by NAME would refuse the first, and stopping at the top
/// node would admit the second and compile a per-row read into a goal that means nothing.
#[test]
fn wi1127_binder_matching_is_symbol_exact_and_descends() {
    const SHADOW: &str = r#"
namespace test.wi1127shadow
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation apply1(f: (x: Int64) -> Int64, v: Int64) -> Int64 = f(v)
  operation shadowed() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> eq(c.age, apply1(lambda c -> c, 30))).takeN(9)
end
"#;
    const NESTED_ROW_READ: &str = r#"
namespace test.wi1127nested
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation apply1(f: (x: Int64) -> Int64, v: Int64) -> Int64 = f(v)
  operation bad() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> eq(c.age, apply1(lambda z -> c.age, 1))).takeN(9)
end
"#;
    let mut interp = interp_for(SHADOW);
    assert_eq!(
        drain(&mut interp, "test.wi1127shadow", "shadowed", &[]),
        vec!["alice/30".to_string()],
        "an inner binder that merely reuses the row binder's SPELLING is a different \
         symbol — the operand reads no row and must be captured"
    );

    let errs = match try_load_kb_with(NESTED_ROW_READ) {
        Err(e) => e,
        Ok(_) => panic!(
            "a row read from inside a NESTED lambda body must not load — the walk has to \
             descend, or a per-row read compiles into a goal that cannot mean it"
        ),
    };
    let joined = errs.join("\n");
    assert!(
        joined.contains("row-INDEPENDENT operand"),
        "the nested row read must be refused by the operand compiler; got: {joined}"
    );
}
