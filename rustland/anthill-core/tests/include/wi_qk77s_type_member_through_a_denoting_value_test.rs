//! WI-20261024-QK77S — a type member reached through a value that denotes its sort is the
//! member the sort's name reaches (WI-20260824-PAPX0's rule, for a type member): under
//! `let dd = D`, `dd.T` is `D.T` in a type and as a value, and a parameter the bracket binds
//! is the type it binds — `pp.T` under `let pp = P[T = String]` is `String`.
//!
//! Each row runs the spelling through the value beside the written one: the annotation's
//! value is computed, the type value compared with `PartialEq.eq`, a refusal read for the
//! written twin's words.
//!
//! CONTROLS — measured, each piece backed out on its own in one build:
//!
//!   the value read (`written_sort_dot`'s type-member arm skipped, so the dot reaches the
//!   refusal it replaced) — FAIL:
//!     a_type_member_through_the_value_is_the_written_type_value
//!     a_bracket_binds_the_parameter_it_names
//!     a_positional_bracket_binds_the_next_parameter
//!     a_type_parameter_in_the_bracket_is_that_parameter
//!     an_alias_hop_keeps_the_denotation
//!     a_rule_body_reads_the_member_of_a_written_type
//!     a_parameter_left_open_is_refused_as_the_written_one
//!     a_parameter_the_bracket_leaves_open_is_the_written_one
//!     a_rewrite_reads_the_member_where_it_is_written
//!     a_type_member_is_no_call
//!     a_member_hidden_from_the_dot_is_hidden_from_both_positions (its value half)
//!     a_member_over_the_sorts_parameters_is_read_at_the_bracket (its value half)
//!   the type read (`read_denoted_projections` answering its input) — FAIL:
//!     a_type_member_through_the_value_annotates_as_the_written_one
//!     a_bracket_binds_the_parameter_it_names
//!     a_positional_bracket_binds_the_next_parameter
//!     a_type_parameter_in_the_bracket_is_that_parameter
//!     an_alias_hop_keeps_the_denotation
//!     a_lambda_binder_reads_the_member_too
//!     a_pattern_binder_reads_the_member_too
//!     a_parameter_left_open_is_refused_as_the_written_one
//!     a_parameter_the_bracket_leaves_open_is_the_written_one
//!     a_rewrite_reads_the_member_where_it_is_written
//!     a_member_the_sort_does_not_declare_is_refused_about_the_sort
//!     a_member_hidden_from_the_dot_is_hidden_from_both_positions (its type half)
//!     a_member_over_the_sorts_parameters_is_read_at_the_bracket
//!   the lambda site's read alone — FAIL: a_lambda_binder_reads_the_member_too
//!   the pattern site's read alone — FAIL: a_lambda_binder_reads_the_member_too,
//!     a_pattern_binder_reads_the_member_too
//!   the member read as the written name reads (`load::alias_read`) replaced by the bare
//!   sort reference — FAIL, the refusal no longer says `T (Int64)`:
//!     a_type_member_through_the_value_annotates_as_the_written_one
//!     a_lambda_binder_reads_the_member_too
//!   a definition that reads the sort's parameters told by its shape not being ground,
//!   which a slot left open with `?` is not either — FAIL:
//!     a_parameter_the_bracket_leaves_open_is_the_written_one (`qq.S`)
//!   the annotation's scope taken from the enclosing operation, not from where the text is
//!   written — FAIL: a_rewrite_reads_the_member_where_it_is_written
//!   the member's type value built as a rule body's own term builds an alias (`structural`
//!   off there) — FAIL: a_structural_member_is_the_type_it_stands_for (`(Tup).TT`)
//!   the loader's check admitting a nominal type value only — FAIL, a crash of the load:
//!     a_structural_member_is_the_type_it_stands_for (`Tup.TT` in the rule)
//!   the rule body's dot marked written without parentheses — FAIL:
//!     a_rule_body_reads_the_member_of_a_written_type
//!     (the rows of `wi_papx0_…`, `wi_r653s_…` and `wi_a3fy2_…` pass either way)
//!
//!
//!   Measured with the rows of the reading at a receiver's bindings and the alias, value and
//!   bracket readings beside them:
//!   a member's definition never read at the receiver's bindings (`member_at` answering its
//!   written name) — FAIL:
//!     a_member_over_the_sorts_parameters_is_read_at_the_bracket
//!     a_type_member_off_a_value_is_the_written_one
//!     an_alias_member_is_read_at_the_alias_parameters
//!     (and two rows of `wi_qk77s_dotted_type_in_a_data_slot_test`)
//!   a type member that is no parameter not projected off a value (`project_type_member`'s
//!   arm skipped) — FAIL: a_type_member_off_a_value_is_the_written_one
//!   the alias-prefix pass of the field ladder (`DotFieldPass::AliasPrefix` admitting
//!   nothing), and separately the sort rung taking a chain read through an alias that fixes
//!   parameters — FAIL, each: an_alias_member_is_read_at_the_alias_parameters
//!   a bracket entry rooted at a value read as a name (`try_value_rooted_entry` and the
//!   term walk's rung off), and separately a value's type member read as a value
//!   (`type_member_as_value` skipped) — FAIL, each:
//!     a_type_member_in_a_value_bracket_is_the_member
//!
//!   the refusal of an internal member projected off a value — FAIL:
//!     an_internal_member_off_a_value_is_refused
//!
//!   PASS EITHER WAY, by design: a_type_that_denotes_nothing_here_keeps_its_refusal — a
//!   parameter `t: Type` denotes no sort at the dot, so `t.T` is the `Type` value's
//!   member, which `Type` does not have. a_path_past_an_alias_member_is_read_by_its_name —
//!   the fence of the sort rung's alias test: a path past the alias's member keeps the name
//!   reading (measured also with the test asked through `dotted_alias_receiver`).

use anthill_core::eval::Value;

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, query_unary, run_int64};

/// The sorts the rows read members of: `D` fixes its members, `P` leaves it a parameter, `Q`
/// has a parameter and a member defined over it, `CA` and `CB` are aliases of `P`.
const DECLS: &str = "\
  sort P
    sort T = ?
    entity p(x: T)
  end
  sort Q
    sort A = ?
    sort B = ?
    sort L = List[T = A]
    sort LB = List[T = B]
    sort K = Int64
    sort S = List[T = ?]
    entity q(x: A, y: B)
  end
  sort D
    sort T = Int64
    sort Inner
      entity inn
    end
    entity d(x: T)
    const c: Int64 = 3
  end
  sort CA = P[T = String]
  sort CB = P
  sort CQ = Q[A = Int64]
  sort LI = List[T = Int64]
  operation idt(t: Type) -> Type = t
  operation bit(c: Bool) -> Int64 = if c then 1 else 0
";

/// A program in `qk77s.<ns>` with [`DECLS`] and `main` as the body of `main() -> Int64`.
fn program(ns: &str, main: &str) -> String {
    program_with(ns, "", main)
}

/// [`program`] with `decls` declared beside [`DECLS`].
fn program_with(ns: &str, decls: &str, main: &str) -> String {
    format!(
        "namespace qk77s.{ns}\n  import anthill.prelude.{{Int64, String, Bool, List, Type, \
         PartialEq}}\n  import anthill.reflect.{{TypeValue}}\n{DECLS}{decls}  operation main() -> \
         Int64 =\n    {main}\nend\n"
    )
}

fn run(ns: &str, main: &str) -> Result<i64, String> {
    run_int64(&program(ns, main), &format!("qk77s.{ns}.main"))
}

/// The refusals of `main`, which must not load.
fn refusals(ns: &str, main: &str) -> Vec<String> {
    let errs = load_errors_of(&program(ns, main));
    assert!(!errs.is_empty(), "{ns}: must be refused, and loaded clean");
    errs
}

/// The refusals' text with the namespace taken out, so two rows' refusals compare.
fn refusal_text(ns: &str, main: &str) -> Vec<String> {
    refusals(ns, main)
        .into_iter()
        .map(|e| {
            let mut e = e.replace(&format!("qk77s.{ns}"), "qk77s.NS");
            // A refusal located by a line and column names the line the row writes it on.
            while let Some((at, rest)) = e.split_once(": ") {
                if at.contains(' ') || !at.contains(|c: char| c.is_ascii_digit() || c == '.') {
                    break;
                }
                e = rest.to_string();
            }
            e
        })
        .collect()
}

// ── the rule ────────────────────────────────────────────────────────────────

/// The ticket's first row: `let y: dd.T = 5` is `let y: D.T = 5`, and the string is refused
/// in the written spelling's words. It was refused "type 'anthill.prelude.Type' has no
/// member 'T'": the projection read the value's type, `Type`.
#[test]
fn a_type_member_through_the_value_annotates_as_the_written_one() {
    assert_eq!(run("ann1", "let y: D.T = 5\n    y + 1"), Ok(6));
    assert_eq!(run("ann2", "let dd = D\n    let y: dd.T = 5\n    y + 1"), Ok(6));
    assert_eq!(
        run("ann3", "let dd = D\n    let ys: List[T = dd.T] = [5]\n    0"),
        Ok(0)
    );
    let written = refusal_text("ann4", "let y: D.T = \"s\"\n    0");
    let through = refusal_text("ann5", "let dd = D\n    let y: dd.T = \"s\"\n    0");
    assert_eq!(through, written);
    assert_refused_naming(&through, &["expected T (Int64), got String"], "dd.T");
}

/// The ticket's second row: the value `dd.T` is the type value `D.T` is, `Int64`. It was
/// refused "`T` is declared in `D` and is none of them".
#[test]
fn a_type_member_through_the_value_is_the_written_type_value() {
    assert_eq!(run("val1", "bit(PartialEq.eq(idt(D.T), Int64))"), Ok(1));
    assert_eq!(run("val2", "let dd = D\n    bit(PartialEq.eq(idt(dd.T), Int64))"), Ok(1));
    assert_eq!(run("val3", "let dd = D\n    bit(PartialEq.eq(dd.T, D.T))"), Ok(1));
    assert_eq!(run("val4", "let dd = D\n    bit(PartialEq.eq(dd.T, String))"), Ok(0));
    // A nested sort is a type member too.
    assert_eq!(run("val5", "let dd = D\n    bit(PartialEq.eq(dd.Inner, D.Inner))"), Ok(1));
}

/// `pp.T` under `let pp = P[T = String]` is `String`, in a type and as a value.
#[test]
fn a_bracket_binds_the_parameter_it_names() {
    assert_eq!(
        run("br1", "let pp = P[T = String]\n    let y: pp.T = \"s\"\n    0"),
        Ok(0)
    );
    assert_eq!(run("br2", "let pp = P[T = String]\n    bit(PartialEq.eq(pp.T, String))"), Ok(1));
    assert_refused_naming(
        &refusals("br3", "let pp = P[T = String]\n    let y: pp.T = 5\n    0"),
        &["y.annotation (let-binding): expected String, got Int64"],
        "pp.T is String",
    );
    // An alias that fixes the parameter, read as a value as the bracket it writes.
    assert_eq!(run("br4", "let c = CA\n    bit(PartialEq.eq(c.T, String))"), Ok(1));
    assert_refused_naming(
        &refusals("br5", "let c = CA\n    let y: c.T = 5\n    0"),
        &["expected String, got Int64"],
        "c.T is String",
    );
}

/// A positional bracket binds the next parameter, as in a type position.
#[test]
fn a_positional_bracket_binds_the_next_parameter() {
    assert_eq!(run("pos1", "let pp = P[String]\n    bit(PartialEq.eq(pp.T, String))"), Ok(1));
    assert_refused_naming(
        &refusals("pos2", "let pp = P[String]\n    let y: pp.T = 5\n    0"),
        &["expected String, got Int64"],
        "P[String]",
    );
}

/// One alias hop is read through, as a receiver path is (`let u = dd`).
#[test]
fn an_alias_hop_keeps_the_denotation() {
    assert_eq!(
        run("hop1", "let dd = D\n    let u = dd\n    let y: u.T = 5\n    y"),
        Ok(5)
    );
    assert_eq!(run("hop2", "let dd = D\n    let u = dd\n    bit(PartialEq.eq(u.T, Int64))"), Ok(1));
}

/// A type parameter of the enclosing operation in the bracket is that parameter: `pp.T` under
/// `let pp = P[T = X]` is `X`, in a type and as a value.
#[test]
fn a_type_parameter_in_the_bracket_is_that_parameter() {
    let decls = "  operation tv[X]() -> Type requires TypeValue[T = X] =\n    let pp = P[T = X]\n    \
                 pp.T\n  operation through[X](y: X) -> X requires TypeValue[T = X] =\n    let pp = \
                 P[T = X]\n    let z: pp.T = y\n    z\n";
    let main = "bit(PartialEq.eq(tv[X = Int64](), Int64)) + 2 * bit(PartialEq.eq(tv[X = \
                String](), Int64)) + 4 * through(5)";
    assert_eq!(
        run_int64(&program_with("tp1", decls, main), "qk77s.tp1.main"),
        Ok(1 + 4 * 5)
    );
}

/// A lambda's binder annotation reads the member as a `let`'s does. It was left the path
/// type `dd.T`, and `z + 1` refused "expected dd.T, got Int64".
#[test]
fn a_lambda_binder_reads_the_member_too() {
    assert_eq!(
        run("lam1", "let dd = D\n    let f = lambda (z: dd.T) -> z + 1\n    f(1)"),
        Ok(2)
    );
    let written = refusal_text("lam2", "let f = lambda (z: D.T) -> z\n    f(\"s\")");
    let through = refusal_text("lam3", "let dd = D\n    let f = lambda (z: dd.T) -> z\n    f(\"s\")");
    assert_eq!(through, written);
}

/// A rule body reads a written type's dot as an operation body does: `(D).T` is `D.T`. It
/// was refused as written with parentheses — the rule body's dot carried no mark that it
/// was written without them.
#[test]
fn a_rule_body_reads_the_member_of_a_written_type() {
    let rules = |ns: &str, rule: &str| {
        let main = program(ns, "0");
        let body = main.trim_end().strip_suffix("end").expect("the program ends its namespace");
        format!(
            "{body}  operation isInt(t: Type) -> Int64 = bit(PartialEq.eq(t, Int64))\n  {rule}\nend\n"
        )
    };
    for (ns, rhs) in [("rb1", "D.T"), ("rb2", "(D).T")] {
        let mut kb = load_kb_with(&rules(ns, &format!("rule r(?n) :- ?n <=> isInt({rhs})")));
        let answers = query_unary(&mut kb, &format!("qk77s.{ns}.r"));
        assert!(
            matches!(answers[..], [(Value::Int(1), true)]),
            "{ns}: {answers:?}"
        );
    }
    assert_refused_naming(
        &load_errors_of(&rules("rb3", "rule r(?t) :- ?t <=> idt((D).T())")),
        &["the type member written without parentheses, `D.T`"],
        "(D).T()",
    );
}

/// A member that is a structural alias — a tuple — is the type it stands for, through the
/// value as written, in an operation body and in a rule body. In a rule body the written
/// `D.TT` crashed the load (the loader's check that the walk built a type value admitted a
/// nominal one only), and `(D).TT` read the alias's name.
#[test]
fn a_structural_member_is_the_type_it_stands_for() {
    let decls = "  sort Tup\n    sort TT = (Int64, String)\n    entity tup\n  end\n  sort Pair2 = \
                 (Int64, String)\n  operation isTup(t: Type) -> Int64 = bit(PartialEq.eq(t, Pair2))\n  \
                 rule r(?n) :- ?n <=> isTup(Tup.TT) + 2 * isTup((Tup).TT)\n";
    let main = "let tt = Tup\n    isTup(Tup.TT) + 2 * isTup(tt.TT)";
    let src = program_with("st1", decls, main);
    assert_eq!(run_int64(&src, "qk77s.st1.main"), Ok(3));
    let mut kb = load_kb_with(&src);
    let answers = query_unary(&mut kb, "qk77s.st1.r");
    assert!(matches!(answers[..], [(Value::Int(3), true)]), "{answers:?}");
}

/// A binder's own annotation inside a pattern — a `match` case, a destructuring `let` —
/// reads the member too. It was compared as the path type `dd.T` and refused, "expected
/// Int64, got dd.T".
#[test]
fn a_pattern_binder_reads_the_member_too() {
    assert_eq!(
        run("pat1", "let dd = D\n    match 5\n      case (z: dd.T) -> z + 1"),
        Ok(6)
    );
    assert_eq!(
        run("pat2", "let dd = D\n    let (a: dd.T, b) = (1, 2)\n    a + b"),
        Ok(3)
    );
}

// ── the refusals ────────────────────────────────────────────────────────────

/// A parameter the receiver leaves open is refused as the written `P.T` is: in a type it is
/// not manifest, and as a value it reads the parameter, which needs `TypeValue`.
#[test]
fn a_parameter_left_open_is_refused_as_the_written_one() {
    let written = refusal_text("open1", "let y: P.T = 5\n    0");
    let through = refusal_text("open2", "let pp = P\n    let y: pp.T = 5\n    0");
    assert_refused_naming(&through, &["'P.T' is not manifest"], "pp.T in a type");
    // The annotation's refusal is the same. The written spelling has one more: the loader
    // records `P.T` where it lowers it, and the formation sweep refuses it there too
    // (`P.T (entity-field)`); `pp.T` is formed by the typer and has no such record.
    assert_eq!(
        through.iter().filter(|e| e.contains("annotation")).collect::<Vec<_>>(),
        written.iter().filter(|e| e.contains("annotation")).collect::<Vec<_>>(),
    );
    let written = refusal_text("open3", "let t = idt(P.T)\n    0");
    let through = refusal_text("open4", "let pp = P\n    let t = idt(pp.T)\n    0");
    assert_eq!(through, written);
    assert_refused_naming(&through, &["requires anthill.reflect.TypeValue[T = T]"], "pp.T");
}

/// A parameter a bracket leaves open is the written `Q.B` too, refused in its words: not
/// manifest in a type, a parameter read as a value. A member whose definition leaves a slot
/// open with `?` names no parameter, and reads through a bracket as written.
#[test]
fn a_parameter_the_bracket_leaves_open_is_the_written_one() {
    let written = refusal_text("ob1", "let t = idt(Q.B)\n    0");
    let through = refusal_text("ob2", "let qq = Q[A = Int64]\n    let t = idt(qq.B)\n    0");
    assert_eq!(through, written);
    assert_refused_naming(
        &refusals("ob3", "let qq = Q[A = Int64]\n    let y: qq.B = 5\n    0"),
        &["'Q.B' is not manifest"],
        "qq.B in a type",
    );
    assert_eq!(run("ob4", "let qq = Q[A = Int64]\n    let y: qq.S = [5]\n    0"), Ok(0));
    assert_eq!(run("ob5", "let y: Q.S = [5]\n    0"), Ok(0));
}

/// A rewrite's text is read where it is written: a `@[simp]` right-hand side inside `V`
/// reads `V`'s `internal` member through `vv`, in a type and as a value, wherever the rule
/// fires.
#[test]
fn a_rewrite_reads_the_member_where_it_is_written() {
    let src = "namespace lib.rw\n  import anthill.prelude.{Int64, String, Type}\n  sort V\n    \
               internal sort H = String\n    entity v\n    operation idt(t: Type) -> Type = t\n    \
               rule probeA() <=> (let vv = V\n      let y: vv.H = \"s\"\n      1) @[simp]\n    rule \
               probeB() <=> (let vv = V\n      let t = idt(vv.H)\n      2) @[simp]\n  end\nend\n\
               namespace qk77s.rw\n  import anthill.prelude.{Int64}\n  import lib.rw.{V}\n  \
               operation main() -> Int64 = V.probeA() + V.probeB()\nend\n";
    assert_eq!(run_int64(src, "qk77s.rw.main"), Ok(3));
}

/// A member `D` does not declare is refused about `D`, in a type and as a value; a constant
/// is declared and is none of what a dot on a sort reaches.
#[test]
fn a_member_the_sort_does_not_declare_is_refused_about_the_sort() {
    assert_refused_naming(
        &refusals("miss1", "let dd = D\n    let y: dd.Nope = 5\n    0"),
        &["type 'qk77s.miss1.D' has no member 'Nope'"],
        "dd.Nope in a type",
    );
    assert_refused_naming(
        &refusals("miss2", "let dd = D\n    let t = idt(dd.Nope)\n    0"),
        &["Nope"],
        "dd.Nope as a value",
    );
    assert_refused_naming(
        &refusals("miss3", "let dd = D\n    dd.c"),
        &["`c` is declared in `D` and is none of them"],
        "a constant",
    );
}

/// A type member is no call: `dd.T()` is refused, saying to write it without parentheses.
#[test]
fn a_type_member_is_no_call() {
    assert_refused_naming(
        &refusals("call1", "let dd = D\n    let t = idt(dd.T())\n    0"),
        &["the type member written without parentheses, `D.T`"],
        "dd.T()",
    );
}

/// An `internal` member is hidden from a dot written outside its sort in both positions, as
/// its written name is.
#[test]
fn a_member_hidden_from_the_dot_is_hidden_from_both_positions() {
    let src = |ns: &str, body: &str| {
        format!(
            "namespace lib.{ns}\n  sort V\n    internal sort H = String\n    entity v\n  end\nend\n\
             namespace qk77s.{ns}\n  import anthill.prelude.{{Int64, Type}}\n  import lib.{ns}.V\n  \
             operation idt(t: Type) -> Type = t\n  operation main() -> Int64 =\n    let vv = V\n    {body}\nend\n"
        )
    };
    for (ns, body) in [("hid1", "let y: vv.H = \"s\"\n    0"), ("hid2", "let t = idt(vv.H)\n    0")] {
        assert_refused_naming(
            &load_errors_of(&src(ns, body)),
            &[&format!("'H' is internal to 'lib.{ns}.V'")],
            ns,
        );
    }
}

/// A member defined over the sort's parameters (`L = List[T = A]`), reached through a
/// receiver that binds them, is its definition at them, as a field's type is: `qq.L` under
/// `let qq = Q[A = Int64]` is `List[T = Int64]`, in a type and as a value. One whose
/// definition names a parameter the receiver leaves open (`LB` over `B`) is refused. A member
/// that reads no parameter (`K = Int64`) is the member, bracket or not.
#[test]
fn a_member_over_the_sorts_parameters_is_read_at_the_bracket() {
    assert_eq!(
        run("atb1", "let qq = Q[A = Int64]\n    let y: qq.L = [5]\n    bit(PartialEq.eq(qq.L, LI))"),
        Ok(1)
    );
    assert_refused_naming(
        &refusals("atb2", "let qq = Q[A = Int64]\n    let y: qq.L = [\"s\"]\n    0"),
        &["expected Int64, got String"],
        "qq.L is List[T = Int64]",
    );
    for (ns, main) in [
        ("atb3", "let qq = Q[A = Int64]\n    let y: qq.LB = [5]\n    0"),
        ("atb4", "let qq = Q[A = Int64]\n    let t = idt(qq.LB)\n    0"),
    ] {
        assert_refused_naming(
            &refusals(ns, main),
            &["`LB` is defined over a parameter of `Q` the receiver leaves open"],
            ns,
        );
    }
    assert_eq!(
        run("atb5", "let qq = Q[A = Int64]\n    let y: qq.K = 5\n    y"),
        Ok(5)
    );
}

/// A type member off a VALUE is the member the written name is, at the parameters the
/// value's type binds: `let y: x.T = 5` over `x: D` is `let y: D.T = 5`, refused in its words
/// for a string; `x.L` over `x: Q[A = Int64]` is `List[T = Int64]`; a parameter the value's
/// type leaves open is the value's own (`x.LB` over `x: Q[A = Int64]` is `List[T = x.B]`). It
/// was refused, "type 'D' has no member 'T'": only a parameter was read off a value.
#[test]
fn a_type_member_off_a_value_is_the_written_one() {
    let decls = "  operation five(x: D) -> Int64 =\n    let y: x.T = 5\n    y\n  operation \
                 six(x: D, y: x.T) -> Int64 = y + 1\n  operation lst(x: Q[A = Int64]) -> Int64 =\n    \
                 let y: x.L = [5]\n    0\n";
    assert_eq!(
        run_int64(
            &program_with("ov1", decls, "five(d(x: 1)) + six(d(x: 1), 5) + lst(q(x: 1, y: \"s\"))"),
            "qk77s.ov1.main"
        ),
        Ok(11)
    );
    let written = refusal_text("ov2", "let y: D.T = \"s\"\n    0");
    let off_value = load_errors_of(&program_with(
        "ov3",
        "  operation bad(x: D) -> Int64 =\n    let y: x.T = \"s\"\n    0\n",
        "0",
    ));
    assert_refused_naming(&off_value, &[&written[0]], "x.T over x: D");
    assert_refused_naming(
        &load_errors_of(&program_with(
            "ov4",
            "  operation bad(x: Q[A = Int64]) -> Int64 =\n    let y: x.LB = [5]\n    0\n",
            "0",
        )),
        &["expected x.B, got Int64"],
        "x.LB is List[T = x.B]",
    );
}

/// A member through an alias that fixes parameters is read at them, in an operation body:
/// `CA.T` is `String`, `CQ.L` is `List[T = Int64]`, `CQ.K` is `Int64` — as a dot on the alias
/// written as a type value reads them. Through an alias that fixes none (`CB = P`), `CB.T` is
/// the written `P.T`. `CA.T` was refused, "T.name: expected resolved name"; `CQ.L` was the
/// member's name, `L`, which nothing equals.
#[test]
fn an_alias_member_is_read_at_the_alias_parameters() {
    assert_eq!(
        run(
            "al1",
            "bit(PartialEq.eq(CA.T, String)) + 2 * bit(PartialEq.eq(CQ.L, LI)) + 4 * \
             bit(PartialEq.eq(CQ.K, Int64))"
        ),
        Ok(7)
    );
    let written = refusal_text("al2", "let t = idt(P.T)\n    0");
    let through = refusal_text("al3", "let t = idt(CB.T)\n    0");
    assert_eq!(through, written);
}

/// A path past a member of the alias's sort (`CQ.Inner.X`) is the sort's nested member, read
/// by its name as before: only a member of the alias itself is read at its parameters.
#[test]
fn a_path_past_an_alias_member_is_read_by_its_name() {
    let decls = "  sort Q3\n    sort A = ?\n    sort Inner\n      sort X = Int64\n      entity inn\n    \
                 end\n    entity q3(x: A)\n  end\n  sort CQ3 = Q3[A = Int64]\n";
    let main = "bit(PartialEq.eq(CQ3.Inner.X, Int64)) + 2 * bit(PartialEq.eq(CQ3.Inner, Q3.Inner))";
    assert_eq!(run_int64(&program_with("pa1", decls, main), "qk77s.pa1.main"), Ok(3));
}

/// An `internal` type member projected off a value is refused: a projection carries no scope
/// to ask its visibility from. (Inside the declaring sort too, where the written name is
/// visible — the projection's limit, which the written name does not have.)
#[test]
fn an_internal_member_off_a_value_is_refused() {
    let src = "namespace lib.ivm\n  import anthill.prelude.{String}\n  sort V\n    internal sort H \
               = String\n    entity v\n  end\nend\nnamespace qk77s.ivm\n  import anthill.prelude.{Int64}\n  \
               import lib.ivm.V\n  operation bad(x: V) -> Int64 =\n    let y: x.H = \"s\"\n    0\nend\n";
    assert_refused_naming(
        &load_errors_of(src),
        &["'H' is internal to 'lib.ivm.V', and a projection off a value does not read an internal member"],
        "x.H",
    );
}

/// A bracket's entry written as a dot on a value is that value's member: `List[T = dd.T]`
/// under `let dd = D`, `List[T = x.T]` over `x: P[T = Int64]` and `List[pp.T]` under `let pp
/// = P[T = Int64]` are `List[T = Int64]`. Each was refused, "unresolved name 'dd.T'": the
/// entry is lowered as a type, one dotted name. A value's type member read as a value is the
/// type it is where the value's type determines it, and refused where it leaves it open.
#[test]
fn a_type_member_in_a_value_bracket_is_the_member() {
    let decls = "  operation viaParam(x: P[T = Int64]) -> Int64 = bit(PartialEq.eq(List[T = x.T], \
                 LI)) + 2 * bit(PartialEq.eq(x.T, Int64))\n";
    let main = "let dd = D\n    let pp = P[T = Int64]\n    bit(PartialEq.eq(List[T = dd.T], LI)) + 2 * \
                bit(PartialEq.eq(List[pp.T], LI)) + 4 * viaParam(p(x: 1))";
    assert_eq!(
        run_int64(&program_with("vb1", decls, main), "qk77s.vb1.main"),
        Ok(1 + 2 + 4 * 3)
    );
    for (ns, decls, token) in [
        ("vb2", "  operation g(x: P) -> Type = x.T\n", "the receiver's type leaves it open here"),
        (
            "vb3",
            "  operation g(x: P[T = Int64]) -> Type = x.T()\n",
            "the type member written without parentheses, `.T`",
        ),
    ] {
        assert_refused_naming(&load_errors_of(&program_with(ns, decls, "0")), &[token], ns);
    }
}

/// The boundary: a parameter `t: Type` denotes no sort at the dot, so `t.T` is the member of
/// the `Type` value, which `Type` does not have — in a type and as a value.
#[test]
fn a_type_that_denotes_nothing_here_keeps_its_refusal() {
    let src = |ns: &str, body: &str| {
        format!(
            "namespace qk77s.{ns}\n  import anthill.prelude.{{Int64, String, Bool, List, Type, \
             PartialEq}}\n{DECLS}  {body}\nend\n"
        )
    };
    assert_refused_naming(
        &load_errors_of(&src("par1", "operation k(t: Type) -> Type = t.T")),
        &["anthill.prelude.Type.T", "no such member"],
        "t.T as a value",
    );
    assert_refused_naming(
        &load_errors_of(&src(
            "par2",
            "operation k(t: Type) -> Int64 =\n    let y: t.T = 5\n    0",
        )),
        &["type 'anthill.prelude.Type' has no member 'T'"],
        "t.T in a type",
    );
}
