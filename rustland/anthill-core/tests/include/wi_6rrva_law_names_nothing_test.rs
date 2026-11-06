//! WI-20260825-6RRVA — AN EQUATIONAL LAW'S RIGHT-HAND SIDE, AND A DOTTED NAME ANYWHERE IN
//! A HEAD, NAMED NOTHING SILENTLY.
//!
//! WI-1034 refuses a rule-body goal that names nothing, WI-1058 a rule-body data slot, and
//! WI-20260904-B8ESG a head argument. Two shapes in a head stayed out of every one of them:
//!
//! ```text
//!   rule r: f(?a) <=> Bogus.nope(?a)        -- the REPLACEMENT: exempt as a whole
//!   rule r: vec_scale(Ring.one, ?v) <=> ?v  -- a PAREN-LESS DOTTED name: a minted
//!                                              `field_access` chain, which the compound
//!                                              check's provenance gate passes over
//! ```
//!
//! Both loaded clean, and that is how `anthill.prelude.algebra.VectorSpace`'s scalar-side
//! laws went on writing `Ring.sub(Ring.zero, Ring.one)` / `Ring.one` / `Ring.mul(?c, ?d)` /
//! `Ring.add(?c, ?d)` after WI-20260825-1WBZT moved those operations off `Ring`: five
//! addresses that named nothing, in a stdlib that loaded. Untagged, a law is read only by
//! the proof layers, so the load was the one place left to say so.
//!
//! ## THE CENSUS, taken before the check was turned on
//!
//! Zero sites in the stdlib (104 equation heads) and in the five examples. In the suites,
//! five fixtures: one real typo (`anthill.realization.Pending` for
//! `ObligationStatus.Pending`, in `wi_s8cyd_record_names_test`), two names the fixtures
//! never declared (`dbl` in `wi_n20ez_…`, `bar` in `equational_attr_test`, now declared),
//! a guarded `bar(?a) = bar(?a) :- …` in `wi627_…` that repeats its own subject, and one
//! shape that is not a path at all — `vv.H` over a `let vv = V` in a `@[simp]`
//! right-hand side, which is what the binding gate below is for. `/code-review` then found
//! five more shapes the first cut refused or let through; each has a row below.
//!
//! ## WHICH ROWS MOVE
//!
//! Each part of the change was backed out on its own, MEASURED over this file and the
//! suites it touches (114 rows; each row's name below without this file's prefix):
//!
//! | backed out | fails |
//! |---|---|
//! | the REPLACEMENT arm of `ClauseHead::judged_position` (the replacement exempt again) | `a_replacement_that_names_nothing_is_refused`, `the_scalar_side_laws_dead_addresses_are_each_refused`, `a_chain_is_named_once_where_it_fails`, `a_name_read_through_a_requirement_is_not_judged`, `a_call_through_a_parameter_names_nothing` |
//! | the DOTTED check (`Loader::judge_head_dotted_name` returning at once) | `the_scalar_side_laws_dead_addresses_are_each_refused`, `a_chain_is_named_once_where_it_fails`, `a_dotted_name_in_a_fact_head_is_judged`, `a_hidden_member_is_refused_as_the_access_it_is`, `a_name_read_through_a_requirement_is_not_judged` |
//! | its PREFIX gate | `a_chain_is_named_once_where_it_fails` (two refusals for one chain) |
//! | its BINDING gate | `a_projection_is_not_a_path`, `wi_qk77s_…::a_rewrite_reads_the_member_where_it_is_written` |
//! | its VALUE-PREFIX gate | `a_projection_is_not_a_path` |
//! | its HIDDEN-member refusal | `a_hidden_member_is_refused_as_the_access_it_is` |
//! | the REQUIREMENT-NAME reading, in both checks | `a_name_read_through_a_requirement_is_not_judged` |
//! | the DOTTED-SUBJECT span | `a_dotted_subject_is_one_name` |
//! | the REPEATED-SUBJECT exemption | `the_subject_repeated_in_its_replacement_is_not_judged`, and `wi627_…`'s three rows |
//! | the discrimination-tree BACKSTOP for a paren-less name | `a_dotted_name_a_fact_declares_is_declared` |
//!
//! `the_live_and_the_provided_addresses_load`, `the_names_that_resolve_run`,
//! `what_a_head_introduces_is_not_judged` and
//! `a_dotted_name_that_resolves_reaches_the_check_and_loads` pass under every one of
//! these, by design: they are the controls that say the refusals are about the NAME and not
//! the shape. A check that refused EVERY dotted name fails the last of them — and 101 rows
//! more, the stdlib's own `VectorSpace` laws first.

use crate::common::{assert_refused_naming, try_load_kb_with};

/// The rendered refusals of `src`, empty on a clean load.
fn refusals(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// The refusals of `src` that are this check's, in either of its two sentences.
fn names_nothing(src: &str) -> Vec<String> {
    refusals(src)
        .into_iter()
        .filter(|e| e.contains("names nothing"))
        .collect()
}

/// `VectorSpace`'s two scalar-side laws with the given spellings: `vec_sub_def`'s
/// replacement reads `$scalar`, and `vec_scale_identity`'s subject argument `$one`.
fn vector_space(ns: &str, scalar: &str, one: &str) -> String {
    format!(
        r#"
namespace test.wi6rrva.{ns}
  import anthill.prelude.{{Float, Additive, Multiplicative}}
  import anthill.prelude.algebra.{{Ring}}
  sort Vs
    sort V = ?
    sort F = ?
    requires Ring[F]
    operation {{
      vec_add(a: V, b: V) -> V
      vec_sub(a: V, b: V) -> V
      vec_scale(c: F, v: V) -> V
    }}
    rule {{
      vec_sub_def:        vec_sub(?a, ?b) <=> vec_add(?a, vec_scale({scalar}, ?b))
      vec_scale_identity: vec_scale({one}, ?v) <=> ?v
    }}
  end
end
"#
    )
}

/// THE REPLACEMENT POSITION. A compound on the right of `<=>` whose functor names nothing
/// is refused, in the replacement's own sentence, at its `line:col`, qualified or bare.
#[test]
fn a_replacement_that_names_nothing_is_refused() {
    for (functor, at) in [("Bogus.nope", "6:23"), ("nope_bare", "6:23")] {
        let errs = refusals(&format!(
            r#"
namespace test.wi6rrva.rhs
  import anthill.prelude.{{Float}}
  sort S
    operation f(a: Float) -> Float
    rule r: f(?a) <=> {functor}(?a)
  end
end
"#
        ));
        assert_refused_naming(
            &errs,
            &[
                &format!("equation replacement term `{functor}` names nothing"),
                "no rule, fact, operation, entity, const or builtin is declared under that name",
                "equals a term nothing gives a meaning to",
                at,
            ],
            "a law's right-hand side naming nothing",
        );
    }
}

/// THE TICKET'S OWN INSTANCE, restored with dead spellings: the replacement's compound,
/// the replacement's dotted constant, and the subject argument's dotted constant are each
/// refused, each in its own position's sentence.
#[test]
fn the_scalar_side_laws_dead_addresses_are_each_refused() {
    let errs = names_nothing(&vector_space(
        "dead",
        "Nope.sub(Nope.zero, Multiplicative.one)",
        "Nope.one",
    ));
    assert_refused_naming(
        &errs,
        &[
            "equation replacement term `Nope.sub` names nothing",
            "equation replacement term `Nope.zero` names nothing",
            "head argument term `Nope.one` names nothing",
        ],
        "VectorSpace's laws over addresses that name nothing",
    );
    assert_eq!(
        errs.len(),
        3,
        "one refusal per dead address. Got:\n{errs:#?}"
    );
}

/// CONTROL: the spellings the stdlib writes, and the `Ring.*` spellings, which resolve
/// through `Ring`'s `provides` since WI-20260825-X9RRN, load — the check asks the dotted
/// ladder the resolver asks, that rung included.
#[test]
fn the_live_and_the_provided_addresses_load() {
    for (ns, scalar, one) in [
        (
            "live",
            "Additive.sub(Additive.zero, Multiplicative.one)",
            "Multiplicative.one",
        ),
        ("provided", "Ring.sub(Ring.zero, Ring.one)", "Ring.one"),
    ] {
        let errs = refusals(&vector_space(ns, scalar, one));
        assert!(errs.is_empty(), "{ns}: the laws load. Got:\n{errs:#?}");
    }
}

/// CONTROL, DRIVEN: a replacement that resolves rewrites to its value, and a dotted name
/// in a head argument that resolves matches — `K.seven` is the const's value there.
///
/// WHAT THIS DOES NOT REACH, found by `/code-review`: `K.seven` is folded to `7` before the
/// dotted check is asked, so it says nothing about that check. `K.one` in a fact head is
/// not folded and is asked — `a_dotted_name_that_resolves_reaches_the_check_and_loads`.
#[test]
fn the_names_that_resolve_run() {
    let src = r#"
namespace test.wi6rrva.run
  import anthill.prelude.{Int64}
  sort K
    const seven: Int64 = 7
    operation one() -> Int64 = 1
  end
  operation f(a: Int64) -> Int64
  rule r: f(?a) <=> K.one() @[simp]
  operation main() -> Int64 = f(5)
  fact holds(K.seven)
  rule drive(1) :- holds(7)
end
"#;
    assert_eq!(
        crate::common::run_int64(src, "test.wi6rrva.run.main"),
        Ok(1)
    );
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        crate::common::definite_unary(&mut kb, "test.wi6rrva.run.drive").len(),
        1,
        "`holds(7)` finds `holds(K.seven)`",
    );
}

/// A CHAIN IS NAMED ONCE, where its resolution fails: `Bogus.x.y` is `Bogus.x` read `.y`,
/// and the refusal names `Bogus.x` — on either side of the equation.
#[test]
fn a_chain_is_named_once_where_it_fails() {
    let errs = names_nothing(
        r#"
namespace test.wi6rrva.chain
  import anthill.prelude.{Int64}
  sort S
    operation f(a: Int64) -> Int64
    rule r1: f(?a) <=> Bogus.x.y
    rule r2: f(Bogus.p.q) <=> 0
  end
end
"#,
    );
    assert_refused_naming(
        &errs,
        &[
            "equation replacement term `Bogus.x` names nothing",
            "head argument term `Bogus.p` names nothing",
        ],
        "a three-segment chain whose second segment fails",
    );
    assert_eq!(errs.len(), 2, "one refusal per chain. Got:\n{errs:#?}");
}

/// A PROJECTION IS NOT A PATH: a chain rooted at a clause parameter reads its field, and one
/// whose prefix is a value (`K.mk`, a nullary operation) reads that value's field. Neither
/// names anything by itself, and neither is refused. A chain rooted at a `let` binder is
/// the third kind, and `wi_qk77s_…::a_rewrite_reads_the_member_where_it_is_written` reads a
/// member through one to a value — the census's one false report, before the gate.
///
/// The whole load must be clean, not only free of this check's sentence: an untagged
/// parameter-form equation is refused on its own (§5.3), and a row asserting only the
/// absence of "names nothing" would pass over that refusal saying nothing.
#[test]
fn a_projection_is_not_a_path() {
    let param = refusals(
        r#"
namespace test.wi6rrva.param
  import anthill.prelude.{Int64}
  sort Pt
    entity pt(x: Int64)
  end
  operation px(p: Pt) -> Int64
  rule r: px(p: Pt) <=> p.x @[simp]
end
"#,
    );
    assert!(
        param.is_empty(),
        "`p.x` reads the parameter's field. Got:\n{param:#?}"
    );
    let value = refusals(
        r#"
namespace test.wi6rrva.value
  import anthill.prelude.{Int64}
  sort K
    entity box(v: Int64)
    operation mk() -> K = box(v: 4)
  end
  sort S
    operation f(a: Int64) -> Int64
    rule r: f(?a) <=> K.mk.v
  end
end
"#,
    );
    assert!(
        value.is_empty(),
        "`K.mk.v` reads `v` off `K.mk()`. Got:\n{value:#?}"
    );
}

/// CONTROL: what a head INTRODUCES is not judged — the subject an equation defines, and its
/// own name on the right (`foo` is the one the subject introduces) — and neither is a bare
/// name, which is a symbolic constant (kernel-language.md §5.3). Its qualified twin is a
/// path, and the rows above refuse it.
#[test]
fn what_a_head_introduces_is_not_judged() {
    let errs = refusals(
        r#"
namespace test.wi6rrva.intro
  import anthill.prelude.{Int64}
  rule comm: foo(?a, ?b) <=> foo(?b, ?a)
  sort S
    operation h(a: Int64) -> Int64
    rule sym: h(?a) <=> alpha
  end
end
"#,
    );
    assert!(errs.is_empty(), "the fixture loads. Got:\n{errs:#?}");
}

// ── Rows from `/code-review` of the first cut ─────────────────────────────────────────

/// A dotted name is judged in a plain FACT head as in a law: `holds(Bogus.zero)` with
/// nothing declaring `Bogus.zero` matches nothing a declared name is written as.
#[test]
fn a_dotted_name_in_a_fact_head_is_judged() {
    let errs = names_nothing(
        r#"
namespace test.wi6rrva.fact
  fact holds(Bogus.zero)
end
"#,
    );
    assert_refused_naming(
        &errs,
        &["head argument term `Bogus.zero` names nothing", "3:14"],
        "a fact head's dotted argument naming nothing",
    );
}

/// CONTROL: a dotted name that resolves and is NOT folded away first — a nullary
/// operation — reaches the dotted check and loads.
#[test]
fn a_dotted_name_that_resolves_reaches_the_check_and_loads() {
    let errs = refusals(
        r#"
namespace test.wi6rrva.reach
  import anthill.prelude.{Int64}
  sort K
    operation one() -> Int64 = 1
  end
  fact holds(K.one)
end
"#,
    );
    assert!(
        errs.is_empty(),
        "`K.one` names the operation. Got:\n{errs:#?}"
    );
}

/// A PAREN-LESS FACT DECLARES ITS NAME: `fact Bogus.zero` files an arity-0 proposition that
/// only the discrimination tree holds, and a rule-body goal of that name answers it, so a
/// head argument of that name names it too — with a sort `Bogus` in scope or without one.
/// The first cut asked the functor tables alone and refused both.
#[test]
fn a_dotted_name_a_fact_declares_is_declared() {
    for (ns, sort) in [("bare", ""), ("sorted", "  sort Bogus\n  end\n")] {
        let src = format!(
            "namespace test.wi6rrva.{ns}\n  import anthill.prelude.{{Int64}}\n{sort}  \
             fact Bogus.zero\n  fact holds(Bogus.zero)\n  rule drive(1) :- Bogus.zero\nend\n"
        );
        let errs = refusals(&src);
        assert!(
            errs.is_empty(),
            "{ns}: the fact declares `Bogus.zero`. Got:\n{errs:#?}"
        );
        let mut kb = crate::common::load_kb_with(&src);
        assert_eq!(
            crate::common::definite_unary(&mut kb, &format!("test.wi6rrva.{ns}.drive")).len(),
            1,
            "{ns}: the goal `Bogus.zero` finds the fact the head argument names",
        );
    }
}

/// A HIDDEN MEMBER IS REFUSED as the forbidden access it is, as its compound spelling is: a
/// path that reaches only an `internal` operation of another scope has an answer, and it is
/// not the citing scope's to use. The first cut counted it answered and said nothing.
#[test]
fn a_hidden_member_is_refused_as_the_access_it_is() {
    let errs = refusals(
        r#"
namespace test.wi6rrva.lib
  import anthill.prelude.{Int64}
  sort Vault
    internal operation secret() -> Int64 = 1
  end
end
namespace test.wi6rrva.hidden
  import test.wi6rrva.lib.{Vault}
  fact holds(Vault.secret)
end
"#,
    );
    assert_refused_naming(
        &errs,
        &["'Vault.secret' is internal to 'test.wi6rrva.lib.Vault'"],
        "a fact head's dotted argument reaching an internal operation",
    );
}

/// A NAME READ THROUGH A REQUIREMENT is the operation its dictionary holds (WI-20261013-50ZMN),
/// in an argument and in a replacement, paren-less or applied — `R.add(?a, ?a)` type-checks
/// where the rewrite fires. A member the requirement does not hold names nothing.
#[test]
fn a_name_read_through_a_requirement_is_not_judged() {
    let law = |ns: &str, rhs: &str| {
        format!(
            r#"
namespace test.wi6rrva.{ns}
  import anthill.prelude.{{Int64, Additive, Multiplicative}}
  import anthill.prelude.algebra.{{Ring}}
  sort G
    sort F = ?
    requires R: Ring[F]
    operation f(a: F) -> F
    rule r1: f(R.one) <=> {rhs}
    rule r2: f(?a) <=> R.add(?a, ?a) @[simp]
    operation g(a: F) -> F = f(a)
  end
end
"#
        )
    };
    let errs = refusals(&law("req", "R.zero"));
    assert!(
        errs.is_empty(),
        "`R.one`, `R.zero`, `R.add` are `Ring`'s. Got:\n{errs:#?}"
    );
    assert_refused_naming(
        &names_nothing(&law("reqnope", "R.nope")),
        &["equation replacement term `R.nope` names nothing"],
        "a member no requirement holds",
    );
}

/// A DOTTED SUBJECT IS ONE NAME: every node inside `Foo.Bar.c` is a segment of the name the
/// subject introduces, as `Foo.Bar.c()` introduces it, and none is an argument. The first
/// cut judged the inner `Foo.Bar`.
#[test]
fn a_dotted_subject_is_one_name() {
    let errs = refusals(
        r#"
namespace test.wi6rrva.subject
  import anthill.prelude.{Int64}
  sort Foo
    operation a() -> Int64 = 1
  end
  rule r1: Foo.Bar.c <=> 0
  rule r2: X.Y.c <=> 0
end
"#,
    );
    assert!(
        errs.is_empty(),
        "the subjects introduce their names. Got:\n{errs:#?}"
    );
}

/// THE SUBJECT REPEATED IN ITS REPLACEMENT is the name the equation is about: a guarded
/// `bar(?a) = bar(?a) :- g` is a law about `bar` exactly as `baz(?a) = 0 :- g` is one about
/// `baz`, and the first cut refused only the first (`wi627_…`'s fixture is this shape).
#[test]
fn the_subject_repeated_in_its_replacement_is_not_judged() {
    let errs = refusals(
        r#"
namespace test.wi6rrva.repeat
  import anthill.prelude.{Int64}
  rule bodied: bar(?a) = bar(?a) :- Int64.gt(1, 0)
  rule bodied2: baz(?a) = 0 :- Int64.gt(1, 0)
end
"#,
    );
    assert!(errs.is_empty(), "both laws load. Got:\n{errs:#?}");
}

/// DECIDED, NOT OVERLOOKED: a call through a sigil-free PARAMETER in a replacement names
/// nothing, and is refused. `f` stays a bare name in the stored term, not the parameter's
/// variable, so the rewrite never produced a call of the function bound to `f` — MEASURED
/// with the replacement exempt, `app(inc, 4)` died `OperationBodyMissing`, typed by the
/// arrow or by a sort alias of it. `/code-review` proposed exempting it as a binding.
#[test]
fn a_call_through_a_parameter_names_nothing() {
    let errs = names_nothing(
        r#"
namespace test.wi6rrva.param_call
  import anthill.prelude.{Int64}
  operation app(f: (x: Int64) -> Int64, x: Int64) -> Int64
  rule r: app(f: (x: Int64) -> Int64, x: Int64) <=> f(x) @[simp]
end
"#,
    );
    assert_refused_naming(
        &errs,
        &["equation replacement term `f` names nothing"],
        "a call through a parameter in a replacement",
    );
}
