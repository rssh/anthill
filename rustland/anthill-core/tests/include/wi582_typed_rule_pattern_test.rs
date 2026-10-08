//! WI-582 — explicit typed rule patterns (`?x: T`).
//!
//! The EXPLICIT surface for type-directed rules: a `: T` annotation on a rule
//! LHS pattern variable. Distinct from the IMPLICIT path (WI-292), where a
//! `@[simp]` rule inherits its enclosing sort's `requires`. Here the rule is a
//! bare top-level relation in NO requires-sort, so the implicit guard is
//! inapplicable — the explicit `?x: Summable.T` bound is the deciding guard.
//!
//! Semantics (the desugaring): `keep(?x: Summable.T, ?y) = ?x` MEANS
//! `keep[A](?x: A, ?y) = ?x :- Summable[A]` — `?x` is a value of a sort that
//! provides `Summable`. The loader STRIPS the annotation from the head (so the
//! discrimination tree indexes `keep(?x, ?y)` identically to the untyped form —
//! carrier-neutral, M1) and installs the requirement as a per-variable `Type`
//! constraint keyed by the variable's DeBruijn index
//! (`install_rule_type_bounds`). At fire, `apply_eq_rules` reads each matched
//! value's CARRIED type (WI-578, `value_type_term`) and checks its sort provides
//! the spec — firing where it does, suspending (leaving the redex) where it does
//! not or the type is under-determined (never NAF-deciding an undecided guard;
//! WI-067).
//!
//! WI-20261005-KSSA4: the variable is typed `Summable.T`, not `Summable`. A value
//! whose sort provides `Summable` is the `T` of a `Summable`; it is not a
//! `Summable`, in a rule head as in an operation's signature, and the direct
//! spelling is a load error (`a_variable_typed_at_the_spec_itself_is_refused`).

use anthill_core::kb::term::{Literal, Term};
use smallvec::SmallVec;

/// A parametric spec sort `Summable` that `Int64` provides (`fact
/// Summable[T = Int64]`) and `Bool` does not, plus an operation `keep[A]` in a
/// PLAIN sort (`Lib`, no `requires`) with a `@[simp]` rule carrying an explicit
/// typed pattern `keep(?x: Summable.T, ?y) = ?x`. Because `Lib` declares no
/// `requires`, the IMPLICIT guard (WI-292) is inapplicable: only the EXPLICIT
/// per-variable bound `?x: Summable.T` gates firing. The annotation is stripped
/// from the head before the typer sees it, so it does not collide with the
/// signature's `x: A`.
const SRC: &str = r#"
namespace test.wi582
  import anthill.prelude.{Int64, Bool, Eq}
  import test.wi582.Lib.{keep}

  sort Summable
    sort T = ?
    requires Eq[T]
  end


  sort Lib
    sort A = ?
    operation {
      keep(x: A, y: A) -> A
    }
    rule {
      keep_id: keep(?x: Summable.T, ?y) <=> ?x @[simp]
    }
  end
end

namespace anthill.prelude.Int64
  import test.wi582.Summable
  provides Summable[T = Int64]
end
"#;

#[test]
fn typed_pattern_bound_installed_on_rule() {
    let kb = crate::common::load_kb_with(SRC);
    // The explicit `?x: Summable.T` bound is stripped from the head and recorded
    // as a per-variable Type bound, keyed by the variable's DeBruijn index.
    // The rule's head functor is `Eq.eq` (it is an equation), so look it up by
    // its citation label `keep_id`, not by the `keep` operation symbol.
    let rid = kb
        .rule_id_by_qn("test.wi582.Lib.keep_id")
        .expect("keep_id rule loaded");
    let bounds = kb.rule_type_bounds(rid);
    assert_eq!(
        bounds.len(),
        1,
        "keep must carry exactly one typed-pattern bound (?x: Summable.T); got {bounds:?}",
    );
    // ?x is first in the frame. Its bound's carrier type and dictionary also
    // occupy frame slots, so use the complete arity when reversing the index.
    assert_eq!(
        bounds[0].0,
        kb.rule_arity(rid) - 1,
        "the bound must key ?x's DeBruijn index"
    );
    assert!(
        matches!(
            kb.get_term(bounds[0].1),
            Term::Var(anthill_core::kb::term::Var::DeBruijn(_))
        ),
        "the bound names a real carrier type slot, not the spec instance"
    );
}

#[test]
fn typed_pattern_fires_when_carrier_provides_the_bound() {
    let mut kb = crate::common::load_kb_with(SRC);
    let keep = kb
        .try_resolve_symbol("test.wi582.Lib.keep")
        .expect("keep symbol");
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    let term = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[five, seven]),
        named_args: SmallVec::new(),
    });
    // keep(5, 7): ?x = 5, carried type Int64, which provides Summable → the
    // explicit bound holds → the rule fires → 5. Compare by VALUE (the
    // instantiated RHS carries the matched 5; WI-584).
    let result = kb.simplify(term);
    assert_eq!(
        kb.get_term(result),
        &Term::Const(Literal::Int(5)),
        "keep must fire over Int64 (which provides Summable): keep(5, 7) → 5; got {:?}",
        kb.get_term(result),
    );
}

#[test]
fn typed_pattern_suspends_when_carrier_lacks_the_bound() {
    let mut kb = crate::common::load_kb_with(SRC);
    let keep = kb
        .try_resolve_symbol("test.wi582.Lib.keep")
        .expect("keep symbol");
    let t = kb.alloc(Term::Const(Literal::Bool(true)));
    let f = kb.alloc(Term::Const(Literal::Bool(false)));
    let term = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[t, f]),
        named_args: SmallVec::new(),
    });
    // keep(true, false): ?x = true, carried type Bool, which does NOT provide
    // Summable → the explicit bound fails → the rule does NOT fire (the redex is
    // left intact). Firing here would erase a call whose `?x: Summable.T` is unmet.
    assert_eq!(
        kb.simplify(term),
        term,
        "keep must NOT fire over Bool (which lacks Summable): keep(true, false) is left intact",
    );
}

#[test]
fn typed_pattern_checks_the_annotated_variable_not_a_sibling() {
    // MIXED-type arguments: the bound is on ?x (the first arg). A wrong-variable
    // bug — e.g. a DeBruijn-index mismatch that reads ?y instead of ?x — would
    // invert both assertions. Same-typed args (5,7 / true,false) cannot catch it.
    let mut kb = crate::common::load_kb_with(SRC);
    let keep = kb
        .try_resolve_symbol("test.wi582.Lib.keep")
        .expect("keep symbol");
    // keep(5, true): ?x = 5 (Int64 provides Summable) → FIRES to 5, regardless of
    // ?y = true (Bool, which does NOT provide Summable). The guard is on ?x only.
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let tru = kb.alloc(Term::Const(Literal::Bool(true)));
    let fire = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[five, tru]),
        named_args: SmallVec::new(),
    });
    let fire_res = kb.simplify(fire);
    assert_eq!(
        kb.get_term(fire_res),
        &Term::Const(Literal::Int(5)),
        "guard is on ?x: keep(5, true) must fire on ?x=Int64 (ignoring ?y=Bool); got {:?}",
        kb.get_term(fire_res),
    );
    // keep(true, 5): ?x = true (Bool lacks Summable) → SUSPENDS, even though
    // ?y = 5 (Int64) provides it. A bug reading ?y would wrongly fire here.
    let tru2 = kb.alloc(Term::Const(Literal::Bool(true)));
    let five2 = kb.alloc(Term::Const(Literal::Int(5)));
    let susp = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[tru2, five2]),
        named_args: SmallVec::new(),
    });
    assert_eq!(
        kb.simplify(susp),
        susp,
        "guard is on ?x: keep(true, 5) must suspend on ?x=Bool (ignoring ?y=Int64)",
    );
}

/// The `[T]` type-variable-introducer form `keep[T](?x: T, ?y) = ?x :- Summable[T]`
/// — the verbose spelling of the inline `keep(?x: Summable.T, ?y) = ?x`. The loader
/// desugars it: the head introduces `T`, the guard `:- Summable[T]` bounds it, and
/// `?x: T` folds to the requirement of `Summable`. It must load and fire identically.
const SRC_TP: &str = r#"
namespace test.wi582tp
  import anthill.prelude.{Int64, Bool, Eq}
  import test.wi582tp.Lib.{keep}

  sort Summable
    sort T = ?
    requires Eq[T]
  end


  sort Lib
    sort A = ?
    operation {
      keep(x: A, y: A) -> A
    }
    rule {
      keep_id: keep[T](?x: T, ?y) <=> ?x :- Summable[T] @[simp]
    }
  end
end

namespace anthill.prelude.Int64
  import test.wi582tp.Summable
  provides Summable[T = Int64]
end
"#;

#[test]
fn tparam_form_folds_guard_into_bound_and_fires() {
    let mut kb = crate::common::load_kb_with(SRC_TP);
    // Desugared: the head-introduced `T` bounded by `:- Summable[T]` folds into
    // the requirement on `?x`, installed as the single per-variable bound.
    let rid = kb
        .rule_id_by_qn("test.wi582tp.Lib.keep_id")
        .expect("keep_id rule loaded");
    let bounds = kb.rule_type_bounds(rid);
    assert_eq!(
        bounds.len(),
        1,
        "the [T] form must install one folded bound on ?x; got {bounds:?}",
    );
    // The value, carrier type and dictionary slots share one reversed frame.
    assert_eq!(
        bounds[0].0,
        kb.rule_arity(rid) - 1,
        "the bound keys ?x in the frame including its carrier type variable"
    );

    let keep = kb
        .try_resolve_symbol("test.wi582tp.Lib.keep")
        .expect("keep symbol");
    // Fires over Int64 (provides Summable).
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    let pos = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[five, seven]),
        named_args: SmallVec::new(),
    });
    let pos_res = kb.simplify(pos);
    assert_eq!(
        kb.get_term(pos_res),
        &Term::Const(Literal::Int(5)),
        "[T] form must fire over Int64: keep(5, 7) → 5; got {:?}",
        kb.get_term(pos_res),
    );
    // Suspends over Bool (does not provide Summable).
    let t = kb.alloc(Term::Const(Literal::Bool(true)));
    let f = kb.alloc(Term::Const(Literal::Bool(false)));
    let neg = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[t, f]),
        named_args: SmallVec::new(),
    });
    assert_eq!(
        kb.simplify(neg),
        neg,
        "[T] form must NOT fire over Bool: keep(true, false) left intact",
    );
}

/// The same rule with the variable typed at the spec itself. `Summable` is a spec
/// over its parameter `T`: a value whose sort provides it is not a `Summable`, so
/// the bound could match nothing. The load says so and names both repairs.
const SRC_DIRECT: &str = r#"
namespace test.wi582direct
  import anthill.prelude.{Int64, Bool, Eq}
  import test.wi582direct.Lib.{keep}

  sort Summable
    sort T = ?
    requires Eq[T]
  end


  sort Lib
    sort A = ?
    operation {
      keep(x: A, y: A) -> A
    }
    rule {
      keep_id: keep(?x: Summable, ?y) <=> ?x @[simp]
    }
  end
end

namespace anthill.prelude.Int64
  import test.wi582direct.Summable
  provides Summable[T = Int64]
end
"#;

/// A WRITTEN `domain` GOAL AT THE SPEC IS THE SAME QUESTION, asked in a body: is the matched
/// value a `Summable`? No value is — `Int64` provides it, and is its `T` — so the goal
/// holds of nothing and is refused where it is written (WI-20261005-KSSA4). It answered by
/// provision before: `d(?b)` held of the row whose first column is an `Int64`.
///
/// THE CONTROL is the bound spelling of what the goal meant, `d[A](?a: A, ?b) … :-
/// Summable[A]`, which loads and answers that one row. FAILS with the body's goal sorts
/// not recorded (`note_written_domain_goal_sorts`): the program loads.
#[test]
fn a_written_domain_goal_at_the_spec_is_refused() {
    let program = |rule: &str| {
        format!(
            r#"
namespace test.wi582domain
  import anthill.prelude.{{Int64, Bool}}
  import anthill.kernel.{{domain}}

  sort Summable
    sort T = ?
    operation zero() -> T
  end

  fact src(1, 10)
  fact src(true, 20)

  {rule}
end

namespace anthill.prelude.Int64
  import test.wi582domain.Summable
  provides Summable[T = Int64]
  operation zero() -> Int64 = 0
end
"#
        )
    };
    let errs = crate::common::load_errors_of(&program(
        "rule d(?b) :- src(?a, ?b), domain(?a, Summable)\n  rule outd(?b) :- d(?b)",
    ));
    assert_eq!(errs.len(), 1, "one refusal, at the goal; got {errs:#?}");
    assert!(
        errs[0].contains("a `domain` goal asks whether a value is a `test.wi582domain.Summable`")
            && errs[0].contains("so the goal holds of nothing"),
        "the refusal says what the goal asks and why nothing answers; got {}",
        errs[0],
    );
    let mut kb = crate::common::load_kb_with(&program(
        "rule d[A](?a: A, ?b) :- src(?a, ?b), Summable[A]\n  rule outd(?b) :- d(?a, ?b)",
    ));
    let rows = crate::common::query_unary(&mut kb, "test.wi582domain.outd");
    assert!(
        matches!(rows.as_slice(), [(anthill_core::eval::Value::Int(10), _)]),
        "the bound spelling holds of the `Int64` row alone; got {rows:?}",
    );
}

#[test]
fn a_variable_typed_at_the_spec_itself_is_refused() {
    let errs = crate::common::load_errors_of(SRC_DIRECT);
    assert_eq!(errs.len(), 1, "one refusal, at the bound; got {errs:#?}");
    let e = &errs[0];
    assert!(
        e.contains("a rule variable is typed `test.wi582direct.Summable`")
            && e.contains("Write `test.wi582direct.Summable.T`")
            && e.contains(":- test.wi582direct.Summable[A]"),
        "the refusal names the spec, the member spelling and the introducer; got {e}",
    );
}

// ── the bound is a requirement wherever it is read ───────────────────────────────────

/// `Summable` over its parameter, provided by `Int64`; `body` follows inside the namespace.
fn summable(ns: &str, imports: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String}}
{imports}
  sort Summable
    sort T = ?
    operation plus(a: T, b: T) -> T
  end
{body}
end

namespace anthill.prelude.Int64
  import {ns}.Summable
  provides Summable[T = Int64]
  operation plus(a: Int64, b: Int64) -> Int64 = a + b
end
"#
    )
}

/// A COLUMN BOUNDED BY `Summable.T` IS CITED WITH A PROVIDER'S VALUE. `keep(1)` applies the
/// relation to its first column from an operation body, and the argument is checked
/// against the bound the rule stores — a requirement, which an `Int64` meets. Compared as
/// a value's type, the citation was refused ("argument binding column `x` has an
/// incompatible type") and no spelling of the bound could be applied from functional code.
///
/// FAILS with the citation's compare made outside `spec_as_its_providers`: a load error.
/// The uncited relation passes either way.
#[test]
fn a_bounded_column_is_cited_with_a_providers_value() {
    let ns = "test.wi582cite";
    let src = summable(
        ns,
        "  import anthill.prelude.{List, Error}\n  import anthill.prelude.List.{length}\n",
        "  fact src(1, 10)\n  fact src(true, 20)\n  \
         rule keep(?x: Summable.T, ?y) :- src(?x, ?y)\n  \
         operation cited() -> Int64 effects Error = length(keep(1).takeN(5))\n  \
         operation whole() -> Int64 effects Error = length(keep.takeN(5))",
    );
    assert_eq!(crate::common::run_int64(&src, &format!("{ns}.cited")), Ok(1));
    assert_eq!(crate::common::run_int64(&src, &format!("{ns}.whole")), Ok(1));
}

/// A BOUND WITH A SLOT LEFT OPEN STILL ANSWERS. `?p: Pair[A = Summable.T]` writes no `B`:
/// the bound holds the requirement beside a type variable, and is pinned to the matched
/// value before it is compared. Pinned as a value's type, the requirement refuted every
/// provider and the rule answered nothing, in silence, where the twin with `B` written
/// answered the row.
///
/// FAILS with the pin made outside `spec_as_its_providers` (`pin_bound`): no answer. The
/// twin with every slot written passes either way.
#[test]
fn a_bound_with_a_slot_left_open_still_answers() {
    let ns = "test.wi582open";
    let mut kb = crate::common::load_kb_with(&summable(
        ns,
        "  import anthill.prelude.Pair\n  import anthill.prelude.Pair.{pair}\n",
        "  fact src(pair(1, \"a\"))\n  fact src(pair(true, \"b\"))\n  \
         rule keepOpen(?p: Pair[A = Summable.T]) :- src(?p)\n  \
         rule keepFull(?p: Pair[A = Summable.T, B = String]) :- src(?p)",
    ));
    for rule in ["keepOpen", "keepFull"] {
        let rows = crate::common::query_unary(&mut kb, &format!("{ns}.{rule}"));
        assert_eq!(
            rows.len(),
            1,
            "`{rule}` holds of the pair whose first component is an `Int64`; got {rows:?}",
        );
    }
}

/// A ROW'S LABEL INSIDE A BOUND IS NOT WHAT THE VARIABLE IS TYPED AT. `?a: (Int64) -> Int64
/// @ {Error[String]}` types `?a` at an arrow; `Error` is a label of its row, and the rule
/// loads as it did. Walked like any sort written in the bound, the label was refused: "a
/// rule variable is typed `anthill.prelude.Error`, a spec over its parameter `T`".
///
/// THE CONTROL is a spec standing where a type does inside the same arrow, which is
/// refused. A LOAD VERDICT ONLY — no fact holds a function for the bound to be matched
/// against. FAILS with effect rows walked (`collect_sorts_written_as_types`): refused.
#[test]
fn a_row_label_inside_a_bound_is_no_variables_type() {
    let ns = "test.wi582row";
    let program = |bound: &str| {
        summable(
            ns,
            "  import anthill.prelude.Error\n",
            &format!(
                "  fact src(1, 10)\n  rule g(?a: {bound}, ?b: Int64) :- src(?a, ?b)\n  \
                 rule outg(?b) :- g(?a, ?b)"
            ),
        )
    };
    let errs = crate::common::load_errors_of(&program("(Int64) -> Int64 @ {Error[String]}"));
    assert!(errs.is_empty(), "a row label is not a variable's type: {errs:#?}");
    let errs = crate::common::load_errors_of(&program("(Summable) -> Int64"));
    assert_eq!(errs.len(), 1, "one refusal, at the bound; got {errs:#?}");
    assert!(
        errs[0].contains(&format!("a rule variable is typed `{ns}.Summable`")),
        "a spec standing as an arrow's parameter is refused; got {}",
        errs[0],
    );
}

/// AN ALIAS OF THE SPEC IS REFUSED AS THE SPEC IS. `sort Sum1 = Summable` and `sort Sums =
/// List[T = Summable]` are the same types under other names; a variable typed at either is
/// typed at the spec. Classified as written, both loaded and answered by provision.
///
/// FAILS with the alias not read through (`check_rule_sort_uses`): both rules load.
#[test]
fn an_alias_of_the_spec_is_refused_as_the_spec_is() {
    let ns = "test.wi582alias";
    let errs = crate::common::load_errors_of(&summable(
        ns,
        "  import anthill.prelude.List\n",
        "  sort Sums = List[T = Summable]\n  sort Sum1 = Summable\n  \
         fact src([1, 2])\n  fact one(1)\n  \
         rule r(?xs: Sums) :- src(?xs)\n  rule direct(?x: Sum1) :- one(?x)",
    ));
    assert_eq!(errs.len(), 2, "one refusal for each rule; got {errs:#?}");
    for e in &errs {
        assert!(
            e.contains(&format!("a rule variable is typed `{ns}.Summable`")),
            "the refusal names the spec the alias stands for; got {e}",
        );
    }
}

/// A `domain` GOAL IN A CONSTRAINT IS THE SAME GOAL. `constraint c :- one(?x), domain(?x,
/// Summable)` asks of a value what a rule body's goal asks, and holds of nothing for the
/// same reason. Recorded only where a rule is loaded, it loaded there and held by
/// provision — the reading the refusal's own text says is not made.
///
/// FAILS with a constraint's body not recorded (`note_constraint_domain_goal_sorts`): the
/// program loads.
#[test]
fn a_domain_goal_in_a_constraint_is_refused_too() {
    let ns = "test.wi582constraint";
    let errs = crate::common::load_errors_of(&summable(
        ns,
        "  import anthill.kernel.{domain}\n",
        "  fact one(true)\n  constraint no_summable_ones\n    :- one(?x), domain(?x, Summable)",
    ));
    assert_eq!(errs.len(), 1, "one refusal, at the goal; got {errs:#?}");
    assert!(
        errs[0].contains(&format!(
            "a `domain` goal asks whether a value is a `{ns}.Summable`"
        )) && errs[0].contains("so the goal holds of nothing"),
        "the refusal says what the goal asks; got {}",
        errs[0],
    );
}

/// 8DXVK closes KSSA4's temporary refusal: an aliased member retains the instance
/// rather than dropping Out. Both spellings execute and admit only the integer.
/// Backing out 8DXVK refuses the member half; the introducer remains a control.
#[test]
fn a_member_through_an_alias_retains_the_members_it_fixes() {
    let ns = "test.wi582aliasmember";
    let program = |rule: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}

  sort Tagger
    sort C = ?
    sort Out = ?
    operation tag(x: C) -> Out
  end
  sort IntTagger = Tagger[Out = Int64]

  fact item(1)
  fact item("s")
  {rule}
end

namespace anthill.prelude.Int64
  import {ns}.Tagger
  provides Tagger[C = Int64, Out = Int64]
  operation tag(x: Int64) -> Int64 = x
end

namespace anthill.prelude.String
  import {ns}.Tagger
  import anthill.prelude.String
  provides Tagger[C = String, Out = String]
  operation tag(x: String) -> String = x
end
"#
        )
    };
    for rule in [
        "rule ints(?x: IntTagger.C) :- item(?x)",
        "rule ints[A](?x: A) :- item(?x), IntTagger[A]",
    ] {
        let mut kb = crate::common::load_kb_with(&program(rule));
        let rows = crate::common::query_unary(&mut kb, &format!("{ns}.ints"));
        assert!(
            matches!(rows.as_slice(), [(anthill_core::eval::Value::Int(1), true)]),
            "{rule} holds of the `Int64` item alone; got {rows:?}",
        );
    }
}

/// THE MEMBER NAMED IS THE ONE A PROVIDER IS. `Tagger`'s operations receive on `C`, so a
/// sort that provides `Tagger` is its `C`: `?x: Tagger.Out` asks for a provider through a
/// member no provider is, and is refused naming `Tagger.C` — which holds of both items.
/// `Stream` receives on itself, so no member of it stands for a provider: `?x: Stream.T` is
/// refused the other way, and the variable typed `Stream` holds of the list.
///
/// Each refusal names a spelling, and the spelling is run. FAILS with a rule head's
/// members not recorded (`RuleSortSite::HeadMember`): both rules load.
#[test]
fn a_member_that_is_not_the_carrier_is_refused_naming_the_spelling_that_is() {
    let ns = "test.wi582member";
    let program = |rules: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Stream, List}}

  sort Tagger
    sort C = ?
    sort Out = ?
    operation tag(x: C) -> Out
  end

  fact item(1)
  fact item("s")
  fact listed([1, 2])
  fact listed(7)
  {rules}
end

namespace anthill.prelude.Int64
  import {ns}.Tagger
  provides Tagger[C = Int64, Out = Int64]
  operation tag(x: Int64) -> Int64 = x
end

namespace anthill.prelude.String
  import {ns}.Tagger
  import anthill.prelude.String
  provides Tagger[C = String, Out = String]
  operation tag(x: String) -> String = x
end
"#
        )
    };
    let errs = crate::common::load_errors_of(&program("rule outs(?x: Tagger.Out) :- item(?x)"));
    assert_eq!(errs.len(), 1, "one refusal, at the member; got {errs:#?}");
    assert!(
        errs[0].contains(&format!("`{ns}.Tagger.Out` in a rule head requires `{ns}.Tagger`"))
            && errs[0].contains("is its `C`, not its `Out`")
            && errs[0].contains(&format!("write `{ns}.Tagger.C`")),
        "the refusal names the member a provider is; got {}",
        errs[0],
    );
    let errs = crate::common::load_errors_of(&program("rule elems(?x: Stream.T) :- listed(?x)"));
    assert_eq!(errs.len(), 1, "one refusal, at the member; got {errs:#?}");
    assert!(
        errs[0].contains("`anthill.prelude.Stream.T` in a rule head")
            && errs[0].contains("is not a spec over a parameter")
            && errs[0].contains("Type the variable `anthill.prelude.Stream`"),
        "the refusal says the sort is its own carrier; got {}",
        errs[0],
    );
    let mut kb = crate::common::load_kb_with(&program(
        "rule taggers(?x: Tagger.C) :- item(?x)\n  rule streams(?x: Stream) :- listed(?x)",
    ));
    let taggers = crate::common::query_unary(&mut kb, &format!("{ns}.taggers"));
    assert_eq!(taggers.len(), 2, "both items' sorts provide `Tagger`; got {taggers:?}");
    let streams = crate::common::query_unary(&mut kb, &format!("{ns}.streams"));
    assert_eq!(streams.len(), 1, "the list is a `Stream`, and the `Int64` is not; got {streams:?}");
}
