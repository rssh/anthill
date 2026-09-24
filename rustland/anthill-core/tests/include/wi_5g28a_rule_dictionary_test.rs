//! WI-20260911-5G28A — a requirement DICTIONARY reaching a RULE: the two measurements the
//! type-domains direction (`docs/design/060-typedomains-implementation.md`) stands on,
//! one section each.
//!
//! 1. A RULE CITATION DROPS THE CALLER'S DICTIONARY — PINNED DEFECT. An operation with a
//!    rigid `A` and `requires WeakOrd[T = A]` cites a rule that calls `compare` on its
//!    values. Selected `[WeakOrd = Descending]`, the operation's OWN call answers through
//!    `Descending`; the RULE answers through `Int64`'s own ordering, whichever rival the
//!    caller selected. Nothing carries the caller's dictionary across the citation
//!    (`op-to-rule-requirement-channel.md` §5.1, crossing 2), so the clause's
//!    `require[WeakOrd[T]]` DERIVES one from the value's type, and 058 §3.2's default rung
//!    takes the carrier's own provision. A SILENT WRONG ANSWER, pinned here so the fix is
//!    seen when it lands: crossing 2 flips it to `4` / `-4`. A rule body cannot select a
//!    provider itself — the loader refuses a bracket there ("call an operation whose body
//!    carries the bracket") — so a passed dictionary is the only route a caller's choice
//!    has into a rule.
//!
//! 2. A DICTIONARY IS AN ORDINARY RULE ARGUMENT, AND ITS SUBTREE PROJECTS — the gate the
//!    ticket set on 2026-09-12 ("if a dictionary cannot ride a generative rule call and be
//!    projected, nothing else matters"). A dictionary DERIVED in one clause rides a
//!    GENERATIVE call as an ordinary head argument, `Dictionary.sub(?d, 0)` projects the
//!    ELEMENT's dictionary out of it, and the projection crosses a second head and is read
//!    and CHECKED (WI-860) like any other. This is §4.1's `List.member(?x, ?d)` shape —
//!    the tail keeps `?d`, the element takes `sub(?d, 0)` — driven with what exists.
//!
//! 3. THE WHOLE CASE — demo2: a GENERATIVE citation of a parameterised sort whose clause
//!    both ENUMERATES its values and CALLS AN OPERATION on each, the operation's provider
//!    chosen by the caller among two rivals. Both of today's answers are PINNED: the
//!    projected spelling LOADS since §7.3's S1 (it was refused, the citation typing its
//!    column at `Wrap`'s own `T` rather than at the bracket's `X`) and finds no row at run
//!    time, and the count spelling answers `0` where the answer is `1`.
//!    `060-implementation.md` §7.3 names the steps that flip each.
//!
//! BACK-OUT, measured: [V] drop the `from_view` fallback from `expect_dictionary`
//! (`eval/builtins.rs`). `the_element_dictionary_projects_out_of_a_passed_one` and
//! `a_projected_dictionary_is_read_and_checked` fail — `Dictionary.sub` refuses the
//! occurrence carrier a head-passed dictionary arrives on ("expected Dictionary, got
//! Node"), so `elemOfSum` answers one CONDITIONAL row with the whole tree in its residual,
//! and `agree` a CONDITIONAL `3`: `use`'s own derivation still answers, with the
//! projection left undecided beside it. PASS EITHER WAY, BY DESIGN: `an_operation_passes_its_dictionary_to_an_operation`
//! (op→op passing works, which is what makes section 1's number about the RULE edge),
//! `a_rule_citation_drops_the_callers_dictionary` (the pin — nothing here touches that
//! edge), `a_dictionary_derived_in_the_clause_reads_as_before` (the value carrier,
//! which `from_value` always read), and section 3's two pins (nothing here touches the
//! citation's typing or its evaluation).

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

// ── 1. the op→rule citation ─────────────────────────────────────────────────

/// Two opposite `Ord[Int64]` rivals beside `Int64`'s own provision — WI-870's pair, so
/// the three answers differ: `Descending` gives `4`, `Ascending` `-4`, and `Int64`'s own
/// `compare` `-1`, for `compare(1, 5)`.
const ORD_PROGRAM: &str = r#"
namespace wi5g28a.ord
  import anthill.prelude.{Int64, Error, EmptyStream, Ord, WeakOrd, PartialOrd, PartialEq, Eq}

  sort Ascending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end

  sort Descending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end

  -- a RULE that calls an operation of the requirement on its values
  rule cmp(?a, ?b, ?c) :- ?d = require[WeakOrd[T]], WeakOrd.compare(?a, ?b, ?c)

  sort Driver
    -- rigid `A`, with the requirement at `A`
    operation direct[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)
    operation viaRule[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = cmp(x, y).head.c

    operation directDesc() -> Int64 = direct[A = Int64, WeakOrd = Descending](1, 5)
    operation directAsc() -> Int64 = direct[A = Int64, WeakOrd = Ascending](1, 5)
    operation ruleDesc() -> Int64 effects {Error, Error[EmptyStream]} =
      viaRule[A = Int64, WeakOrd = Descending](1, 5)
    operation ruleAsc() -> Int64 effects {Error, Error[EmptyStream]} =
      viaRule[A = Int64, WeakOrd = Ascending](1, 5)
  end
end
"#;

/// Call a nullary driver on a FRESH interpreter — a trapped call poisons later calls on
/// a shared one, and `interp_for` panics on a dirty load, so a value here is also a
/// clean-load assertion.
fn drive(entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(ORD_PROGRAM);
    match interp.call(&format!("wi5g28a.ord.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// THE CONTROL for the pin below — passes either way, BY DESIGN. Between two OPERATIONS
/// the selected dictionary does travel: `direct`'s `compare` answers through whichever
/// rival its caller named. So when the rule below answers otherwise, the loss is at the
/// rule edge, not in the selection.
#[test]
fn an_operation_passes_its_dictionary_to_an_operation() {
    assert_eq!(drive("directDesc"), 4, "Descending: compare(1, 5) = 5 - 1");
    assert_eq!(drive("directAsc"), -4, "Ascending: compare(1, 5) = 1 - 5");
}

/// PINNED DEFECT — this row asserts today's WRONG answer, and crossing 2
/// (`op-to-rule-requirement-channel.md` §7 step 4) is what must flip it: the design
/// answer is `4` for `Descending` and `-4` for `Ascending`, the numbers the control above
/// gives.
///
/// Today both selections answer `-1`, `Int64`'s own `compare`: the citation `cmp(x, y)`
/// builds its query from the head alone, `viaRule`'s `WeakOrd[A]` dictionary stays in
/// `viaRule`'s frame, and `cmp`'s `require[WeakOrd[T]]` re-derives at the value's type,
/// where the carrier's own provision is the default among three. MEASURED 2026-09-24 in
/// a rule alone (`?d = require[WeakOrd[T]], WeakOrd.compare(1, 5, ?c)`): `?d`'s impl is
/// `Int64`, definite.
///
/// WHAT THE FLIP MUST ALSO DECIDE: a supplied dictionary is CHECKED against the local
/// derivation (WI-860), and the local derivation here is that DEFAULT pick. If the check
/// reads a default as a unique derivation, `Descending` is refused instead of answering
/// `4`. WI-20260922-ATFGH's reading is that a default among several answers "which
/// provider wins", not "which one built this value" — so it must not veto a supplied one.
#[test]
fn a_rule_citation_drops_the_callers_dictionary() {
    let (desc, asc) = (drive("ruleDesc"), drive("ruleAsc"));
    // The DEFECT is that the selection is ignored — both rivals give one number; the
    // number is which provider the re-derivation fell back to. Asserted as the pair so
    // a change that moves only the fallback reads as that, not as the fix.
    assert_eq!(
        desc, asc,
        "PINNED DEFECT: the rule ignores the caller's selection — one answer for both \
         rivals. If they now DIFFER (4, -4), crossing 2 has landed — flip this row to \
         assert that. Got (Descending, Ascending) = ({desc}, {asc})",
    );
    assert_eq!(
        (desc, asc),
        (-1, -1),
        "PINNED DEFECT: the rule answers through `Int64`'s own ordering whichever rival \
         the caller selected. If this now reads (4, -4), crossing 2 has landed — flip this \
         row to assert that. Got (Descending, Ascending) = ({desc}, {asc})",
    );
}

// ── 2. a dictionary as a rule argument, projected ───────────────────────────

/// NAR1X's conditional provider: `Wrap`'s `Zeroable` needs its element's, so the
/// dictionary for `Zeroable[Wrap]` is `Dictionary(Dictionary(impl: <element>), impl:
/// Wrap)` and `sub(0)` is the element's. `Sum` and `Prod` differ in every number, so a
/// projection that answered a constant cannot pass.
const GATE_PROGRAM: &str = r#"
namespace wi5g28a.gate
  import anthill.prelude.Int64
  import anthill.realization.runtime.Dictionary

  sort Zeroable
    sort T = ?
    operation zero() -> Int64
    operation tag(x: T) -> Int64 = 0
  end

  sort Sum
    import anthill.prelude.Int64
    entity sum
    provides Zeroable[T = Sum]
    operation zero() -> Int64 = 3
    operation tag(x: Sum) -> Int64 = 1
  end

  sort Prod
    import anthill.prelude.Int64
    entity prod
    provides Zeroable[T = Prod]
    operation zero() -> Int64 = 5
    operation tag(x: Prod) -> Int64 = 2
  end

  sort Wrap
    import anthill.prelude.Int64
    sort E = ?
    entity wrap(inner: E)
    provides Zeroable[T = Wrap] :- Zeroable[E] where
      operation zero() -> Int64 = Int64.add(Zeroable.zero(), 100)
      operation tag(x: Wrap) -> Int64 = 9
    end
  end

  -- a dictionary DERIVED in one clause, from a ground anchor
  rule get(?x, ?d) :- ?d = require[Zeroable[T]], Zeroable.tag(?x, ?t)

  -- GENERATIVE: `?w` is free and `?d` is an ordinary argument; the element's is PROJECTED
  rule gen(?w, ?d, ?ed) :- ?ed <=> Dictionary.sub(?d, 0), ?w <=> wrap(inner: ?i)

  rule elemOfSum(?s) :- get(wrap(inner: sum()), ?d), gen(?w, ?d, ?ed), ?s <=> Dictionary.impl(?ed)
  rule elemOfProd(?s) :- get(wrap(inner: prod()), ?d), gen(?w, ?d, ?ed), ?s <=> Dictionary.impl(?ed)
  rule rootOfSum(?s) :- get(wrap(inner: sum()), ?d), ?s <=> Dictionary.impl(?d)

  -- the projection crosses a SECOND head and is read by `require`, which CHECKS it
  rule use(?e, ?ed, ?r) :- ?ed = require[Zeroable[T]], Zeroable.tag(?e, ?u), Zeroable.zero(?r)
  rule agree(?r) :- get(wrap(inner: sum()), ?d), gen(?w, ?d, ?ed), use(sum(), ?ed, ?r)
  rule disagree(?r) :- get(wrap(inner: prod()), ?d), gen(?w, ?d, ?ed), use(sum(), ?ed, ?r)
end
"#;

/// The sort a symbol answer names, by qualified name — read through the view, since an
/// answer may ride a `SymbolRef` or a nullary term.
fn sort_named(kb: &KnowledgeBase, v: &Value) -> String {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    match v.head(kb) {
        ViewHead::Ident(s)
        | ViewHead::Functor {
            functor: Some(s),
            pos_arity: 0,
            ..
        } => kb.qualified_name_of(s).to_string(),
        _ => panic!("expected an answer naming a sort, got {v:?}"),
    }
}

/// The ONE definite answer of a unary relation, as the sort it names. Asserts that the
/// relation answered exactly that and nothing conditional: under the back-out the row is
/// one CONDITIONAL answer, which a definite-only count would miss as "no answer" rather
/// than as the undecided goal it is.
fn only_sort(kb: &mut KnowledgeBase, rel: &str) -> String {
    let all = crate::common::query_unary(kb, rel);
    assert!(
        all.len() == 1 && all[0].1,
        "{rel}: expected exactly one DEFINITE answer, got {all:?}",
    );
    sort_named(kb, &all[0].0)
}

/// The control — passes either way, BY DESIGN. A dictionary derived in the SAME clause
/// is built by `fetch_dictionary` on the value carrier, which `Dictionary::from_value`
/// has always read.
#[test]
fn a_dictionary_derived_in_the_clause_reads_as_before() {
    let mut kb = crate::common::load_kb_with(GATE_PROGRAM);
    assert_eq!(only_sort(&mut kb, "wi5g28a.gate.rootOfSum"), "wi5g28a.gate.Wrap");
}

/// THE GATE. The dictionary crosses `gen`'s head as an ordinary argument — `gen` has no
/// value to derive anything from, `?w` is its output — and `sub(?d, 0)` is the ELEMENT's
/// dictionary: `Sum` for one tree, `Prod` for the other, so it is read off the tree that
/// arrived and not off anything `gen` knows.
#[test]
fn the_element_dictionary_projects_out_of_a_passed_one() {
    let mut kb = crate::common::load_kb_with(GATE_PROGRAM);
    assert_eq!(only_sort(&mut kb, "wi5g28a.gate.elemOfSum"), "wi5g28a.gate.Sum");
    assert_eq!(only_sort(&mut kb, "wi5g28a.gate.elemOfProd"), "wi5g28a.gate.Prod");
}

/// The projection is a dictionary like any other: it crosses `use`'s head, `require`
/// reads it, and WI-860's check holds it to `use`'s own derivation at `sum()`. The
/// `Sum` projection agrees and the carrier-less `zero()` answers `Sum`'s `3`; the `Prod`
/// projection DISAGREES and the clause answers nothing at all — which is what says the
/// projected dictionary was read, since the local derivation alone would answer `3`
/// for both.
#[test]
fn a_projected_dictionary_is_read_and_checked() {
    let mut kb = crate::common::load_kb_with(GATE_PROGRAM);
    let agree = crate::common::query_unary(&mut kb, "wi5g28a.gate.agree");
    assert!(
        agree.len() == 1 && agree[0].1 && crate::common::scalar_int(&kb, &agree[0].0) == Some(3),
        "the agreeing projection answers `Sum`'s zero, 3, definitely; got {agree:?}",
    );
    let disagree = crate::common::query_unary(&mut kb, "wi5g28a.gate.disagree");
    assert!(
        disagree.is_empty(),
        "a projected `Prod` dictionary checked against `use`'s own `Sum` derivation must \
         answer NOTHING (WI-860) — not `3`, which would mean it was never read, and not a \
         conditional row, which is the back-out's undecided `Dictionary.sub`; got {disagree:?}",
    );
}

// ── 3. demo2: enumerate, and call the caller's operation on each value ──────

/// `Score` has two RIVAL witnesses at `Colour` and no provision on `Colour` itself, so
/// nothing but the caller's selection says which one a call means. Under `ByHeat` only
/// `red` scores 3, under `ByName` only `blue` does — so `top` has ONE row either way, and
/// WHICH row it is names the provider that reached the clause.
const DEMO2_PROGRAM: &str = r#"
namespace wi5g28a.demo2
  import anthill.prelude.{Int64, Error, EmptyStream}

  sort Score
    sort T = ?
    operation score(x: T) -> Int64
  end

  sort Colour
    entity red
    entity green
    entity blue
  end

  sort ByName
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 =
      match x
        case red() -> 1
        case green() -> 2
        case blue() -> 3
  end

  sort ByHeat
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 =
      match x
        case red() -> 3
        case green() -> 1
        case blue() -> 2
  end

  -- ENUMERATES `Wrap[T = T]` (its typed head) and CALLS `score` on each element
  sort Wrap[T]
    entity wrap(v: T)
    rule top(?x: Wrap[T = T]) :- ?d = require[Score[T]], ?x <=> wrap(?v), Score.score(?v, 3)
  end

  sort Driver
    operation countAt[X]() -> Int64 effects {Error} requires Score[T = X] =
      Wrap[T = X].top.takeN(5).length()
    operation countHeat() -> Int64 effects {Error} = countAt[X = Colour, Score = ByHeat]()
    operation countName() -> Int64 effects {Error} = countAt[X = Colour, Score = ByName]()
{projected}  end
end
"#;

/// The projected spelling — the one whose answer NAMES the provider (`wrap(red())` under
/// `ByHeat`, `wrap(blue())` under `ByName`) once the case works end to end.
const DEMO2_PROJECTED: &str = "    operation topAt[X]() -> Wrap[T = X] effects {Error, Error[EmptyStream]}\n      \
     requires Score[T = X] = Wrap[T = X].top.head.x\n    \
     operation topHeat() -> Wrap[T = Colour] effects {Error, Error[EmptyStream]} =\n      \
     topAt[X = Colour, Score = ByHeat]()\n";

fn demo2(projected: bool) -> String {
    DEMO2_PROGRAM.replace("{projected}", if projected { DEMO2_PROJECTED } else { "" })
}

/// PINNED — the projected spelling LOADS, and finds no row. §7.3's S1 flipped its load
/// verdict: the citation used to type `top`'s column at `Wrap`'s own `T` and refuse the
/// return the author wrote (`expected Wrap[T = ?X], got Wrap[T = ?T]`); it now reads the
/// bracket's `X`. At run time the relation is still EMPTY — the causes are
/// `demo2_the_count_answers_zero`'s — so `.head` raises `empty_stream`. The row the whole
/// case flips to is `wrap(red())` under `ByHeat` and `wrap(blue())` under `ByName`.
#[test]
fn demo2_the_projected_spelling_loads_and_finds_no_row() {
    let mut interp = crate::common::interp_for(&demo2(true));
    let err = interp
        .call("wi5g28a.demo2.Driver.topHeat", &[])
        .expect_err("PINNED: the relation is still empty; if a row comes back, flip this row");
    match &err {
        anthill_core::eval::EvalError::Raised { payload } => {
            let raised = sort_named(interp.kb(), payload);
            assert!(
                raised.ends_with(".empty_stream"),
                "`.head` of an empty relation raises `empty_stream`, got `{raised}`",
            );
        }
        other => panic!("expected a raised `empty_stream`, got {other:?}"),
    }
}

/// PINNED — a SILENT WRONG ANSWER. `countAt` loads, runs, and answers `0` under both
/// providers, where the answer is `1` under each. MEASURED 2026-09-24, and more than one
/// thing is missing, so this row is flipped only by the LAST of them: nothing carries the
/// caller's `Score` dictionary or `X`'s domain into `top`'s clause (§7.3 S2, S3), a
/// rule-body operation call whose argument is still unbound answers nothing instead of
/// waiting for the generator the sweep appends after it (WI-20260924-35E14), and a
/// clause's `require` answers nothing when its only provider is a WITNESS sort
/// (WI-20260924-DG57J).
#[test]
fn demo2_the_count_answers_zero() {
    for entry in ["countHeat", "countName"] {
        let mut interp = crate::common::interp_for(&demo2(false));
        match interp.call(&format!("wi5g28a.demo2.Driver.{entry}"), &[]) {
            Ok(Value::Int(n)) => assert_eq!(
                n, 0,
                "PINNED: {entry} answers 0 today where the design answers 1. If it now \
                 answers 1, §7.3's S2 and S3, 35E14 and DG57J have all landed — flip this row, and \
                 assert the projected spelling's row by value (`wrap(red())` / \
                 `wrap(blue())`)",
            ),
            other => panic!("{entry}: expected an Int64, got {other:?}"),
        }
    }
}
