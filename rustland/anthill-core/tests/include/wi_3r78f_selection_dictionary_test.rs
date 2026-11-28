//! WI-20261127-3R78F — a host asks, before any call, whether a call that selects a provider
//! for a spec can be built: `typing::dictionary_at_selection(kb, Spec, W, spec_args)` answers
//! with the dictionary a host's `Spec.op[Spec = W, …](…)` (`Interpreter::call_bracketed`) is
//! handed, or with the refusal that call makes — with no operation and no argument.
//!
//! WHO ASKS: anthill-traces runs a model, a carrier providing a spec, through the bracketed
//! call, and refuses at startup, by name, a carrier the call cannot use. Each of the
//! ticket's four shapes passes `sort_provides` and is refused at every call; and
//! `typing::resolve` on a goal built by hand from each requirement answered as the call did
//! on those shapes, but departs from it where the call's own goals are built otherwise (the
//! review's four). So the question is the CALL'S OWN CODE, shared with it and not rebuilt:
//! the bracket's reading and its selections' checks (`spec_dispatch_bracket` over
//! `seed_bracket_bindings` and `check_selections_at_slots`, in the slots a body-less spec
//! operation's call has, `push_sort_slots`) and the dispatch's pinned search
//! (`dispatch_dictionary`). One reading is its own, standing for the call's arguments: a
//! spec parameter the bracket leaves out, read from the witness's provisions where they all
//! say it alike.
//!
//! THE ROWS (`ROWS`) are carriers of one spec, `Keeps`, each asked and then called. Each row
//! asserts the verdict it is listed with AND that the call agrees: refused exactly where
//! the question fails, naming the goal the question names; run where it holds. A spec's own
//! bracket — its type arguments, a carrier parameter, a requirement of the spec selected —
//! is `the_spec_s_own_bracket_is_read_as_the_call_reads_it`, held to the calls the same way.
//!
//! BACK-OUT, measured on a binary of this file alone (each change made by hand, the file
//! run, the change undone; every row that departs is named, the loops collect them):
//!
//!  1. The bracket not read — the selection built by hand from the value's sort, the
//!     witness's own bracket still read: RED are `T2` (the ticket's (a)) and `Named`, each
//!     still FAILING but answered by the search ("provides no instance at these bindings")
//!     where the call refuses the selection — a check of "fails where the call is refused"
//!     alone passes them — and the spec test's two rows at `Two` written with a `T`.
//!  2. The selections' binding-precise half dropped from `spec_dispatch_bracket`: RED is the
//!     spec test's `One` at `[T = String]`, refused by the search where the call refuses the
//!     selection.
//!  3. The refusal of an unwritten parameter dropped: RED is the spec test's `Two` with `T`
//!     left out, answered by the search's "provides no instance at these bindings".
//!  4. The witness's own bracket dropped (the selection's `slots` and `args` emptied): RED are
//!     `BoxBad[T = Int64]` ("nothing fixes its `T`"), `NamedReq[D = Rival]` (the tie at `D`)
//!     and `NamedReq[D = Named]` (the tie at `D`, where the call names the slot's goal), and
//!     `a_witness_s_own_bracket_is_read_as_the_call_reads_it`.
//!  5. The search without the call's σ (`sigma: None`): every row GREEN. No goal here has a
//!     variable for σ to class, so the σ-precise and the coarse covers agree; it is passed
//!     because the call passes one, and is not measured by this file.
//!  6. The witness's provisions not read for an unwritten parameter: RED are the spec test's
//!     `One` with `T` left out, `LBox[A = Int64]` with `T` left out (read through `A`) and
//!     `Holder` at `Box` with `C` left out, each refused as unwritten where the call runs.
//!  7. The spec's own `requires` left out of the question's slots (the dispatch's alone): RED
//!     is the spec test's `Ranked` at `[Desc2 = DA]`, refused as a key naming nothing
//!     (`NoSuchTypeParam`) where the call takes it.
//!  8. The refusal of a `spec` that is no spec dropped: RED is the spec test's `Box` as the
//!     spec, told that the witness "does not provide pp.Box" — the wrong mistake named.
//!
//! GREEN EITHER WAY, by design: every other row, and
//! `a_named_slot_is_not_settled_by_the_default_resolve_takes` under all eight — its control
//! half asks `typing::resolve`, not the question, and its other half writes no bracket.

use anthill_core::eval::{EvalError, HostValue, Interpreter, Value};
use anthill_core::kb::typing::{
    dictionary_at_selection, resolve, DictionaryRefusal, ResolutionResult, ResolutionScope,
    ResolvedRequiresNode, SelectionRefusal, SortGoal, TypeError,
};
use anthill_core::kb::KnowledgeBase;

use crate::common::interp_for;

const SRC: &str = r#"
namespace pu
  import anthill.prelude.{Int64, Eq, Ord}
  sort Named
    entity named(n: Int64)
  end
  sort Keeps
    operation keep(n: Int64) -> Int64
  end
  sort Marker
  end

  -- A provider of `Keeps`, and one only of a provider of it.
  sort Mid
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 1
  end
  sort T2
    provides Mid
  end

  -- A provision's condition, unheld and held (`Named` has `Eq`, derived, and no `Ord`).
  sort CondBad
    provides Keeps :- Ord[T = Named]
    operation keep(n: Int64) -> Int64 = n + 2
  end
  sort CondGood
    provides Keeps :- Eq[T = Named]
    operation keep(n: Int64) -> Int64 = n + 3
  end

  -- A requirement of the carrier's own frame, unheld and held, and a refinement.
  sort ReqBad
    requires Ord[T = Named]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 4
  end
  sort ReqGood
    requires Eq[T = Named]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 5
  end
  sort ReqMarker
    requires Marker
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 6
  end

  -- A type parameter the frame's `requires` reads, and one nothing reads.
  sort BoxBad[T]
    requires Eq[T = T]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 7
  end
  sort BoxGood[T]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 8
  end

  -- An unconditional clause beside an unheld conditional one, and beside two equal ones
  -- (the review's (1): counting clauses against condition groups is what P5G39 fixed).
  sort Mixed
    provides Keeps :- Ord[T = Named]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 10
  end
  sort Alt
    provides Keeps :- Ord[T = Named]
    provides Keeps :- Ord[T = Named]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 11
  end

  -- A requirement leaving a parameter unwritten (the review's (2)): `Store[C = MemStore]`
  -- is asked at the `Key` `MemStore`'s provision says; `Store[Key = Named]` at none.
  sort Store
    sort C = ?
    sort Key = ?
    operation size(c: C) -> Int64
  end
  sort MemStore
    entity mem(n: Int64)
    provides Store[C = MemStore, Key = Int64]
    operation size(c: MemStore) -> Int64 = 0
  end
  sort OpenGood
    requires Store[C = MemStore]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 12
  end
  sort OpenBad
    requires Store[Key = Named]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 13
  end

  -- A requirement whose view binds an operation (the review's (3)): only a type
  -- parameter's key is a binding of the goal.
  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end
  operation namedCombine(x: Named, y: Named) -> Named = x
  operation otherCombine(x: Named, y: Named) -> Named = y
  namespace Named
    provides Combiner[T = Named, combine = namedCombine]
  end
  sort OpReqGood
    requires Combiner[T = Named, combine = namedCombine]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 14
  end
  sort OpReqOther
    requires Combiner[T = Named, combine = otherCombine]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 15
  end

  -- A named slot only a default would settle (the review's (4)): `Leaf` provides `Desc`
  -- itself, so it is the default among the two (058 §3.6), which an anonymous requirement
  -- takes and a named slot does not (`rung_for_dep`).
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Rival
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
  sort NamedReq
    requires D: Desc[T = Leaf]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 16
  end
  sort AnonReq
    requires Desc[T = Leaf]
    provides Keeps
    operation keep(n: Int64) -> Int64 = n + 17
  end
end
"#;

/// What a row is asked to answer.
#[derive(Debug, Clone, Copy)]
enum Verdict {
    /// The dictionary is built, its provider the row's carrier; the call runs, answering this.
    Holds(i64),
    /// The selection is refused: the carrier writes no provision of `Keeps` (058 §4.4 check 1).
    NotAProvider,
    /// The dictionary is not built: this goal does not resolve, and the hint says this.
    Unresolved(&'static str, &'static str),
    /// The dictionary is not built: two providers of this spec answer a goal of it.
    Tie(&'static str),
}

use Verdict::*;

/// A carrier, the bracket it is written with (`(parameter, sort)` pairs, qualified), and its
/// verdict. A row a back-out of the header turns red says so; the rest pass either way.
type Row = (
    &'static str,
    &'static [(&'static str, &'static str)],
    Verdict,
);

const ROWS: &[Row] = &[
    // Controls: a provider; the ticket's held forms.
    ("Mid", &[], Holds(2)),
    ("CondGood", &[], Holds(4)),
    ("ReqGood", &[], Holds(6)),
    ("ReqMarker", &[], Holds(7)),
    ("BoxGood", &[], Holds(9)),
    ("Mixed", &[], Holds(11)),
    // The ticket's four.
    ("T2", &[], NotAProvider), // RED under back-out 1
    (
        "CondBad",
        &[],
        Unresolved(
            "anthill.prelude.Ord[T = pu.Named]",
            "no impl provides anthill.prelude.Ord",
        ),
    ),
    (
        "ReqBad",
        &[],
        Unresolved(
            "anthill.prelude.Ord[T = pu.Named]",
            "no impl provides anthill.prelude.Ord",
        ),
    ),
    (
        "BoxBad",
        &[],
        Unresolved("pu.Keeps", "nothing fixes its `T`"),
    ),
    // A parameter the bracket fixes: answered at what it writes. RED under back-out 4.
    (
        "BoxBad",
        &[("pu.BoxBad.T", "anthill.prelude.Int64")],
        Holds(8),
    ),
    // The review's four.
    ("Alt", &[], Holds(12)),
    ("OpenGood", &[], Holds(13)),
    (
        "OpenBad",
        &[],
        Unresolved("pu.Store[Key = pu.Named]", "no impl provides pu.Store"),
    ),
    ("OpReqGood", &[], Holds(15)),
    ("OpReqOther", &[], Holds(16)),
    ("NamedReq", &[], Tie("pu.Desc")),
    ("AnonReq", &[], Holds(18)),
    // A named slot the bracket binds on the carrier. Both RED under back-out 4.
    ("NamedReq", &[("pu.NamedReq.D", "pu.Rival")], Holds(17)),
    (
        "NamedReq",
        &[("pu.NamedReq.D", "pu.Named")],
        Unresolved(
            "pu.Desc[T = pu.Leaf]",
            "binds slot `D` of `pu.NamedReq` to `pu.Named`",
        ),
    ),
    // A sort that provides nothing.
    ("Named", &[], NotAProvider), // RED under back-out 1
];

/// The type `base[p1 = a1, …]`, every name qualified.
fn applied(kb: &mut KnowledgeBase, base: &str, args: &[(&str, &str)]) -> Value {
    let b = kb
        .try_resolve_symbol(base)
        .unwrap_or_else(|| panic!("the sort `{base}`"));
    let base = kb.make_sort_ref(b);
    let pairs: Vec<_> = args
        .iter()
        .map(|(p, a)| {
            let p = kb
                .try_resolve_symbol(p)
                .unwrap_or_else(|| panic!("the parameter `{p}`"));
            let a = kb
                .try_resolve_symbol(a)
                .unwrap_or_else(|| panic!("the sort `{a}`"));
            (p, kb.make_sort_ref(a))
        })
        .collect();
    if pairs.is_empty() {
        return Value::term(base);
    }
    Value::term(kb.make_parameterized_type(base, &pairs))
}

/// The question and the call, for one row: the question's answer, and the call's.
fn ask_and_call(
    interp: &mut Interpreter,
    carrier: &str,
    args: &[(&str, &str)],
) -> (
    Result<ResolvedRequiresNode, SelectionRefusal>,
    Result<Value, EvalError>,
) {
    let ty = applied(interp.kb_mut(), &format!("pu.{carrier}"), args);
    let kb = interp.kb_mut();
    let spec = kb.try_resolve_symbol("pu.Keeps").expect("`Keeps`");
    let asked = dictionary_at_selection(kb, spec, &ty, &[]);
    let called = interp
        .call_bracketed(
            "pu.Keeps.keep",
            &[(Some("Keeps"), ty)],
            &[HostValue::from(Value::Int(1))],
        )
        .map(|h| h.value);
    (asked, called)
}

/// The call's refusal sentence, or why the row fails: the call ran.
fn refused(called: Result<Value, EvalError>) -> Result<String, String> {
    match called {
        Err(EvalError::HostCallRefused { detail, .. }) => Ok(detail),
        other => Err(format!(
            "the question fails, so the call must be refused; got {other:?}"
        )),
    }
}

/// One row, asked and called: `Err` names how it departs from its verdict.
fn check_row(interp: &mut Interpreter, (carrier, args, verdict): &Row) -> Result<(), String> {
    let (asked, called) = ask_and_call(interp, carrier, args);
    let kb = interp.kb();
    let holds = |ok: bool, why: String| if ok { Ok(()) } else { Err(why) };
    match (*verdict, asked) {
        (Holds(answer), Ok(tree)) => {
            let provider = match &tree {
                ResolvedRequiresNode::Leaf { impl_sort, .. }
                | ResolvedRequiresNode::Conditional { impl_sort, .. } => *impl_sort,
                other => return Err(format!("a dictionary at the carrier, not {other:?}")),
            };
            let provider = kb.qualified_name_of(provider);
            holds(
                provider == format!("pu.{carrier}"),
                format!("the dictionary's provider is the selected carrier, not {provider}"),
            )?;
            holds(
                matches!(called, Ok(Value::Int(n)) if n == answer),
                format!("the question holds, so the call runs the carrier's member ({answer}); got {called:?}"),
            )
        }
        // Check 1's refusal, not the binding-precise half's ("provides `Keeps`, but not at the
        // bindings"), which would tell a witness providing nothing that it provides the spec.
        (
            NotAProvider,
            Err(SelectionRefusal::Selection(
                e @ TypeError::WitnessDoesNotProvide {
                    witness,
                    at_bindings: false,
                    ..
                },
            )),
        ) => {
            let named = kb.qualified_name_of(witness).to_string();
            holds(
                named == format!("pu.{carrier}"),
                format!("the refusal names {named}"),
            )?;
            let says = format!("pu.{carrier} does not provide pu.Keeps");
            let text = e.format(kb);
            holds(
                text.contains(&says),
                format!("the question says `{says}`: {text}"),
            )?;
            let detail = refused(called)?;
            holds(
                detail.contains(&says),
                format!("the call's refusal says `{says}`: {detail}"),
            )
        }
        (
            Unresolved(goal, hint),
            Err(SelectionRefusal::Dictionary(DictionaryRefusal::Unresolved(failure))),
        ) => {
            holds(
                failure.goal_text == goal,
                format!("the question names `{goal}`: {failure:?}"),
            )?;
            holds(
                failure.hint.contains(hint),
                format!("the hint says `{hint}`: {failure:?}"),
            )?;
            let detail = refused(called)?;
            let names = format!("unresolved: {goal} ({}", failure.hint);
            holds(
                detail.contains(&names),
                format!("the call's refusal names the same goal and hint `{names}`: {detail}"),
            )
        }
        (Tie(spec), Err(SelectionRefusal::Dictionary(DictionaryRefusal::Ambiguous(tie)))) => {
            let tied = kb.qualified_name_of(tie.spec).to_string();
            holds(
                tied == spec,
                format!("the tie is at `{spec}`, not `{tied}`"),
            )?;
            let detail = refused(called)?;
            holds(
                detail.contains(&format!("instances provide `{spec}` (pu.Leaf, pu.Rival)")),
                format!("the call's refusal is the same tie: {detail}"),
            )
        }
        (verdict, asked) => Err(format!(
            "expected {verdict:?}; the question answered {asked:?}, the call {called:?}"
        )),
    }
}

/// DONE WHEN (1)–(3): each row's verdict, the question's and the call's — the ticket's four
/// failing, each naming the goal the call's refusal names; its held forms holding; the
/// review's four answered as the call answers them. Every row is checked and each that
/// departs is named, so a back-out reads its whole set.
#[test]
fn each_row_answers_as_the_bracketed_call_does() {
    let mut interp = interp_for(SRC);
    let departed: Vec<String> = ROWS
        .iter()
        .filter_map(|row| {
            check_row(&mut interp, row)
                .err()
                .map(|why| format!("{}{:?}: {why}", row.0, row.1))
        })
        .collect();
    assert!(
        departed.is_empty(),
        "rows that depart:\n{}",
        departed.join("\n")
    );
}

/// The review's (4), from the side of what a goal built by hand answers: `typing::resolve`
/// asked `Desc[T = Leaf]` takes the default, `Leaf`, as an unselected dispatch does — where
/// the dictionary build for a NAMED slot withholds it and the call is refused. The question
/// answers as the call does (`NamedReq` in `ROWS`); this is the control that the two
/// questions differ on this goal, so the row measures something.
#[test]
fn a_named_slot_is_not_settled_by_the_default_resolve_takes() {
    let mut interp = interp_for(SRC);
    let kb = interp.kb_mut();
    let desc = kb.try_resolve_symbol("pu.Desc").expect("`Desc`");
    let leaf = kb.try_resolve_symbol("pu.Leaf").expect("`Leaf`");
    let leaf_ty = Value::term(kb.make_sort_ref(leaf));
    let goal = SortGoal {
        spec_sort: desc,
        bindings: smallvec::smallvec![(kb.intern("T"), leaf_ty)],
        carrier: None,
        left_open: smallvec::SmallVec::new(),
    };
    let scope = ResolutionScope {
        available_requires: &[],
        sigma: None,
        pin: None,
        sub_goal_requires: &[],
    };
    match resolve(kb, &goal, &scope) {
        ResolutionResult::Resolved(ResolvedRequiresNode::Leaf { impl_sort, .. }) => {
            assert_eq!(kb.qualified_name_of(impl_sort), "pu.Leaf", "the default");
        }
        other => panic!("`resolve` takes the default at `Desc[T = Leaf]`; got {other:?}"),
    }
    let (asked, called) = ask_and_call(&mut interp, "NamedReq", &[]);
    assert!(
        matches!(
            asked,
            Err(SelectionRefusal::Dictionary(DictionaryRefusal::Ambiguous(
                _
            )))
        ),
        "the question withholds the default from the named slot: {asked:?}"
    );
    assert!(
        matches!(called, Err(EvalError::HostCallRefused { .. })),
        "so does the call: {called:?}"
    );
}

/// A bracket's value is read as the call reads it, its own bracket included: `NamedReq[D =
/// Rival]` selects `Rival` for the slot, `BoxBad[T = Int64]` fixes the parameter its frame
/// reads, and `NamedReq[D = Named]` is refused at the slot's goal, `Named` providing no
/// `Desc` — where the bare `NamedReq` ties. RED under back-out 4 of the header.
#[test]
fn a_witness_s_own_bracket_is_read_as_the_call_reads_it() {
    let mut interp = interp_for(SRC);
    for (carrier, args, holds) in [
        ("NamedReq", &[("pu.NamedReq.D", "pu.Rival")][..], true),
        (
            "BoxBad",
            &[("pu.BoxBad.T", "anthill.prelude.Int64")][..],
            true,
        ),
        ("NamedReq", &[("pu.NamedReq.D", "pu.Named")][..], false),
    ] {
        let (asked, called) = ask_and_call(&mut interp, carrier, args);
        if holds {
            assert!(asked.is_ok(), "{carrier}{args:?} holds: {asked:?}");
            assert!(
                called.is_ok(),
                "{carrier}{args:?}: the call runs: {called:?}"
            );
        } else {
            let Err(SelectionRefusal::Dictionary(DictionaryRefusal::Unresolved(failure))) = &asked
            else {
                panic!("{carrier}{args:?}: refused at the slot's goal; got {asked:?}");
            };
            assert!(
                failure
                    .hint
                    .contains("binds slot `D` of `pu.NamedReq` to `pu.Named`"),
                "{failure:?}"
            );
            assert!(
                called.is_err(),
                "{carrier}{args:?}: the call is refused: {called:?}"
            );
        }
    }
}

/// The spec's own bracket, read as the call reads it: `S[T]`'s argument written beside the
/// selection, as the call's arguments fix it (`S.f[S = W](5)` at `T = Int64`), by key or by
/// position; a witness providing `S` at another `T` refused at the selection, as the call is
/// ("not at the bindings this call … needs"), where one providing it at both holds at both.
///
/// An argument the bracket leaves out is read from the witness's provisions where they all
/// say it alike: `One` provides `S` at `T = Int64` alone, and every call at `One` runs there
/// (`S.g[S = One]()`, whose arguments fix no `T`, runs `One`'s member, 30); `Two` provides it
/// at two, and a call there runs at the `T` its arguments fix (`S.g[S = Two]()` is refused),
/// so the question refuses it naming `T`. A carrier parameter is one such argument:
/// `Box provides Holder[C = Box]` holds at `[Holder = Box]`, as `Holder.size[Holder =
/// Box](box(n: 1))` runs, and a witness's own parameter is read at what the bracket writes of
/// it (`LBox[A] provides S[T = A]` holds at `LBox[A = Int64]` and is refused bare). A spec that
/// receives on itself (`Shape.area(s: Shape)`) holds as
/// its call runs; and a key of a spec the spec requires selects for that requirement, as the
/// call's does (`[Desc2 = DA]`), a provider of nothing refused at the selection, as there.
///
/// RED under back-outs 1, 2, 3, 6, 7 and 8 of the header, each at the rows its comment names.
#[test]
fn the_spec_s_own_bracket_is_read_as_the_call_reads_it() {
    const SPEC_SRC: &str = r#"
namespace pp
  import anthill.prelude.{Int64, String}
  sort S
    sort T = ?
    operation f(x: T) -> Int64
    operation g() -> Int64
  end
  operation fInt(x: Int64) -> Int64 = 1
  operation fStr(x: String) -> Int64 = 2
  operation gInt() -> Int64 = 10
  operation gStr() -> Int64 = 20
  sort Two
    provides S[T = Int64, f = fInt, g = gInt]
    provides S[T = String, f = fStr, g = gStr]
  end
  sort One
    provides S[T = Int64]
    operation f(x: Int64) -> Int64 = 3
    operation g() -> Int64 = 30
  end
  sort LBox[A]
    provides S[T = A]
    operation f(x: A) -> Int64 = 5
    operation g() -> Int64 = 50
  end

  sort Holder
    sort C = ?
    operation size(c: C) -> Int64
  end
  sort Box
    entity box(n: Int64)
    provides Holder[C = Box]
    operation size(c: Box) -> Int64 = 4
  end

  sort Shape
    operation area(s: Shape) -> Int64
  end
  sort Sq
    entity sq(n: Int64)
    provides Shape
    operation area(s: Sq) -> Int64 = 9
  end

  sort Desc2
    sort T = ?
    operation d(x: T) -> Int64
  end
  sort DA
    provides Desc2[T = Int64]
    operation d(x: Int64) -> Int64 = 1
  end
  sort Ranked
    requires Desc2[T = Int64]
    operation rank(n: Int64) -> Int64
  end
  sort R1
    provides Ranked
    operation rank(n: Int64) -> Int64 = Desc2.d(n)
  end
end
"#;
    let mut interp = interp_for(SPEC_SRC);
    let ty = |interp: &mut Interpreter, qn: &str| crate::common::sort_type(interp.kb_mut(), qn);
    let int64 = ty(&mut interp, "anthill.prelude.Int64");
    let string = ty(&mut interp, "anthill.prelude.String");
    let ask = |interp: &mut Interpreter, spec: &str, w: &Value, args: &[(Option<&str>, Value)]| {
        let kb = interp.kb_mut();
        let spec = kb
            .try_resolve_symbol(&format!("pp.{spec}"))
            .expect("the spec");
        dictionary_at_selection(kb, spec, w, args)
    };
    let call =
        |interp: &mut Interpreter, op: &str, bracket: &[(Option<&str>, Value)], args: &[Value]| {
            let args: Vec<HostValue> = args.iter().cloned().map(HostValue::from).collect();
            interp
                .call_bracketed(&format!("pp.{op}"), bracket, &args)
                .map(|h| h.value)
        };
    let entity = |interp: &Interpreter, ctor: &str, n: i64| Value::Entity {
        functor: interp.kb().resolve_symbol(&format!("pp.{ctor}")),
        pos: vec![Value::Int(n)].into(),
        named: Vec::new().into(),
    };
    let one = ty(&mut interp, "pp.One");
    let two = ty(&mut interp, "pp.Two");
    let da = ty(&mut interp, "pp.DA");
    let lbox_int64 = applied(
        interp.kb_mut(),
        "pp.LBox",
        &[("pp.LBox.A", "anthill.prelude.Int64")],
    );
    let sq_value = entity(&interp, "Sq.sq", 1);
    let box_value = entity(&interp, "Box.box", 1);

    // Held, and the call at what the bracket writes runs. The question's witness is the call
    // bracket's first entry.
    let held: Vec<(
        &str,
        &str,
        Vec<(Option<&str>, Value)>,
        &str,
        Vec<(Option<&str>, Value)>,
        Vec<Value>,
        i64,
    )> = vec![
        (
            "S",
            "One",
            vec![(Some("T"), int64.clone())],
            "S.f",
            vec![(Some("S"), one.clone())],
            vec![Value::Int(5)],
            3,
        ),
        (
            "S",
            "One",
            vec![(None, int64.clone())],
            "S.f",
            vec![(Some("S"), one.clone())],
            vec![Value::Int(5)],
            3,
        ),
        // `T` read from `One`'s one provision (RED under back-out 6).
        (
            "S",
            "One",
            vec![],
            "S.g",
            vec![(Some("S"), one.clone())],
            vec![],
            30,
        ),
        // `Two` at a written `T` (both RED under back-out 1).
        (
            "S",
            "Two",
            vec![(Some("T"), int64.clone())],
            "S.f",
            vec![(Some("S"), two.clone())],
            vec![Value::Int(5)],
            1,
        ),
        (
            "S",
            "Two",
            vec![(Some("T"), string.clone())],
            "S.f",
            vec![(Some("S"), two.clone())],
            vec![Value::Str("x".into())],
            2,
        ),
        // `T` read through `LBox`'s own parameter, at what the bracket writes of it (RED
        // under back-out 6).
        (
            "S",
            "LBox[A = Int64]",
            vec![],
            "S.f",
            vec![(Some("S"), lbox_int64.clone())],
            vec![Value::Int(5)],
            5,
        ),
        // `C` read from `Box`'s provision (RED under back-out 6).
        (
            "Holder",
            "Box",
            vec![],
            "Holder.size",
            vec![(Some("Holder"), ty(&mut interp, "pp.Box"))],
            vec![box_value],
            4,
        ),
        (
            "Shape",
            "Sq",
            vec![],
            "Shape.area",
            vec![(Some("Shape"), ty(&mut interp, "pp.Sq"))],
            vec![sq_value],
            9,
        ),
        (
            "Ranked",
            "R1",
            vec![],
            "Ranked.rank",
            vec![(Some("Ranked"), ty(&mut interp, "pp.R1"))],
            vec![Value::Int(5)],
            1,
        ),
        // A key of a spec `Ranked` requires (RED under back-out 7).
        (
            "Ranked",
            "R1",
            vec![(Some("Desc2"), da.clone())],
            "Ranked.rank",
            vec![
                (Some("Ranked"), ty(&mut interp, "pp.R1")),
                (Some("Desc2"), da.clone()),
            ],
            vec![Value::Int(5)],
            1,
        ),
    ];
    let mut departed: Vec<String> = Vec::new();
    for (spec, w, args, op, bracket, values, answer) in held {
        let asked = ask(&mut interp, spec, &bracket[0].1, &args);
        if asked.is_err() {
            departed.push(format!("{spec} at {w}{args:?} holds: {asked:?}"));
        }
        let called = call(&mut interp, op, &bracket, &values);
        if !matches!(called, Ok(Value::Int(n)) if n == answer) {
            departed.push(format!("{op} at {w}: the call runs ({answer}): {called:?}"));
        }
    }
    assert!(
        departed.is_empty(),
        "rows that depart:\n{}",
        departed.join("\n")
    );

    // Refused at the selection, in the call's words: `One` at `T = String` (its binding-precise
    // half, RED under back-out 2) and a key of a required spec naming a provider of nothing.
    let not_at_bindings = "pp.One provides pp.S, but not at the bindings this call to";
    let not_a_provider = "pp.Sq does not provide pp.Desc2";
    let sq = ty(&mut interp, "pp.Sq");
    let r1 = ty(&mut interp, "pp.R1");
    for (spec, w, args, op, bracket, values, said) in [
        (
            "S",
            "One",
            vec![(Some("T"), string.clone())],
            "S.f",
            vec![(Some("S"), one.clone())],
            vec![Value::Str("x".into())],
            not_at_bindings,
        ),
        (
            "Ranked",
            "R1",
            vec![(Some("Desc2"), sq.clone())],
            "Ranked.rank",
            vec![(Some("Ranked"), r1), (Some("Desc2"), sq)],
            vec![Value::Int(5)],
            not_a_provider,
        ),
    ] {
        let asked = ask(&mut interp, spec, &bracket[0].1, &args);
        let Err(SelectionRefusal::Selection(e)) = &asked else {
            panic!("{spec} at {w}{args:?} is refused at the selection; got {asked:?}");
        };
        let text = e.format(interp.kb());
        assert!(text.contains(said), "the question says `{said}`: {text}");
        match call(&mut interp, op, &bracket, &values) {
            Err(EvalError::HostCallRefused { detail, .. }) => {
                assert!(
                    detail.contains(said),
                    "the call's refusal says `{said}`: {detail}"
                )
            }
            other => panic!("{op} at {w}{bracket:?} is refused; got {other:?}"),
        }
    }

    // `T` at `Two`, said apart by its two provisions and written by nothing: refused by name
    // (RED under back-out 3), where the call whose arguments fix no `T` is refused too.
    // So is `T` at the bare `LBox`, whose provision says it at a parameter the bracket does
    // not write.
    let lbox = ty(&mut interp, "pp.LBox");
    for (w, ty) in [("Two", &two), ("LBox", &lbox)] {
        match ask(&mut interp, "S", ty, &[]) {
            Err(SelectionRefusal::ParameterUnwritten { param, .. }) => {
                assert_eq!(interp.kb().qualified_name_of(param), "pp.S.T", "{w}")
            }
            other => panic!("`{w}` with `T` unwritten is refused naming it; got {other:?}"),
        }
    }
    let g_two = call(&mut interp, "S.g", &[(Some("S"), two.clone())], &[]);
    assert!(
        matches!(g_two, Err(EvalError::HostCallRefused { .. })),
        "`S.g[S = Two]()` is refused: {g_two:?}"
    );
    // A call whose arguments fix no `T` is the operation's to answer, the question holding:
    // `S.g[S = One]()` runs `One`'s member (above); `S.g[S = LBox[A = Int64]]()` is refused,
    // where every call at `LBox[A = Int64]` that fixes `T` runs at the `Int64` the question
    // reads (`S.f(5)` above; `S.g[S = LBox[A = Int64], T = Int64]()`).
    let g_lbox = call(&mut interp, "S.g", &[(Some("S"), lbox_int64.clone())], &[]);
    assert!(
        matches!(g_lbox, Err(EvalError::HostCallRefused { .. })),
        "`S.g[S = LBox[A = Int64]]()` is refused: {g_lbox:?}"
    );
    let g_lbox_at = call(
        &mut interp,
        "S.g",
        &[(Some("S"), lbox_int64.clone()), (Some("T"), int64.clone())],
        &[],
    );
    assert!(
        matches!(g_lbox_at, Ok(Value::Int(50))),
        "`S.g[S = LBox[A = Int64], T = Int64]()` runs: {g_lbox_at:?}"
    );

    // What no provider provides is no spec: a sort with constructors, an operation (RED under
    // back-out 8).
    for no_spec in ["Box", "fInt"] {
        match ask(&mut interp, no_spec, &two, &[]) {
            Err(SelectionRefusal::NotASpec { spec }) => {
                assert_eq!(interp.kb().qualified_name_of(spec), format!("pp.{no_spec}"))
            }
            other => panic!("`{no_spec}` is refused as no spec; got {other:?}"),
        }
    }
}
