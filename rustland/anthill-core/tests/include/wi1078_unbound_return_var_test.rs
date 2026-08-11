//! WI-1078 — a NAMED logical variable in a RETURN is existential too, unless the SIGNATURE
//! binds it. The exemption WI-1063 shipped keyed on the SPELLING; this keys on the signature.
//!
//! WI-1063 made a return's unwritten slot existential and opens it to a fresh rigid at every
//! use. Its call-side narrowing reads only an ANONYMOUS carrier as unwritten, which left its
//! own headline exploit alive under a two-character edit — `-> Stream[T = Int64, E = ?E]`
//! loaded while `E = ?` and the omitted form were refused, and `{Error}` reached a slot
//! declaring `E = {}`. `docs/kernel-language.md` §"Sort composition" says both spellings
//! express existential quantification and that a name buys only binding *across the term*, so
//! the exemption had no rule behind it — a divergence, not a decision.
//!
//! ## The rule, and it is about the SIGNATURE rather than the variable
//!
//! A variable the declaration also uses somewhere the CALLER supplies or instantiates is an
//! ordinary universal and must stay flexible; a variable used ONLY in the return is the
//! existential the polarity rule describes. THREE binders count — a PARAMETER type, the
//! operation's own `[A]`, and a `requires` bound — and each has a row below. The declared
//! EFFECTS are not a fourth: a row the operation incurs is on the same side of the arrow as
//! the return, so it binds nothing.
//!
//! THE ENCLOSING SORT'S PARAMETERS WERE A FOURTH AND ARE NOT, which is the one thing here that
//! was decided by a measurement contradicting the design. They looked necessary — `to_pair(h:
//! Holder) -> Pair[A = T, B = T]` names `T` in no parameter type — and the entry cost zero
//! tests when backed out, so it was read directly: a sort parameter written in a type is a
//! `Ref` to its symbol, never a `Var::Global`, and that return reaches the opening with
//! `vars_in_result = []`. Unreachable by construction, not merely unexercised, so it is gone;
//! [`the_enclosing_sorts_parameter_is_threaded_from_the_receiver`] holds the behaviour.
//!
//! ## The NAME still buys sharing — that is the half of the spelling that was real
//!
//! `?` is fresh per occurrence and keeps its per-SLOT mint. A named variable is opened ONCE
//! PER CALL and shared by every slot it appears in, so `mkpair() -> Pair[A = ?t, B = ?t]`
//! opens to `Pair[A = ρ, B = ρ]` and still says its components agree —
//! [`the_tie_survives_the_opening`] drives exactly that, against a two-variable control that
//! must not.
//!
//! ## THE CORPUS REACHES THIS ZERO TIMES — so this file is its only coverage
//!
//! Counted at the mint over all six loadable tiers (`rustland/anthill-stl/anthill`,
//! `rustland/anthill-todo/anthill`, `rustland/anthill-cpp-gen/anthill`, `examples/`,
//! `anthill-todo/`, `anthill-testcases/` — the stdlib rides along with each), the opening
//! fires **zero** times and every tier loads with byte-identical fact and rule totals. Over
//! the workspace suite AS IT STOOD BEFORE THIS FILE it fires exactly **once**:
//! `test.wi1063.named.mk_named`, the row in `wi1063_existential_return_test` that pinned the
//! exemption, which this ticket rewrites to the opposite verdict. So "the corpus is clean" is
//! evidence that nothing broke and NOT evidence that anything works — every claim below is
//! driven here or it is not driven at all.
//!
//! ## `empty` DID NOT HAVE TO MOVE, which the ticket predicted it would
//!
//! `LogicalStream.empty() -> LogicalStream[?A]` was WI-1063's stated justification for the
//! exemption, and the ticket expected this rule to bite it. It does not, and the reason is
//! worth keeping: `empty` is a member of the sort its return names, so the return is a SELF
//! reference and `SlotPosition::CallResult` never opens one at all (WI-1063's §3 parametricity
//! tie) — the same hatch that carries `List.empty`. The named variable was never what was
//! holding it up. Driven from two sides: [`a_self_sort_return_is_not_opened_in_either_spelling`]
//! here, and `wi1076_self_representing_spec_carrier_test::mplus_unifies_an_empty_stream_with_-
//! a_non_empty_one`, which calls `empty()` for real and stays green.
//!
//! ## What fails when each piece is backed out — DRIVEN, one revert each, whole suite per row
//!
//! | revert | cost |
//! |---|---|
//! | the whole rule (`unbound_return_var_openings` returns an empty map) | **6**: `wi1063_…::every_spelling_of_an_unbound_return_slot_opens`, plus this file's [`the_headline_a_named_row_variable_is_opened_at_the_consumer`], [`the_four_return_spellings_agree`], [`a_named_variable_only_in_the_return_is_opened_for_a_data_parameter_too`], [`the_bare_nullary_name_and_the_eta_lift_open_it_too`], [`the_tie_survives_the_opening`] |
//! | PARAMETERS dropped from the bound set | **2**: [`a_signature_bound_variable_is_left_flexible`] and `wi186_free_standing_parametric_test::make_pair_free_standing_parametric_returns_pair` |
//! | the op's own `[A]` dropped | **16**, the widest: [`an_operation_type_parameter_is_not_opened`] plus WI-204 (×3), WI-236 (×4), WI-270 (×2), WI-427 (×3), WI-734 and two `wi204_smoke` rows |
//! | `requires` dropped | **1**: [`a_requires_bound_binds_its_variable`] |
//! | candidates read off the CALL's result instead of the DECLARED return | **1**: `wi714_relation_reference_test::wi714_cross_sort_rule_body_subgoal` (`expected List[T = Int64], got List[T = ?x]`) — and [`an_eliminated_projection_is_not_a_candidate`], once rebuilt on the cross-sort form that reproduces it |
//! | the mint keyed per SLOT instead of per VARIABLE | **3**: [`the_tie_survives_the_opening`] on the VERDICT, plus `wi1063_…::every_spelling_…` and [`a_named_variable_…_data_parameter_too`] on the DIAGNOSTIC — a per-slot rigid is named after the SLOT (`?T`), so the message stops naming the variable the author wrote (`?A`) |
//! | the ENCLOSING SORT's parameters dropped | **0** — which is why that entry is not in the code; see above |
//!
//! Each was run alone against the whole `anthill-core` suite. Two rows here pass under EVERY
//! revert, by design, and say so at their own sites:
//! [`a_self_sort_return_is_not_opened_in_either_spelling`] and
//! [`the_enclosing_sorts_parameter_is_threaded_from_the_receiver`]. They are non-regressions
//! and boundary records, not measurements of this rule.
//!
//! REFERENCE: WI-1063 (the polarity rule, the call as mint site, and the ANONYMOUS-only
//! exemption this ticket retires); WI-1061/WI-1059 (the parameter polarity); WI-1079 (the
//! `PolyType` binder layer that makes "bound" structural rather than a signature scan);
//! `docs/kernel-language.md` §"In a RETURN the quantifier flips to ∃" and §"Sort composition".

use crate::wi1012_static_supplier_tie_test::refusal;

/// Every row below hands its producer's result to `takes_pure`, which demands the EMPTY row.
const PRE: &str = "namespace test.wi1078.rows\n\
    \x20 import anthill.prelude.{Int64, Stream, Error, List}\n\
    \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n";

fn rows(decl: &str) -> String {
    format!("{PRE}{decl}end\n")
}

/// THE HEADLINE. `widen_named` writes its row as a NAMED variable used nowhere else in the
/// signature, packs `{Error}` into it, and the consumer demands `{}`. Refused at the CONSUMER
/// — `takes_pure`'s parameter, where the opening happens — and NOT at the producer, whose body
/// is correct as written: an existential's body exhibits one witness.
///
/// Both halves are asserted together because either alone is satisfiable by the wrong fix, and
/// the `got` side must carry the skolem so the row cannot pass on an unrelated refusal.
///
/// CONTROL: on main the whole chain LOADS — this is WI-1063's headline exploit with `E = ?E`
/// written where the refused program omitted the slot, and it was the two-character edit that
/// bought it. `refusal` panics there.
#[test]
fn the_headline_a_named_row_variable_is_opened_at_the_consumer() {
    let msg = refusal(&rows(
        " operation widen_named(s: Stream[T = Int64, E = {Error}]) \
         -> Stream[T = Int64, E = ?E] = s\n\
         \x20 operation exploit(s: Stream[T = Int64, E = {Error}]) -> Int64 = \
         takes_pure(widen_named(s))\n",
    ));
    assert!(
        msg.contains("takes_pure.s") && msg.contains("E = ?E"),
        "a named row variable used only in the return is the existential the polarity rule \
         describes, opened at the use: {msg}",
    );
    assert!(
        !msg.contains("widen_named.return"),
        "the PRODUCER packs a witness and is correct as written — refusing it is the universal \
         reading, which is the wrong quantifier in a positive position: {msg}",
    );
}

/// ALL FOUR SPELLINGS OF ONE RETURN AGREE, which is what the ticket is for: WI-1063 kept three
/// of them and let the fourth through. The omitted slot, the explicit `?` and the named `?E`
/// are all refused at the CONSUMER; a named variable that the BODY contradicts is refused
/// earlier still, at the DECLARATION, and that row is what says which way to fix the other
/// three — the body check already reads a named return variable as universally quantified.
///
/// WHY THE FIRST THREE ARE REFUSED AT THE CALL AND NOT AT THE DECLARATION, since the ticket
/// left the choice open: a body-LESS declaration has no body to check, and `widen_*` here does
/// have one only incidentally. The call is the only site both forms share, and it is where
/// WI-1063 already mints. [`a_named_variable_only_in_the_return_is_opened_for_a_data_parameter_too`]
/// holds the body-less half.
///
/// CONTROL: the `?E` row is the one that changes — it loads on main. The other three are
/// WI-1063's verdicts and are here to show they are UNCHANGED, not to measure this rule.
#[test]
fn the_four_return_spellings_agree() {
    for (label, ret) in [
        ("omitted", "Stream[T = Int64]"),
        ("anonymous", "Stream[T = Int64, E = ?]"),
        ("named", "Stream[T = Int64, E = ?E]"),
    ] {
        let msg = refusal(&rows(&format!(
            " operation widen_it(s: Stream[T = Int64, E = {{Error}}]) -> {ret} = s\n\
             \x20 operation exploit(s: Stream[T = Int64, E = {{Error}}]) -> Int64 = \
             takes_pure(widen_it(s))\n"
        )));
        assert!(
            msg.contains("takes_pure.s") && !msg.contains("widen_it.return"),
            "the `{label}` spelling must open at the consumer like the other two: {msg}",
        );
    }
    // The fourth: a named variable the BODY contradicts. Refused at the declaration, by the
    // return check — the body has an `Int64` list and cannot have one good for EVERY element.
    let decl = refusal(&rows(" operation mk_ints() -> List[T = ?A] = cons(1, nil())\n"));
    assert!(
        decl.contains("mk_ints.return") && decl.contains("List[T = ?A]"),
        "a named return variable the body contradicts is refused at the DECLARATION, and that \
         asymmetry is what says the other three belong at the call: {decl}",
    );
}

/// The same rule where the producer is BODY-LESS and the parameter is a DATA one rather than
/// an effect row — the shape a spec declaration takes. Nothing packs a witness here, so this is
/// the rule read as erasure: the caller may not assume the element type the signature never
/// wrote down.
///
/// CONTROL: loads on main.
#[test]
fn a_named_variable_only_in_the_return_is_opened_for_a_data_parameter_too() {
    let msg = refusal(&rows(
        " operation mk_list() -> List[T = ?A]\n\
         \x20 operation want_ints(l: List[T = Int64]) -> Int64\n\
         \x20 operation use_it() -> Int64 = want_ints(mk_list())\n",
    ));
    assert!(
        msg.contains("want_ints.l") && msg.contains("List[T = ?A]"),
        "a body-less declaration's unbound return variable is opened at the use too: {msg}",
    );
}

/// A variable the signature uses in a PARAMETER as well is ordinary parametric polymorphism —
/// the caller instantiates it, and this call's argument is what pins it. This is the corpus
/// shape the rule had to separate out (`interleave(a: LogicalStream[T = ?A, E = ?E], …) ->
/// LogicalStream[T = ?A, E = ?E]`), and opening it would hand every caller a row nothing can
/// bind.
///
/// CONTROL: loads on main too — it is a non-regression for the headline. What it measures is
/// the BOUND half: drop parameter types from the bound set and this row fails, taking
/// `wi1076_…::mplus_unifies_an_empty_stream_with_a_non_empty_one` with it.
#[test]
fn a_signature_bound_variable_is_left_flexible() {
    crate::common::load_kb_with(&rows(
        " operation midentity(a: Stream[T = ?A, E = ?E]) -> Stream[T = ?A, E = ?E]\n\
         \x20 operation use_it(s: Stream[T = Int64, E = {}]) -> Int64 = \
         takes_pure(midentity(s))\n",
    ));
}

/// An operation's OWN `[A]` binder in a return is the CALLER's to instantiate (§5.6), so it
/// must not open — and it is the spelling the ticket names as the replacement for an unbound
/// return variable. Driven at TWO element types in ONE program, which is the property a single
/// call cannot distinguish from a lucky skolem.
///
/// CONTROL: loads on main. Drop `op.type_params` from the bound set and both calls fail.
#[test]
fn an_operation_type_parameter_is_not_opened() {
    crate::common::load_kb_with(
        "namespace test.wi1078.optp\n\
         \x20 import anthill.prelude.{Int64, String, List}\n\
         \x20 operation mk3[A]() -> List[T = A]\n\
         \x20 operation want_ints(l: List[T = Int64]) -> Int64\n\
         \x20 operation want_strs(l: List[T = String]) -> Int64\n\
         \x20 operation use_i() -> Int64 = want_ints(mk3())\n\
         \x20 operation use_s() -> Int64 = want_strs(mk3())\n\
         end\n",
    );
}

/// A `requires` clause BINDS its variable: `-> List[T = ?C] requires Eq[T = ?C]` is a universal
/// with a bound, which is exactly the binder-plus-bound shape WI-1079 records as `PolyType`.
/// Reading it as existential would refuse the dispatch the clause exists to drive.
///
/// CONTROL: loads on main. Drop `op.requires` from the bound set and this row fails at
/// `want_ints.l`.
#[test]
fn a_requires_bound_binds_its_variable() {
    crate::common::load_kb_with(
        "namespace test.wi1078.req\n\
         \x20 import anthill.prelude.{Int64, List, Eq}\n\
         \x20 operation mk_eq() -> List[T = ?C] requires Eq[T = ?C]\n\
         \x20 operation want_ints(l: List[T = Int64]) -> Int64\n\
         \x20 operation use_it() -> Int64 = want_ints(mk_eq())\n\
         end\n",
    );
}

/// THE ENCLOSING SORT'S PARAMETER NEEDED NO ENTRY IN THE BOUND SET, and this row exists
/// because the first cut gave it one. `to_pair(h: Holder) -> Pair[A = T, B = T]` mentions `T`
/// in no parameter TYPE — `Holder` is written bare — so it looks exactly like the unbound case
/// the rule opens. It is not one, and not because the bound set excuses it: a sort parameter
/// written in a type is a `Ref` to its own symbol, never a `Var::Global`, so it is not a
/// variable this rule can see. Read directly at the call, the result is `Pair[A = T, B = T]`
/// with `vars_in_result = []`.
///
/// WHAT THIS ROW ASSERTS IS THE BEHAVIOUR, NOT THE ENTRY, since the entry is gone. Both halves
/// run: the receiver's `T` reaches the result (an `Int64` holder yields an `Int64` pair), and
/// a `String` holder is REFUSED naming `Pair[A = String, B = String]`. A skolemized `T` would
/// fail the first half; a `T` dropped or re-minted would fail the second by naming something
/// other than the receiver's element.
///
/// CONTROL: both halves pass on main — this is a non-regression, and it stayed green under the
/// back-out that removed the sort-parameter entry, which is how that entry was found to be
/// unreachable. It measures the threading, not this rule.
#[test]
fn the_enclosing_sorts_parameter_is_threaded_from_the_receiver() {
    const SORTPARAM: &str = "namespace test.wi1078.sortparam\n\
        \x20 import anthill.prelude.{Int64, String, Pair}\n\
        \x20 sort Holder\n\
        \x20   sort T = ?\n\
        \x20   entity holder(v: T)\n\
        \x20   operation to_pair(h: Holder) -> Pair[A = T, B = T]\n\
        \x20 end\n\
        \x20 operation want_ints(p: Pair[A = Int64, B = Int64]) -> Int64\n\
        \x20 operation use_it(h: Holder[T = Int64]) -> Int64 = want_ints(Holder.to_pair(h))\n\
        end\n";
    crate::common::load_kb_with(SORTPARAM);
    let wrong = refusal(
        &SORTPARAM
            .replace("sortparam", "sortparam2")
            .replace("h: Holder[T = Int64]", "h: Holder[T = String]"),
    );
    assert!(
        wrong.contains("want_ints.p") && wrong.contains("Pair[A = String, B = String]"),
        "the receiver's element must reach the result — a skolem or a dropped slot would name \
         something else here: {wrong}",
    );
}

/// THE NAME BUYS SHARING, and this is the row that spends it. `mk_same() -> Pair[A = ?t, B =
/// ?t]` states that its two components AGREE; the opening must keep that, so both slots take
/// ONE ρ. `needs_same(p: Pair[A = ?u, B = ?u])` is the consumer that can tell: `?u` binds to ρ
/// twice consistently and the call is accepted, while two independently-minted rigids would
/// make `?u` two different things.
///
/// Rendering cannot decide this — two distinct rigids named `t` both print `?t` (the trap
/// WI-1063 names as "these render alike but are not the same type") — which is why the
/// discriminator is a consumer that must UNIFY them rather than an assertion on a message.
///
/// The second half is the control that keeps the first from being vacuous: `Pair[A = ?t, B =
/// ?s]` writes two DIFFERENT variables, and that call must be refused. It loads on main (where
/// neither variable is opened and both stay flexible), so it also shows the tie is now really
/// enforced rather than satisfied by everything unifying with everything.
#[test]
fn the_tie_survives_the_opening() {
    const TIED: &str = "namespace test.wi1078.tie\n\
        \x20 import anthill.prelude.{Int64, Pair}\n\
        \x20 operation mk_same() -> Pair[A = ?t, B = ?t]\n\
        \x20 operation needs_same(p: Pair[A = ?u, B = ?u]) -> Int64\n\
        \x20 operation use_it() -> Int64 = needs_same(mk_same())\n\
        end\n";
    crate::common::load_kb_with(TIED);
    let untied = refusal(&TIED.replace("B = ?t]", "B = ?s]").replace("tie\n", "untie\n"));
    assert!(
        untied.contains("needs_same.p"),
        "two DIFFERENT return variables do not agree, and the consumer that demands agreement \
         must say so — otherwise the first half measures nothing: {untied}",
    );
}

/// A SELF-sort return is not opened in EITHER spelling, and the two agreeing is the point: the
/// §3 parametricity tie is what a reference to the callee's own sort names, so `E = ?E` and an
/// omitted `E` are alike there exactly as they are now alike on a foreign one. This is the
/// hatch `LogicalStream.empty` and `List.empty` both ride, and it is why neither had to move.
///
/// BOTH HALVES LOAD, AND THE FIRST OF THEM LAUNDERS — this fixture hands `{Error}` to a
/// parameter declaring `E = {}` and is accepted, which is §8.1's headline exploit surviving on
/// the self side. It is asserted as a LOAD deliberately: the two spellings agreeing is what
/// proves the route belongs to the self gate (WI-1063's foreign-only scope) and not to a second
/// named-variable seam — if it were about the spelling, the halves would disagree. Closing it
/// is **WI-1082**, which also carries why the two fillers WI-1063 tried are both wrong and what
/// the untried third one is; when it lands, this row is rewritten to its verdict.
///
/// PASSES UNDER EVERY REVERT of this ticket, by design. It measures the boundary, not the rule.
#[test]
fn a_self_sort_return_is_not_opened_in_either_spelling() {
    const SELF: &str = "namespace test.wi1078.selfsort\n\
        \x20 import anthill.prelude.{Int64, Error}\n\
        \x20 sort MyStream\n\
        \x20   sort T = ?\n\
        \x20   effects E = ?\n\
        \x20   entity mystream\n\
        \x20   operation widen_self(s: MyStream[T = Int64, E = {Error}]) \
         -> MyStream[T = Int64, E = ?E] = s\n\
        \x20 end\n\
        \x20 operation takes_pure_s(s: MyStream[T = Int64, E = {}]) -> Int64\n\
        \x20 operation use_it(s: MyStream[T = Int64, E = {Error}]) -> Int64 = \
         takes_pure_s(MyStream.widen_self(s))\n\
        end\n";
    crate::common::load_kb_with(SELF);
    // The omitted spelling of the same return — `-> MyStream[T = Int64]`, WI-1063's row A on a
    // self reference. It loads too, and that agreement is the whole assertion.
    crate::common::load_kb_with(&SELF.replace(", E = ?E] = s", "] = s").replace("selfsort", "selfomit"));
}

/// The other two USE sites WI-1063 had to wire, read at the named spelling — a nullary
/// operation named WITHOUT parentheses, and the ETA lift. Each was a live hole for the
/// anonymous spelling and each is one for this spelling too; a rule that holds only on the
/// path the typer usually takes is not a rule.
///
/// CONTROL: both load on main.
#[test]
fn the_bare_nullary_name_and_the_eta_lift_open_it_too() {
    let bare = refusal(&rows(
        " operation mk_bare() -> Stream[T = Int64, E = ?E]\n\
         \x20 operation use_it() -> Int64 = takes_pure(mk_bare)\n",
    ));
    assert!(
        bare.contains("takes_pure.s") && bare.contains("E = ?E"),
        "the zero-arg-call reading of a bare nullary name is a USE and opens: {bare}",
    );
    let eta = refusal(&rows(
        " operation widen_named(s: Stream[T = Int64, E = {Error}]) \
         -> Stream[T = Int64, E = ?E] = s\n\
         \x20 operation apply_it(f: Function[A = Stream[T = Int64, E = {Error}], \
         B = Stream[T = Int64, E = {}]], s: Stream[T = Int64, E = {Error}]) -> Int64\n\
         \x20 operation use_it(s: Stream[T = Int64, E = {Error}]) -> Int64 = \
         apply_it(widen_named, s)\n",
    ));
    assert!(
        eta.contains("apply_it.f") && eta.contains("E = ?E"),
        "the eta arrow's RESULT is a use of the declared return and opens once per lift: {eta}",
    );
}

/// A variable that reaches the call's result through PROJECTION ELIMINATION is not a candidate,
/// because the author never wrote it in the return. `takeN(s: Stream, n: Int64) -> List[T =
/// s.T]` arrives at the opening as `List[T = ?x]` — `?x` being a variable of the RECEIVER's own
/// row schema, which appears in no parameter type of `takeN` — so reading candidates off the
/// call's result rather than off the declaration skolemizes the caller's element type.
///
/// IT TAKES THE CROSS-SORT FORM TO REPRODUCE, which is the whole reason this row is written
/// out rather than left to a citation. A single-sort `let r = S.q; r.takeN(5)` loads under BOTH
/// readings — it was the first fixture here and it measured nothing. The variable only survives
/// into the result when the drained rule's own body cites ANOTHER sort's rule as a subgoal, so
/// the two files are load-bearing.
///
/// CONTROL: loads on main, and on the first cut of this ticket it did not — candidates read off
/// the call's result refuse it at `rows.return` (`expected List[T = Int64], got List[T = ?x]`).
/// That back-out is measured, and `wi714_relation_reference_test::wi714_cross_sort_rule_body_-
/// subgoal` is the delivered test it was found through.
#[test]
fn an_eliminated_projection_is_not_a_candidate() {
    const F1: &str = "namespace test.wi1078.proj\n\
        \x20 import anthill.prelude.{Int64}\n\
        \x20 sort S\n\
        \x20   entity se(v: Int64)\n\
        \x20   rule q(?x) :- se(v: ?x)\n\
        \x20 end\n\
        \x20 fact se(v: 1)\n\
        end\n";
    const F2: &str = "namespace test.wi1078.proj\n\
        \x20 import anthill.prelude.{Int64, List, Error}\n\
        \x20 sort S2\n\
        \x20   entity s2e(w: Int64)\n\
        \x20   rule other(?x) :- s2e(w: ?x)\n\
        \x20   rule q2(?x) :- S.q(?x), other(?x)\n\
        \x20 end\n\
        \x20 fact s2e(w: 1)\n\
        \x20 operation rows() -> List[Int64] effects Error =\n\
        \x20   let r = S2.q2\n\
        \x20   r.takeN(5)\n\
        end\n";
    crate::common::try_load_kb_with_files(&[F1, F2])
        .unwrap_or_else(|errs| panic!("the receiver's own row variable must not be opened: {errs:?}"));
}
