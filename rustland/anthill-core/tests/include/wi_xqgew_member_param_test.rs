//! WI-20261006-XQGEW — a spec's member written in a signature is a type parameter with no
//! name of its own, and nothing may take the bare member's name for it.
//!
//! `Spec.Member` in an operation's signature is a fresh type parameter under `requires
//! Spec[Member = P]` (§5.4). The loader named its variable by the interned bare member,
//! `E` — the symbol the enclosing sort's own `E`, a bracket's, and another spec's member
//! are named by too. Two readers answered by that name:
//!
//!  * A TYPE DIAGNOSTIC printed `?E`. `effects {Tagger.E}` was reported as `expected
//!    declared: [?E]`, and `Tagger.E` beside `Other.E` as `[?E, ?E]`; the guardians budget
//!    read `[External, ?E, Error]` for `effects {External, Llm.E, Error}`.
//!  * A CALL'S BRACKET matched it. `Holder` declaring `sort E = ?` and `pick(self: Self,
//!    x: X.C) -> X.E`: `Holder.pick[E = String](hold(v: "s"), b(n: 7))` bound `X.E` and was
//!    refused as returning a `String`; `Holder.pick[E = Int64](…)` over the same holder of
//!    a `String` loaded and answered 7; and the receiver spelling `Holder[E = …].pick(…)`,
//!    which the specification calls the same call, gave the other verdict both times
//!    (MEASURED on the parent commit; found by the user's question, 2026-10-06).
//!
//! THE RULE NOW. The parameter's name is a symbol of its own that reads as the member, with
//! the head it was written with recorded for it (`KnowledgeBase::mint_member_param_name`).
//! Every variable standing for the parameter carries the name — the loader's, a body's
//! rigid, the copy an operation used as a value is instantiated at — so it is printed as
//! written wherever it is shown (`Tagger.E`, `Llm.E`, an alias's `PS.E`), and a call's
//! bracket does not name it: a key matches by identity, which the name shares with nothing,
//! and a positional counts the parameters the declaration writes (user's decision,
//! 2026-10-06). Where a refusal's repair would be a clause or a slot over the parameter,
//! a member's is told to be written in the bracket instead: the first does not cover
//! (WI-20261006-P962X), and the second has no spelling.
//!
//! NOT HERE, by the user's decision the same day, each a ticket of its own:
//!
//!  * A member the signature does NOT name (`Other.E` in the ticket's `both`) is no
//!    parameter at all: it is read in the body as a free variable, prints `?_`, and takes
//!    any type (WI-20261006-GVGSQ). [`a_members_parameter_is_declared_by_its_spelling`]
//!    asserts the declared half of that program's refusal and says nothing of the other.
//!  * A `requires` clause over a member the signature names is not supplied at a call, nor
//!    read as covering in the body (WI-20261006-P962X).
//!  * A member written through a dotted head (`X.SX.E`) is not the sugar
//!    (WI-20261006-728RW); [`two_nested_specs_members_run_and_are_told_apart`] names the
//!    nested specs through an import.
//!
//! A refusal row asserts a LOAD verdict naming what is refused; a row that runs asserts the
//! value.
//!
//! P962X supersedes the historical bracket-only repair notes below: clauses over
//! signature members now cover and forward. The four affected tests advise clauses.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ───────────────────────────────
//!
//! EACH PART backed out present-but-wrong, APPLIED AND RUN over this file's 25 rows, the 67
//! of the three modules whose expectations moved with it (`wi_zbwmc_provision_narrowing_
//! test`, `wi_f3fyj_value_in_type_binding_test`, `n01py_witness_provision_subtype_test`),
//! `guardians_test`'s 67 and the layer's row
//! (`kb::layer::tests::spgbp_a_layer_minted_member_still_prints_as_written_after_the_
//! discard`) — 160, green before each. A row of this file is named; another module's is
//! counted.
//!
//!  1. THE NAME MINTED WITH NOTHING RECORDED FOR IT (`mint_member_param_name` without its
//!     insert). 30 FAIL: 20 of this file — every row but the three controls and the two
//!     that turn on a key alone, [`a_bracket_key_is_the_sorts_parameter_and_not_a_members`]
//!     and [`every_e_at_once`], which a name of its own carries by itself — and 10 of the
//!     three modules (`zbwmc` 7, `f3fyj` 2, `n01py` 1). 3 of `guardians_test`: the two that
//!     read the budget, and `an_external_send_is_refused_by_the_conditional_permission`,
//!     which reads the row a candidate is held to. And the layer's row.
//!  2. THE NAME INTERNED, AS THE PARENT COMMIT HAD IT (`intern` for `intern_unique`, and
//!     nothing recorded). 32 FAIL: the 30 of (1) and the two key rows. With it
//!     `total[E = {Modify[k]}](m)` LOADS, which is what `n01py`'s row records as lost.
//!  3. A MEMBER'S NAME RE-INTERNED FOR ITS RIGID (`fresh_rigid_named`). 19 FAIL:
//!     [`a_members_parameter_is_declared_by_its_spelling`],
//!     [`two_specs_members_of_one_name_are_told_apart`],
//!     [`a_body_is_shown_the_member_it_was_handed`],
//!     [`a_member_through_an_alias_is_printed_as_the_alias`],
//!     [`a_parameter_written_by_two_spellings_is_printed_by_the_first`],
//!     [`an_override_is_shown_the_specs_member`] (its second program: "the spec's `?C`"),
//!     [`two_nested_specs_members_run_and_are_told_apart`],
//!     [`a_named_slot_bound_to_a_member_is_told_what_can_be_written`],
//!     [`a_construction_over_a_member_is_told_the_spelling_that_works`],
//!     [`every_member_of_the_spec_moves_to_the_bracket`] (the row its second program is
//!     held to), and 9 of `zbwmc` (7) and `f3fyj` (2); and the example's
//!     `an_external_send_…`. The rows that read the loader's variable or a copy of it
//!     pass: the declared row read back, the function value, the forward and its later
//!     binding, the own clause, the no-join and unconstrained refusals, the bracket rows.
//!  4. NOTHING PRINTED BY THE SPELLING (`member_param_spelling` answering `None`). 29 FAIL:
//!     the 30 of (1) but [`a_written_parameter_beside_a_member_is_bound_as_before`], whose
//!     refusal is the count; and the example's three and the layer's row.
//!  5. A PARAMETER NAMED BY ITS KEY'S TEXT (`type_param_display_name` without the member).
//!     7 FAIL: [`a_parameter_two_arguments_disagree_on_is_named`],
//!     [`what_a_missing_provision_would_say_is_named`],
//!     [`a_forward_over_a_member_is_told_the_spelling_that_works`],
//!     [`a_member_in_a_later_binding_takes_the_members_repair`],
//!     [`a_construction_over_a_member_is_told_the_spelling_that_works`],
//!     [`an_unconstrained_member_is_named_and_not_advised_a_bracket`], and `n01py`'s.
//!  6. A MEMBER'S PARAMETER LEFT IN THE BRACKET'S LIST (`op_info::bracket_type_params`
//!     unfiltered). 2 FAIL, the positionals: [`no_bracket_names_a_members_parameter`] and
//!     [`a_written_parameter_beside_a_member_is_bound_as_before`]. A key does not reach it
//!     either way — that is (2)'s.
//!  7. A CLAUSE OVER A MEMBER TOLD TO BE DECLARED (`CallerRigidCarrier::repair` without
//!     its member branch). 3 FAIL:
//!     [`a_forward_over_a_member_is_told_the_spelling_that_works`],
//!     [`a_member_in_a_later_binding_takes_the_members_repair`] and
//!     [`every_member_of_the_spec_moves_to_the_bracket`].
//!  8. AN UNCONSTRAINED MEMBER ADVISED THE BRACKET (`unconstrained_type_param_text`). 1
//!     FAILS: [`an_unconstrained_member_is_named_and_not_advised_a_bracket`].
//!  9. A BRACKET REFUSAL SILENT ABOUT MEMBERS (`members_no_bracket_names`). 1 FAILS:
//!     [`no_bracket_names_a_members_parameter`].
//! 10. A MEMBER'S OWN VARIABLE PRINTED `?` IN A CLAUSE (`format_term_for_goal` without the
//!     arm for it). 1 FAILS: [`a_callers_own_clause_is_stated_with_the_member`].
//! 11. A MEMBER REACHED THROUGH AN ALIAS PRINTED BY THE SORT THE ALIAS STANDS FOR (the spec
//!     recorded in place of `written`). 2 FAIL:
//!     [`a_member_through_an_alias_is_printed_as_the_alias`] and
//!     [`a_parameter_written_by_two_spellings_is_printed_by_the_first`].
//! 12. THE RECORD ROLLED BACK WITH A LAYER (`member_param_heads` among the scoped fields).
//!     1 FAILS: the layer's row.
//! 13. A NAMED SLOT'S MEMBER TOLD TO DECLARE A SLOT ON IT (`UntiedForward`'s `member`
//!     dropped), or NAMED BY ITS LAST SEGMENT in the advice (`short` taken of the
//!     rendering). 1 FAILS, either way:
//!     [`a_named_slot_bound_to_a_member_is_told_what_can_be_written`].
//! 14. THE MEMBER'S REPAIR TAKEN ON THE CARRIER ALONE (`caller_rigid_carrier` reading the
//!     first of the clause's parameters), or THE CLAUSE SENT WHERE THE CARRIER IS DECLARED
//!     (`declare_on` left the carrier's). 1 FAILS, either way:
//!     [`a_member_in_a_later_binding_takes_the_members_repair`] — its first program, and
//!     its third.
//! 15. A SORT'S REQUIREMENT OVER A MEMBER GIVEN THE NO-ROUTE ADVICE (`dep_member_param`
//!     answering `None`). 1 FAILS:
//!     [`a_construction_over_a_member_is_told_the_spelling_that_works`].
//! 16. A KEY OF THE MEMBER'S WHOLE SPELLING NOT TAKEN FOR IT (`members_no_bracket_names`
//!     matching the bare name only). 1 FAILS: [`no_bracket_names_a_members_parameter`].
//! 17. NO BRACKET SPELLING SAID (`member_param_bracket_spelling` answering `None`). 5 FAIL,
//!     the rows of its three readers: (7)'s three, (13)'s and (15)'s. With the sentence
//!     kept and "every other member … goes the same way" cut from it, 1 FAILS:
//!     [`every_member_of_the_spec_moves_to_the_bracket`].
//!
//! PASS EITHER WAY, by design — the controls: [`a_written_parameter_prints_as_before`],
//! [`a_bracket_key_reaches_a_sort_parameter_of_another_name`] and
//! [`two_members_of_one_name_run_each_through_its_own_requirement`]. And inside rows that
//! do fail: every half that RUNS (the alias row's 1100, the nested row's 11, the
//! bracket-less `eo(1, b(n: 7))`, the two spellings' 1, and each program a refusal
//! advises, written out — 50, 51, 7, 7, 50), the two receiver-spelling calls of the key
//! row, the first three calls of [`a_written_parameter_beside_a_member_is_bound_as_before`],
//! and the half about a parameter declared by name in the unconstrained, forward,
//! named-slot, construction and bracket-refusal rows.
//!
//! NOT DRIVEN, and why. `op_info::declared_type_param_var` leaves a member out of "the
//! bracket declared it" as the bracket's own list does; its one reader asks it of the
//! subject of a projection off an operation's parameter, and the program that puts a
//! member of the subject's name beside one — `mk(x: Tagger.C, k: C.K) -> C ensures KV[C, K
//! = String]` — loads either way (MEASURED, and no row of the 160 fails). `like_named_
//! unknowns` names a rigid through the same function as the walk, and no program puts two
//! rigids of one member spelling on the two sides of one mismatch: a body has one rigid
//! per member, and an override check one per parameter of the spec's operation.

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, run_int64};

// ── fixtures ──────────────────────────────────────────────────────────────────────────

/// Two specs, each over a carrier `C` with a row `E`, and `A`, which provides both purely.
const TWO_SPECS: &str = r#"
  sort Tagger
    sort C = ?
    effects E = ?
    operation tag(self: C) -> Int64 effects {E}
  end

  sort Other
    sort C = ?
    effects E = ?
    operation oth(self: C) -> Int64 effects {E}
  end

  sort A
    entity a
    provides Tagger[C = A, E = {}]
    operation tag(self: A) -> Int64 = 1
    provides Other[C = A, E = {}]
    operation oth(self: A) -> Int64 = 100
  end
"#;

/// An operation that incurs `Error`, for a body that must exceed a row made of members.
const FAILS: &str = "  operation fails() -> Int64 effects {Error}\n";

/// A spec whose member is named `E` and is a TYPE, with `B` providing it at `Int64`: the
/// member a sort's own `E` shares its name with.
const TYPED_SPEC: &str = r#"
  sort X
    sort C = ?
    sort E = ?
    operation get(self: C) -> E
  end

  sort B
    entity b(n: Int64)
    provides X[C = B, E = Int64]
    operation get(self: B) -> Int64 = self.n
  end
"#;

/// A spec over one parameter, required of a type by name.
const TAG_SPEC: &str = "  sort Tag\n    sort T = ?\n    operation tagOf(x: T) -> Int64\n  end\n";

/// `g`, which requires `Tag` of its parameter and reads it.
const G: &str = "  operation g[P](y: P) -> Int64 requires Tag[T = P] = Tag.tagOf(y)\n";

/// `TA`, which provides `Tagger` and `Tag` — the carrier a rewrite a refusal advises is run
/// at, over [`TWO_SPECS`] and [`TAG_SPEC`].
const TAGGED: &str = r#"
  sort TA
    entity ta
    provides Tagger[C = TA, E = {}]
    operation tag(self: TA) -> Int64 = 1
    provides Tag[T = TA]
    operation tagOf(x: TA) -> Int64 = 50
  end
"#;

/// A sort that requires `Tag` of its parameter, built by its one constructor.
const BOX: &str = "  sort Box\n    sort T = ?\n    requires Tag[T = T]\n    entity box(v: T)\n  end\n";

fn program(ns: &str, fixtures: &[&str], body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, String, Bool, Error}}\n{}\n{body}\nend\n",
        fixtures.concat()
    )
}

// ── printed as it was written ─────────────────────────────────────────────────────────

/// THE TICKET'S PROGRAM. `both` declares `{Tagger.E}` and its body incurs more; the row it
/// is held to is reported as the author wrote it. Was `expected declared: [?E]`.
///
/// The undeclared half of this refusal is a member the signature does not name, which is
/// no parameter today and prints as an unknown; this row says nothing of it.
#[test]
fn a_members_parameter_is_declared_by_its_spelling() {
    let ns = "xqgew.both";
    let errs = load_errors_of(&program(
        ns,
        &[TWO_SPECS],
        "  operation both(x: Tagger.C, y: Other.C) -> Int64 effects {Tagger.E} =\n    \
         Tagger.tag(x) + Other.oth(y)",
    ));
    assert_refused_naming(
        &errs,
        &["both.effects (op-effects): expected declared: [Tagger.E], got undeclared effect"],
        "the declared row names the member",
    );
}

/// TWO SPECS WITH A MEMBER OF ONE NAME ARE TOLD APART. Both rows are `E`, and both printed
/// `?E`: `expected declared: [?E, ?E]`.
#[test]
fn two_specs_members_of_one_name_are_told_apart() {
    let ns = "xqgew.apart";
    let errs = load_errors_of(&program(
        ns,
        &[TWO_SPECS, FAILS],
        "  operation both(x: Tagger.C, y: Other.C) -> Int64 effects {Tagger.E, Other.E} = fails()",
    ));
    assert_refused_naming(
        &errs,
        &["expected declared: [Tagger.E, Other.E], got undeclared effect: Error"],
        "each member by its own spec",
    );
}

/// A BODY'S TYPE DIAGNOSTIC names the member too: the value handed in is a `Tagger.C`. Was
/// `expected Int64, got ?C`.
#[test]
fn a_body_is_shown_the_member_it_was_handed() {
    let ns = "xqgew.body";
    let errs = load_errors_of(&program(
        ns,
        &[TWO_SPECS],
        "  operation bad(x: Tagger.C) -> Int64 = x",
    ));
    assert_refused_naming(
        &errs,
        &["bad.return (op-return): expected Int64, got Tagger.C"],
        "the parameter's type is the member",
    );
}

/// CONTROL — a parameter the author wrote in a bracket has a name, and prints by it as it
/// always did. Passes with or without the change by design.
#[test]
fn a_written_parameter_prints_as_before() {
    let ns = "xqgew.written";
    let errs = load_errors_of(&program(
        ns,
        &[],
        "  operation total[P, El](x: P, y: El) -> Int64 = x",
    ));
    assert_refused_naming(
        &errs,
        &["total.return (op-return): expected Int64, got ?P"],
        "a bracket parameter is `?P`",
    );
}

/// WHAT IS READ BACK OF A DECLARED ROW is the member as well — the reading the guardians
/// checker reports its budget by (`spec_budget`: each of an operation's declared effects
/// through `type_display_name_value`). No body is checked here, so the variable printed is
/// the loader's own and not a rigid.
#[test]
fn the_declared_row_reads_back_as_written() {
    let ns = "xqgew.readback";
    let kb = load_kb_with(&program(
        ns,
        &[TWO_SPECS],
        "  operation one(x: Tagger.C) -> Int64 effects {Tagger.E, Error}",
    ));
    let one = kb
        .try_resolve_symbol(&format!("{ns}.one"))
        .expect("`one` is declared");
    let row: Vec<String> = anthill_core::kb::op_info::lookup_operation_info(&kb, one)
        .expect("`one` has a signature")
        .effects
        .iter()
        .map(|e| anthill_core::kb::typing::type_display_name_value(&kb, e))
        .collect();
    assert_eq!(row, vec!["Tagger.E", "Error"]);
}

/// THROUGH AN ALIAS, THE ALIAS — what the signature has. `P.S` and `Q.S` are two specs of one
/// short name, and through `sort PS = P.S` / `sort QS = Q.S` their members printed by the
/// sort each alias stands for: `[S.E, S.E]`, and `got S.C` (MEASURED, this change's first
/// cut). An alias that fixes a parameter (`S2A = Spec2[A = WIS]`) is printed the same way.
#[test]
fn a_member_through_an_alias_is_printed_as_the_alias() {
    let ns = "xqgew.alias";
    let fixtures = r#"
  sort P
    sort S
      sort C = ?
      effects E = ?
      operation ps(self: C) -> Int64 effects {E}
    end
  end

  sort Q
    sort S
      sort C = ?
      effects E = ?
      operation qs(self: C) -> Int64 effects {E}
    end
  end

  sort PS = P.S
  sort QS = Q.S

  sort PQ
    entity pq
    provides P.S[C = PQ, E = {}]
    operation ps(self: PQ) -> Int64 = 100
    provides Q.S[C = PQ, E = {}]
    operation qs(self: PQ) -> Int64 = 1000
  end

  sort WIS
    entity wis(n: Int64)
  end

  sort Spec2
    sort A = ?
    sort B = ?
    operation pair(a: A, b: B) -> Int64
  end

  sort S2A = Spec2[A = WIS]
"#;
    let signature = "operation two(x: PS.C, y: QS.C) -> Int64 effects {PS.E, QS.E}";
    assert_eq!(
        run_int64(
            &program(
                ns,
                &[fixtures],
                &format!(
                    "  {signature} = P.S.ps(x) + Q.S.qs(y)\n  \
                     operation go() -> Int64 = two(pq(), pq())"
                ),
            ),
            &format!("{ns}.go")
        ),
        Ok(1100),
        "the two members are two parameters, each supplied by its own provision"
    );
    let errs = load_errors_of(&program(
        ns,
        &[fixtures, FAILS],
        &format!("  {signature} = fails()"),
    ));
    assert_refused_naming(
        &errs,
        &["expected declared: [PS.E, QS.E], got undeclared effect: Error"],
        "each member by the alias it was written through",
    );
    let errs = load_errors_of(&program(
        ns,
        &[fixtures],
        "  operation useB(a: WIS, b: S2A.B) -> Int64 = b",
    ));
    assert_refused_naming(
        &errs,
        &["useB.return (op-return): expected Int64, got S2A.B"],
        "an alias that fixes a parameter is the spelling too",
    );
}

/// ONE PARAMETER WRITTEN BY TWO SPELLINGS IS PRINTED BY ONE. `TG` is `Tagger`, so `TG.C`
/// and `Tagger.C` in one signature are one parameter — `same` returns its `Tagger.C` as a
/// `TG.C` and runs — and a parameter is printed one way for as long as it lives: by the
/// spelling the loader met first, which is the return type's, then the parameters' in
/// order. So `y`, written `TG.C`, is reported as the `Tagger.C` it is.
///
/// The half that runs passes with or without the change. Both refusals fail with the
/// spelling not recorded or not carried to a rigid — (1) to (4) of the ledger — and the
/// first with the spec recorded for the alias, (11).
#[test]
fn a_parameter_written_by_two_spellings_is_printed_by_the_first() {
    let ns = "xqgew.two_spellings";
    let with = |body: &str| {
        program(
            ns,
            &[TWO_SPECS, "  sort TG = Tagger\n"],
            body,
        )
    };
    assert_eq!(
        run_int64(
            &with(
                "  operation same(x: Tagger.C) -> TG.C = x\n  \
                 operation go() -> Int64 = Tagger.tag(same(a()))"
            ),
            &format!("{ns}.go")
        ),
        Ok(1),
        "the two spellings are one parameter"
    );
    assert_refused_naming(
        &load_errors_of(&with("  operation h(x: Tagger.C) -> TG.C = 5")),
        &["h.return (op-return): expected TG.C, got Int64"],
        "the return type's spelling is met first",
    );
    assert_refused_naming(
        &load_errors_of(&with("  operation h(x: Tagger.C, y: TG.C) -> Int64 = y")),
        &["h.return (op-return): expected Int64, got Tagger.C"],
        "then the parameters', in order",
    );
}

/// AN OVERRIDE IS COMPARED WITH THE SPEC'S MEMBER, and told so by its spelling: `Job.run`
/// takes a `Tagger.C` and the member written for `J` takes an `Int64`. Was "the spec's `?C`
/// admits arguments the member's `Int64` does not".
///
/// THE SIGNATURE AS DECLARED is the loader's variable; the type a RETURN is compared at is
/// the rigid the comparison makes of it ("any type"), and is the same member. With the
/// spelling not carried to a rigid the second program reads "the spec's `?C`" beside "The
/// spec declares `mk(self: J) -> Tagger.C`".
#[test]
fn an_override_is_shown_the_specs_member() {
    let ns = "xqgew.overriding";
    let job = |spec_op: &str, member: &str| {
        program(
            ns,
            &[TWO_SPECS],
            &format!(
                "  sort Job\n    sort C = ?\n    operation {spec_op}\n  end\n\n  \
                 sort J\n    entity j\n    provides Job[C = J]\n    operation {member}\n  end"
            ),
        )
    };
    let errs = load_errors_of(&job(
        "run(self: C, t: Tagger.C) -> Int64",
        "run(self: J, t: Int64) -> Int64 = 1",
    ));
    assert_refused_naming(
        &errs,
        &[
            "the spec's `Tagger.C` admits arguments the member's `Int64` does not",
            "The spec declares `run(self: J, t: Tagger.C) -> Int64`",
        ],
        "the spec's parameter is the member",
    );
    let errs = load_errors_of(&job(
        "mk(self: C) -> Tagger.C",
        "mk(self: J) -> Int64 = 1",
    ));
    assert_refused_naming(
        &errs,
        &[
            "the member returns `Int64`, which is not a subtype of the spec's `Tagger.C`",
            "The spec declares `mk(self: J) -> Tagger.C`",
        ],
        "the spec's result is the member",
    );
}

/// A FUNCTION VALUE CARRIES THE MEMBER TOO. An operation used as a value is instantiated
/// at a copy of each of its parameters, and the copy is the same member: `tagIt` handed
/// where a two-parameter function is wanted is shown as `Tagger.C -> Int64`. Was `?C ->
/// Int64`, beside a body that printed the same parameter `Tagger.C`.
#[test]
fn an_operation_used_as_a_value_is_shown_its_member() {
    let ns = "xqgew.value";
    let errs = load_errors_of(&program(
        ns,
        &[TWO_SPECS],
        "  operation tagIt(x: Tagger.C) -> Int64 effects {Tagger.E} = Tagger.tag(x)\n  \
         operation app2(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(1, 2)\n  \
         operation go() -> Int64 = app2(tagIt)",
    ));
    assert_refused_naming(
        &errs,
        &["got a 1-parameter function Tagger.C -> Int64"],
        "the value's parameter is the member",
    );
}

/// A PARAMETER TWO ARGUMENTS DISAGREE ON IS NAMED AS IT IS WRITTEN. `same` takes two
/// values of one `Tagger.C`, and `A` and `A2` are two sorts. Was "no common type for type
/// parameter `C` of `same`" — which `Other.C` in the signature would be too.
#[test]
fn a_parameter_two_arguments_disagree_on_is_named() {
    let ns = "xqgew.no_join";
    let errs = load_errors_of(&program(
        ns,
        &[TWO_SPECS],
        "  sort A2\n    entity a2\n    provides Tagger[C = A2, E = {}]\n    \
         operation tag(self: A2) -> Int64 = 2\n  end\n\n  \
         operation same(x: Tagger.C, y: Tagger.C) -> Int64 effects {Tagger.E} = Tagger.tag(x)\n  \
         operation go() -> Int64 = same(a(), a2())",
    ));
    assert_refused_naming(
        &errs,
        &[
            "expected one type for `Tagger.C`",
            "no common type for type parameter `Tagger.C` of `same`: A (x), A2 (y)",
        ],
        "the parameter the two arguments bind",
    );
}

/// WHAT A MISSING PROVISION WOULD HAVE SAID is named the same way. `Plain` provides no
/// `Other`, so nothing says `Other.E`. Was "nothing says the `E` this requirement
/// determines", beside a signature that has two members called `E`.
#[test]
fn what_a_missing_provision_would_say_is_named() {
    let ns = "xqgew.unprovided";
    let errs = load_errors_of(&program(
        ns,
        &[TWO_SPECS],
        "  sort Plain\n    entity plain\n  end\n\n  \
         operation both(x: Tagger.C, y: Other.C) -> Int64 effects {Tagger.E, Other.E} = 1\n  \
         operation go() -> Int64 = both(a(), plain())",
    ));
    assert_refused_naming(
        &errs,
        &[
            &format!("`{ns}.Other[C = Plain]` cannot be supplied for call to `{ns}.both`"),
            "so nothing says the `Other.E` this requirement determines",
        ],
        "the member the requirement would have fixed",
    );
}

/// P962X: a missing clause is advised over the member, and that clause forwards. The bracket form remains an execution control.
#[test]
fn a_forward_over_a_member_is_told_the_spelling_that_works() {
    let ns = "xqgew.forward";
    let refused = format!("requirement `{ns}.Tag[T = Tagger.C]` cannot be supplied for call to `{ns}.g`");
    let errs = load_errors_of(&program(
        ns,
        &[TWO_SPECS, TAG_SPEC, G],
        "  operation f(x: Tagger.C) -> Int64 = g(x)",
    ));
    assert_refused_naming(
        &errs,
        &[
            &refused,
            "its carrier is `Tagger.C`",
            &format!("Declare `requires {ns}.Tag[T = Tagger.C]` on `{ns}.f`"),
        ],
        "P962X: advise the clause over the member",
    );
    assert_eq!(
        run_int64(
            &program(
                ns,
                &[TWO_SPECS, TAG_SPEC, TAGGED, G],
                "  operation f[P](x: P) -> Int64 requires Tagger[C = P], Tag[T = P] = g(x)\n  \
                 operation go() -> Int64 = f(ta())",
            ),
            &format!("{ns}.go")
        ),
        Ok(50),
        "the spelling the refusal advises runs"
    );
    assert_eq!(run_int64(&program(ns, &[TWO_SPECS, TAG_SPEC, TAGGED, G],
        "operation f(x: Tagger.C) -> Int64 requires Tag[T = Tagger.C] = g(x)\noperation go() -> Int64 = f(ta())"), &format!("{ns}.go")), Ok(50), "P962X: the member clause forwards");

    let errs = load_errors_of(&program(
        ns,
        &[TAG_SPEC, G],
        "  operation mid[U](y: U) -> Int64 = g(y)",
    ));
    assert_refused_naming(
        &errs,
        &[
            "its carrier is `U`, a type parameter of the CALLING operation",
            &format!("Declare `requires {ns}.Tag[T = U]` on `{ns}.mid` so the evidence is passed in"),
        ],
        "a parameter declared by name is told to declare the clause",
    );
}

/// P962X: requiring Tag over Tagger.C keeps the signature instance. Moving one member into a separate bracket clause still creates a different instance.
#[test]
fn every_member_of_the_spec_moves_to_the_bracket() {
    let ns = "xqgew.every_member";
    let with = |body: &str| program(ns, &[TWO_SPECS, TAG_SPEC, TAGGED, G], body);
    assert_refused_naming(
        &load_errors_of(&with(
            "  operation f(x: Tagger.C) -> Int64 effects {Tagger.E} = Tagger.tag(x) + g(x)",
        )),
        &[&format!(
            "Declare `requires {ns}.Tag[T = Tagger.C]` on `{ns}.f`"
        )],
        "the members move together",
    );
    assert_refused_naming(
        &load_errors_of(&with(
            "  operation f[P](x: P) -> Int64 effects {Tagger.E} \
             requires Tagger[C = P], Tag[T = P] = Tagger.tag(x) + g(x)",
        )),
        &["f.effects (op-effects): expected declared: [Tagger.E], got undeclared effect"],
        "one member moved alone is two instances of the spec",
    );
    assert_eq!(
        run_int64(
            &with(
                "  operation f[P, Q](x: P) -> Int64 effects {Q} \
                 requires Tagger[C = P, E = Q], Tag[T = P] = Tagger.tag(x) + g(x)\n  \
                 operation go() -> Int64 = f(ta())"
            ),
            &format!("{ns}.go")
        ),
        Ok(51),
        "every member in the one clause"
    );
}

/// P962X: a member in any binding is expressible in the advised clause, which belongs to the operation that introduced that member.
#[test]
fn a_member_in_a_later_binding_takes_the_members_repair() {
    let ns = "xqgew.later_binding";
    let pair = r#"
  sort Pair2
    sort A = ?
    sort B = ?
    operation both(a: A, b: B) -> Int64
  end

  sort PA
    entity pa
    provides Tagger[C = PA, E = {}]
    operation tag(self: PA) -> Int64 = 1
    provides Pair2[A = PA, B = PA]
    operation both(a: PA, b: PA) -> Int64 = 7
  end

  operation g2[P, Q](y: P, z: Q) -> Int64 requires Pair2[A = P, B = Q] = Pair2.both(y, z)
"#;
    let errs = load_errors_of(&program(
        ns,
        &[TWO_SPECS, pair],
        "  operation f[U](x: U, w: Tagger.C) -> Int64 = g2(x, w)",
    ));
    assert_refused_naming(
        &errs,
        &[
            &format!("requirement `{ns}.Pair2[A = U, B = Tagger.C]` cannot be supplied"),
            "its carrier is `U`",
            &format!("Declare `requires {ns}.Pair2[A = U, B = Tagger.C]` on `{ns}.f`"),
        ],
        "P962X: a later member binding can be named by its clause",
    );
    assert_eq!(
        run_int64(
            &program(
                ns,
                &[TWO_SPECS, pair],
                "  operation f[U, P](x: U, w: P) -> Int64 \
                 requires Tagger[C = P], Pair2[A = U, B = P] = g2(x, w)\n  \
                 operation go() -> Int64 = f(pa(), pa())",
            ),
            &format!("{ns}.go")
        ),
        Ok(7),
        "the spelling the refusal advises runs"
    );

    // The carrier a SORT's parameter: the clause a declared parameter is told goes on the
    // sort, and the member's bracket is still the operation's.
    let holder = |m: &str| {
        program(
            ns,
            &[TWO_SPECS, pair],
            &format!(
                "  sort Holder\n    sort T = ?\n    entity hold(v: T)\n    operation m{m} = \
                 g2(self.v, w)\n  end\n  \
                 operation go() -> Int64 = Holder.m(hold(v: pa()), pa())"
            ),
        )
    };
    assert_refused_naming(
        &load_errors_of(&holder("(self: Self, w: Tagger.C) -> Int64")),
        &[
            "its carrier is `T`, a type parameter of the CALLING operation",
            &format!("Declare `requires {ns}.Pair2[A = T, B = Tagger.C]` on `{ns}.Holder.m`"),
        ],
        "the operation's bracket, whatever declares the carrier",
    );
    assert_eq!(
        run_int64(
            &holder(
                "[P](self: Self, w: P) -> Int64 requires Tagger[C = P], Pair2[A = T, B = P]"
            ),
            &format!("{ns}.go")
        ),
        Ok(7),
        "the spelling the refusal advises runs"
    );
}

/// P962X: a construction over a member is repaired by a clause over that member. A named parameter keeps the existing slot advice.
#[test]
fn a_construction_over_a_member_is_told_the_spelling_that_works() {
    let ns = "xqgew.construction";
    let build = |signature: &str, result: &str| {
        program(
            ns,
            &[TWO_SPECS, TAG_SPEC, TAGGED, BOX],
            &format!(
                "  operation f{signature} =\n    let b = box(v: x)\n    {result}\n  \
                 operation go() -> Int64 = 0"
            ),
        )
    };
    let refused = format!(
        "requirement `{ns}.Tag[T = {ns}.Box.T]` of `{ns}.Box` cannot be supplied for the \
         construction `{ns}.Box.box`"
    );
    let errs = load_errors_of(&build("(x: Tagger.C) -> Int64", "1"));
    assert_refused_naming(
        &errs,
        &[
            &refused,
            &format!("declare `requires {ns}.Tag[T = Tagger.C]` on the enclosing operation"),
        ],
        "the member, and the repair that loads",
    );
    assert!(
        !errs.iter().any(|e| e.contains("declare a requirement slot for it")),
        "a member's parameter has no declaration to put a slot on: {errs:#?}"
    );

    let errs = load_errors_of(&build("[P](x: P) -> Int64", "1"));
    assert_refused_naming(
        &errs,
        &[
            &refused,
            "nothing in the enclosing scope supplies it: declare a requirement slot for it on \
             the enclosing SORT",
        ],
        "a parameter declared by name is told to declare the slot",
    );
    assert!(
        !errs.iter().any(|e| e.contains("member")),
        "a declared parameter is told nothing of members: {errs:#?}"
    );

    assert_eq!(
        run_int64(
            &program(
                ns,
                &[TWO_SPECS, TAG_SPEC, TAGGED, BOX],
                "  operation f[P](x: P) -> Int64 requires Tagger[C = P], Tag[T = P] =\n    \
                 let b = box(v: x)\n    Tag.tagOf(b.v)\n  \
                 operation go() -> Int64 = f(ta())",
            ),
            &format!("{ns}.go")
        ),
        Ok(50),
        "the spelling the refusal advises runs"
    );
}

/// A NAMED SLOT BOUND TO A MEMBER IS TOLD WHAT CAN BE WRITTEN. `add` types its set's
/// ordering slot `O` by `Tagger.C`, and nothing in scope holds an ordering for it. The
/// parameter is named by its spelling in the advice as in the sentence before it — the
/// advice took the last segment, `C` — and is not told to declare a slot on it, `requires
/// Tagger.C: …` being no binder a program can write.
///
/// CONTROL, in the same row: a parameter the operation declares is told to declare the
/// slot, as before. Passes with or without the change.
#[test]
fn a_named_slot_bound_to_a_member_is_told_what_can_be_written() {
    let ns = "xqgew.slot";
    let add = |bracket: &str, order: &str| {
        program(
            ns,
            &[TWO_SPECS],
            &format!(
                "  import anthill.prelude.{{SortedSet}}\n  \
                 operation add{bracket}(s: SortedSet[T = Int64, O = {order}], x: Int64) \
                 -> SortedSet[T = Int64, O = {order}] = SortedSet.insert(s, x)"
            ),
        )
    };
    let errs = load_errors_of(&add("", "Tagger.C"));
    assert_refused_naming(
        &errs,
        &[
            "named slot `O` of `anthill.prelude.SortedSet` is bound to `Tagger.C`",
            "holds a dictionary FOR `Tagger.C`",
            "`Tagger.C` is a member's parameter and has no declaration to put a slot on",
            "write it in the enclosing operation's bracket — a parameter `P` under `requires \
             Tagger[C = P]`, with `P` where the signature has `Tagger.C`",
            "and declare the slot on it (`requires P: <the spec above>`)",
        ],
        "the member by its spelling, and a repair that can be written",
    );
    assert!(
        !errs.iter().any(|e| e.contains("requires Tagger.C:")),
        "a member's parameter is given no slot of its own: {errs:#?}"
    );
    assert_refused_naming(
        &load_errors_of(&add("[P]", "P")),
        &[
            &format!("is bound to `{ns}.add.P`"),
            "declare a requirement slot for `P` on the enclosing SORT or OPERATION",
            "(`requires P: <the spec above>`)",
        ],
        "a declared parameter is told to declare the slot",
    );
}

/// A CALLER'S OWN CLAUSE IS STATED WITH THE MEMBER IT NAMES. `f` takes a `Tag.T`, so it
/// requires `Tag` of that parameter; the box it builds is over another one, and the refusal
/// says which clause the scope holds and why it does not answer. The clause read `requires
/// …Tag[T = ?]` — what is said of a scope that left its element undetermined.
#[test]
fn a_callers_own_clause_is_stated_with_the_member() {
    let ns = "xqgew.own_clause";
    let errs = load_errors_of(&program(
        ns,
        &[TAG_SPEC],
        "  sort Box\n    sort T = ?\n    requires Tag[T = T]\n    entity box(v: T)\n  end\n\n  \
         operation f[D](w: Tag.T, d: D) -> Int64 =\n    let b = box(v: d)\n    1",
    ));
    assert_refused_naming(
        &errs,
        &[&format!(
            "the enclosing scope's `requires {ns}.Tag[T = Tag.T]` covers only as a wildcard"
        )],
        "the scope's clause as its signature has it",
    );
}

/// AN UNCONSTRAINED MEMBER IS NAMED BY ITS SPELLING, AND NOT ADVISED A BRACKET. `eo` names
/// `Tagger.E` and no carrier, so no call says which `Tagger` it is of. The advice was `use
/// `eo[E = …](…)``, a key that names no parameter of `eo`; it is now what would fix the
/// parameter at a call, that this call fixed it by none of them, and the one repair that
/// always can — the parameter in the operation's own bracket.
///
/// CONTROL, in the same row: a parameter written in a bracket keeps the advice that fits
/// it. Passes with or without the change.
#[test]
fn an_unconstrained_member_is_named_and_not_advised_a_bracket() {
    let ns = "xqgew.unconstrained";
    let errs = load_errors_of(&program(
        ns,
        &[TWO_SPECS],
        "  operation eo(n: Int64) -> Int64 effects {Tagger.E} = n\n  \
         operation go() -> Int64 = eo(1)",
    ));
    assert_refused_naming(
        &errs,
        &[
            "eo.type_arg: expected a type for 'Tagger.E', got unconstrained",
            "no bracket names a member's parameter",
            "`Tagger.E` is fixed by the provision of `Tagger` at a carrier the call passes",
            "this call fixes it by none of them",
            "write the parameter in `eo`'s own bracket",
        ],
        "the member, what would fix it, and the repair",
    );
    assert!(
        !errs.iter().any(|e| e.contains("use `eo[")),
        "a member's parameter is not advised a bracket: {errs:#?}"
    );

    let errs = load_errors_of(&program(
        ns,
        &[],
        "  operation mk[El]() -> Int64 = 1\n  operation go() -> Int64 = mk()",
    ));
    assert_refused_naming(
        &errs,
        &["mk.type_arg: expected a type for 'El', got unconstrained — use `mk[El = …](…)`"],
        "a bracket parameter is pinned by writing it",
    );
}

// ── not named by a bracket ────────────────────────────────────────────────────────────

/// `Holder` over its own parameter `param`, with a member whose signature names `X.C` and
/// `X.E`, and the four calls that say what `Holder`'s parameter is: by a key on the callee
/// and by the receiver's bracket, rightly (`String`, the holder being built over "s") and
/// wrongly (`Int64`). The key is the holder's in both spellings.
#[track_caller]
fn assert_the_key_is_the_holders(ns: &str, param: &str) {
    let call = |call: &str| {
        program(
            ns,
            &[
                TYPED_SPEC,
                &format!(
                    "  sort Holder\n    sort {param} = ?\n    entity hold(v: {param})\n    \
                     operation pick(self: Self, x: X.C) -> X.E = X.get(x)\n  end\n"
                ),
            ],
            &format!("  operation go() -> Int64 = {call}"),
        )
    };
    let go = format!("{ns}.go");
    for right in [
        format!("Holder.pick[{param} = String](hold(v: \"s\"), b(n: 7))"),
        format!("Holder[{param} = String].pick(hold(v: \"s\"), b(n: 7))"),
    ] {
        assert_eq!(run_int64(&call(&right), &go), Ok(7), "{right}");
    }
    for wrong in [
        format!("Holder.pick[{param} = Int64](hold(v: \"s\"), b(n: 7))"),
        format!("Holder[{param} = Int64].pick(hold(v: \"s\"), b(n: 7))"),
    ] {
        assert_refused_naming(
            &load_errors_of(&call(&wrong)),
            &[&format!(
                "pick.self (op-arg): expected Holder[{param} = Int64], got Holder[{param} = String]"
            )],
            &wrong,
        );
    }
}

/// A BRACKET KEY IS THE SORT'S PARAMETER, AND NOT A MEMBER'S. `Holder` declares `E`, and
/// `pick` names `X.E`. A key `E` on the callee is `Holder`'s — the one `E` its declaration
/// writes — as it is on the receiver, and the two spellings give one verdict.
///
/// On the parent commit the callee spelling bound `X.E`: the first call was refused
/// (`expected Int64, got String`, and `X[E = String, C = B]` cannot be supplied) and the
/// third loaded and answered 7. The two receiver-spelling calls pass either way.
#[test]
fn a_bracket_key_is_the_sorts_parameter_and_not_a_members() {
    assert_the_key_is_the_holders("xqgew.key", "E");
}

/// CONTROL — the same four calls with the sort's parameter under a name no member has.
/// Passes with or without the change by design: the key was never ambiguous.
#[test]
fn a_bracket_key_reaches_a_sort_parameter_of_another_name() {
    assert_the_key_is_the_holders("xqgew.key_control", "F");
}

/// NO BRACKET NAMES A MEMBER'S PARAMETER. `eo` writes no bracket, so a key names no
/// parameter of it — by the member's name or by its whole spelling — and a positional has
/// none to land on; each refusal says which members the author took for bracket
/// parameters. The call without a bracket runs, `X.C`
/// and `X.E` said by the argument's provision; it passes with or without the change.
///
/// On the parent commit `eo[E = Int64](…)` bound `X.E` by the member's name, and `eo[Int64,
/// B](…)` bound both in the order the loader minted them — the return type's first.
///
/// CONTROL, in the same row: a key that names nothing over an operation with no member is
/// refused as it always was, with no word about members.
#[test]
fn no_bracket_names_a_members_parameter() {
    let ns = "xqgew.no_bracket";
    let call = |call: &str| {
        program(
            ns,
            &[TYPED_SPEC],
            &format!(
                "  operation eo(n: Int64, x: X.C) -> X.E = X.get(x)\n  \
                 operation plain(n: Int64) -> Int64 = n\n  \
                 operation go() -> Int64 = {call}"
            ),
        )
    };
    assert_eq!(
        run_int64(&call("eo(1, b(n: 7))"), &format!("{ns}.go")),
        Ok(7)
    );
    assert_refused_naming(
        &load_errors_of(&call("eo[E = Int64](1, b(n: 7))")),
        &["eo.type_arg: expected declared type-param name, got unknown type-param 'E' — \
           `X.E` is a member's parameter, which no bracket names"],
        "a key of the member's name",
    );
    assert_refused_naming(
        &load_errors_of(&call("eo[X.E = Int64](1, b(n: 7))")),
        &["eo.type_arg: expected declared type-param name, got unknown type-param 'X.E' — \
           `X.E` is a member's parameter, which no bracket names"],
        "a key of the member's whole spelling",
    );
    assert_refused_naming(
        &load_errors_of(&call("eo[Int64, B](1, b(n: 7))")),
        &["eo.type_arg: expected at most 0 positional type argument(s), got 2 — the callee \
           is over-applied — `X.E`, `X.C` are members' parameters, which no bracket names"],
        "a positional over the members' parameters",
    );
    let errs = load_errors_of(&call("plain[E = Int64](1)"));
    assert_refused_naming(
        &errs,
        &["plain.type_arg: expected declared type-param name, got unknown type-param 'E'"],
        "a key that names nothing",
    );
    assert!(
        !errs.iter().any(|e| e.contains("member")),
        "an operation with no member says nothing of members: {errs:#?}"
    );
}

/// A WRITTEN PARAMETER BESIDE A MEMBER IS BOUND AS BEFORE, by its name and by position —
/// and the position after it is not a member's. `pick` writes `[E]` and names `X.E`.
///
/// The first three calls pass with or without the change. The fourth fails with the
/// members' parameters left among the targets: `pick[String, Int64](…)` loaded, the second
/// positional landing on `X.E`.
#[test]
fn a_written_parameter_beside_a_member_is_bound_as_before() {
    let ns = "xqgew.beside";
    let call = |call: &str| {
        program(
            ns,
            &[TYPED_SPEC],
            &format!(
                "  operation pick[E](y: E, x: X.C) -> X.E = X.get(x)\n  \
                 operation go() -> Int64 = {call}"
            ),
        )
    };
    let go = format!("{ns}.go");
    assert_eq!(run_int64(&call("pick[E = String](\"s\", b(n: 7))"), &go), Ok(7));
    assert_eq!(run_int64(&call("pick[String](\"s\", b(n: 7))"), &go), Ok(7));
    assert_refused_naming(
        &load_errors_of(&call("pick[E = Int64](\"s\", b(n: 7))")),
        &["pick.y (op-arg): expected Int64, got String"],
        "the key is the written parameter",
    );
    assert_refused_naming(
        &load_errors_of(&call("pick[String, Int64](\"s\", b(n: 7))")),
        &["pick.type_arg: expected at most 1 positional type argument(s), got 2"],
        "one parameter is written",
    );
}

// ── members of one name, together ─────────────────────────────────────────────────────

/// CONTROL — `X.E` AND `Y.E` IN ONE SIGNATURE are two parameters that share a name and
/// nothing else: each call goes through its own requirement. Passes with or without the
/// change by design; it records that the name was never the parameter.
#[test]
fn two_members_of_one_name_run_each_through_its_own_requirement() {
    let ns = "xqgew.two";
    let src = program(
        ns,
        &[TWO_SPECS],
        "  operation two(x: Tagger.C, y: Other.C) -> Int64 effects {Tagger.E, Other.E} =\n    \
         Tagger.tag(x) + Other.oth(y)\n  operation go() -> Int64 = two(a(), a())",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(101));
}

/// `X.Y.E` AND `X.Z.E` — two specs nested in one sort, each named through an import, which
/// is the spelling the sugar takes (a dotted head is not it). They run each through its own
/// requirement and are printed apart.
#[test]
fn two_nested_specs_members_run_and_are_told_apart() {
    let ns = "xqgew.nested";
    let fixtures = format!(
        r#"
  sort Outer
    sort Y
      sort C = ?
      effects E = ?
      operation yo(self: C) -> Int64 effects {{E}}
    end
    sort Z
      sort C = ?
      effects E = ?
      operation zo(self: C) -> Int64 effects {{E}}
    end
  end

  import {ns}.Outer.{{Y, Z}}

  sort N
    entity n
    provides Outer.Y[C = N, E = {{}}]
    operation yo(self: N) -> Int64 = 1
    provides Outer.Z[C = N, E = {{}}]
    operation zo(self: N) -> Int64 = 10
  end
"#
    );
    let signature = "operation two(x: Y.C, y: Z.C) -> Int64 effects {Y.E, Z.E}";
    assert_eq!(
        run_int64(
            &program(
                ns,
                &[&fixtures],
                &format!("  {signature} = Y.yo(x) + Z.zo(y)\n  operation go() -> Int64 = two(n(), n())"),
            ),
            &format!("{ns}.go")
        ),
        Ok(11)
    );
    let errs = load_errors_of(&program(
        ns,
        &[&fixtures, FAILS],
        &format!("  {signature} = fails()"),
    ));
    assert_refused_naming(
        &errs,
        &["expected declared: [Y.E, Z.E], got undeclared effect: Error"],
        "each nested spec's member by its spec",
    );
}

/// EVERY `E` AT ONCE: the sort's own `E`, a bracket's `F`, a type member `X.E` and a row
/// member `Tagger.E`, in one member of `Holder`. The bracket binds the sort's `E` and the
/// operation's `F`; the two members are said by their arguments' provisions.
///
/// Fails with a member's parameter named by the interned `E`, as on the parent commit —
/// (2) of the ledger: the key `E` lands on one of them, the first call is refused and the
/// second loads. A member left in the bracket's list under a name of its own is not
/// reached by a key, so (6) does not fail it.
#[test]
fn every_e_at_once() {
    let ns = "xqgew.every";
    let call = |call: &str| {
        program(
            ns,
            &[TWO_SPECS, TYPED_SPEC],
            &format!(
                "  sort Holder\n    sort E = ?\n    entity hold(v: E)\n    \
                 operation mix[F](self: Self, f: F, x: X.C, t: Tagger.C) -> X.E \
                 effects {{Tagger.E}} =\n      \
                 let tagged = Tagger.tag(t)\n      X.get(x)\n  end\n\n  \
                 operation go() -> Int64 = {call}"
            ),
        )
    };
    assert_eq!(
        run_int64(
            &call("Holder.mix[E = String, F = Bool](hold(v: \"s\"), true, b(n: 7), a())"),
            &format!("{ns}.go")
        ),
        Ok(7)
    );
    assert_refused_naming(
        &load_errors_of(&call(
            "Holder.mix[E = Int64, F = Bool](hold(v: \"s\"), true, b(n: 7), a())",
        )),
        &["mix.self (op-arg): expected Holder[E = Int64], got Holder[E = String]"],
        "the key `E` is the holder's",
    );
}
