//! WI-20260825-CBRSW — `Permission[X]`, authority as an effect at the point of
//! acquisition (proposal 064).
//!
//! `Permission[X]` denotes the RUNTIME CONSULTATION OF AN AMBIENT GRANT for capability
//! `X`, and it is written on the operation that MINTS a capability object and nowhere
//! else. Holding the object is the authority thereafter. Three things have to hold for
//! that to be worth writing, and this file drives each:
//!
//!   1. THE ROW IS ORDINARY. `Permission[X]` is a member like any other, so both legs of
//!      the existing not-widen check apply unchanged — the spec's row bounds the
//!      provider's DECLARED row, and the declared row bounds the row INFERRED FROM ITS
//!      BODY. A provider therefore cannot grant itself a permission its spec never gave.
//!   2. CONTAINMENT IS STRUCTURAL. The capability's constructor is `internal`
//!      (kernel-language.md §8.6, the only hide gate), so the `Permission`-carrying
//!      operation is the sole introduction. Without this the effect is advisory: a
//!      program writes `fs_root()` and skips the check.
//!   3. THE CAPABILITY IS CONTRAVARIANT. `X <: Y  =>  Permission[Y] <: Permission[X]`.
//!      Covariance inverts exactly that and admits privilege escalation.
//!
//! CONTROL, FILE-WIDE. The change has three separable pieces and the rows below are
//! stated against each:
//!
//!   (A) `stdlib/anthill/prelude/permission.anthill` (+ its `anthill-stl` manifest
//!       entry) — the sort and `fact Effect[T = Permission[?]]`. Backing it out makes
//!       EVERY row here fail on an unresolved `Permission`, so it is not a useful axis
//!       to state per row; it is stated once, here.
//!   (B) `fact Contravariant(sort: Permission, param: T)`, written beside the sort in
//!       `stdlib/anthill/prelude/permission.anthill` rather than with the other variance
//!       facts (it decides whether a permission budget can be escalated, so the sort and
//!       its rule must not be separable — and declaring it in `anthill.reflect.typing`
//!       would import a prelude sort into a file scaland loads from a stdlib list that
//!       does not carry this one, breaking every scaland stdlib test invisibly to this
//!       ticket's `cargo-test` gate; found by review). Backing it out degrades `Permission`
//!       to INVARIANT. Red: `a_spec_granting_the_sub_capability_accepts_an_
//!       implementation_acquiring_the_super` and `permission_denial_is_not_evaded_by_a_
//!       sub_capability`. Flipping it to `Covariant` instead turns FOUR rows red — both
//!       halves of the contravariance pair, plus both halves of the negative form, whose
//!       direction inverts with it. That is why the pair is written both ways: a
//!       name-equality implementation passes neither half and a covariant one passes
//!       neither half, but each half ALONE is satisfied by one of invariance's two
//!       verdicts, so one of them would pin nothing. (All three verdicts measured by
//!       editing the fact and re-running this file.)
//!   (C) `typing::permission_entails` — the present-vs-absent verdict for this label's
//!       ENTAILMENT, which is what closes the negative form. Red (3):
//!       `permission_denial_is_not_evaded_by_a_sub_capability`,
//!       `a_bare_permission_denial_forbids_every_capability`, and
//!       `a_body_minting_a_sub_capability_of_a_denied_one_is_refused_as_denied` — the
//!       last because the body leg's denial branch asks this same verdict.
//!   (D) `typing::check_declared_row_contradiction` (+ its `load_phase_inner` call) —
//!       the LOAD-time refusal of a row that both admits and lacks a label. Red (1):
//!       `a_row_that_admits_and_lacks_one_permission_is_refused_at_load`.
//!   (E) the denied-effect branch in `check_operation_bodies` — the body leg naming a
//!       DENIAL rather than a missing declaration. Red (2):
//!       `a_denied_permission_minted_in_the_body_is_refused` and
//!       `a_body_minting_a_sub_capability_of_a_denied_one_is_refused_as_denied`. Both
//!       assert the MESSAGE; the refusal itself predates this ticket, which is why the
//!       rows say so at their sites.
//!
//! Each of (B) through (E) was measured by editing the named code and re-running this
//! file; the counts above are what came back, not what was expected.
//!
//! Everything else PASSES EITHER WAY BY DESIGN, and is here because the value of a new
//! refusal is entirely in where it STOPS: the containment rows, the two not-widen legs,
//! the two `{} <: {Permission[X]} <: {Permission[X], Permission[Y]}` controls, and the
//! guarded-deferral control all describe programs whose verdict this ticket must NOT
//! change.
//!
//! NOT A GENERAL RULE ABOUT LACKS CONSTRAINTS, and the first cut of (C) was one. Asking
//! `types_compatible(absent, present)` for EVERY label is BACKWARDS outside this one:
//! measured, `-Color` beside a supplied `Red` (with `Red provides Color`) still loaded
//! clean under it, while `-Red` beside a supplied `Color` — which loaded clean before and
//! should — was newly REFUSED. Entailment and subsumption run OPPOSITE ways for
//! `Permission` (declared contravariant) and the same way for an ordinary nominal label,
//! so no single reading of the subsumption order serves both. What a lacks constraint
//! should mean for an ordinary label under subtyping is left open; it predates this
//! ticket and is about every label rather than this one. Found by `/code-review`.
//!
//! Every row loads the real stdlib, so each is also a standing assertion that the
//! prelude's own registration is reachable.

/// Load `src` beside the full stdlib, returning the rendered load errors (empty on a
/// clean load).
fn load_errors(src: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => vec![],
        Err(errs) => errs,
    }
}

fn expect_clean(errs: &[String], what: &str) {
    assert!(errs.is_empty(), "{what} must load clean; got: {errs:#?}");
}

fn expect_refusal(errs: &[String], needles: &[&str], what: &str) {
    assert!(
        errs.iter()
            .any(|e| needles.iter().all(|n| e.contains(n))),
        "{what} must be refused, naming {needles:?}; got: {errs:#?}"
    );
}

/// THE CAPABILITY VOCABULARY, shared by every row.
///
/// `Model` / `GptModel` / `Fs` / `AdminFs` are PROJECT sorts, and that division is the
/// point: the prelude registers the KIND (`Permission`), a project names the CAPABILITY.
/// The order is declared the ordinary way — a constructor-less sort is a spec, and
/// `provides` is the is-a — so `GptModel <: Model` and `AdminFs <: Fs` are facts the
/// typer already knows, with nothing capability-specific about them.
///
/// `Oracle` and `SubOracle` are the capability OBJECTS. Their constructors are
/// `internal` and each is minted by exactly one operation, which is the containment
/// discipline the rows below both use and check.
const CAPS: &str = r#"
sort cbrsw.Model
end

sort cbrsw.GptModel
  import cbrsw.{Model}
  provides Model
end

sort cbrsw.Fs
end

sort cbrsw.AdminFs
  import cbrsw.{Fs}
  provides Fs
end

sort cbrsw.Oracle
  import anthill.prelude.{Permission}
  import cbrsw.{Model}
  internal entity oracle
  operation acquire() -> Oracle
    effects {Permission[Model]} = oracle()
end

sort cbrsw.SubOracle
  import anthill.prelude.{Permission}
  import cbrsw.{GptModel}
  internal entity sub_oracle
  operation acquire() -> SubOracle
    effects {Permission[GptModel]} = sub_oracle()
end
"#;

/// `CAPS` plus a `namespace cbrsw` body.
fn program(body: &str) -> String {
    format!(
        "{CAPS}\nnamespace cbrsw\n  \
         import anthill.prelude.{{Permission, Unit, Int64, Bool, External, Error}}\n  \
         import anthill.prelude.PartialEq.{{eq}}\n  \
         import cbrsw.{{Model, GptModel, Fs, AdminFs, Oracle, SubOracle}}\n{body}\nend\n"
    )
}

// ── 1. The label is ordinary: it registers, and a row carrying it loads ──────────────

#[test]
fn an_operation_declaring_a_permission_loads() {
    // THE ACCEPTANCE'S FIRST HALF, and it needs no `fact Effect[…]` of its own: the
    // prelude registers the KIND once, and the project supplies only the capability.
    // That this loads at all is what VM3YB's registration check makes non-trivial —
    // before `permission.anthill` existed, `effects {Permission[Model]}` would have been
    // refused as an unregistered label rather than as an unresolved name.
    let errs = load_errors(&program(
        "  operation mint() -> Oracle\n    effects {Permission[Model]} = Oracle.acquire()",
    ));
    expect_clean(&errs, "an operation declaring `Permission[Model]`");
}

#[test]
fn permission_and_external_combine_freely() {
    // 064's orthogonality table, at the one cell that is not obvious: a row may carry
    // `Permission` WITHOUT `External` (an in-memory root, still gated — where a test
    // double lives) and both together. Neither is a special case; this row exists so a
    // future reading of `Permission` as "a kind of External" would break something.
    let errs = load_errors(&program(
        "  operation gated_only() -> Oracle\n    effects {Permission[Model]} = Oracle.acquire()\n\
         \n  operation gated_and_external() -> Oracle\n    effects {Permission[Model], External} = Oracle.acquire()",
    ));
    expect_clean(&errs, "`Permission` with and without `External`");
}

// ── 2. Containment: the mint is the sole introduction ────────────────────────────────

#[test]
fn an_internal_capability_constructor_is_refused_from_outside_its_sort() {
    // WITHOUT THIS THE EFFECT IS ADVISORY, which is why containment is part of the
    // change and not a convention: a program that can write `oracle()` never consults
    // the grant, and every row in this file becomes decoration. §8.6 makes `internal`
    // the only hide gate and WI-977 puts a namespace body outside the sort's scope, so
    // the refusal is the existing one — what this row asserts is that the capability
    // pattern RESTS on it.
    let errs = load_errors(&program("  operation sneaky() -> Oracle = oracle()"));
    expect_refusal(
        &errs,
        &["'oracle' is internal to 'cbrsw.Oracle'"],
        "naming an `internal` capability constructor from outside its sort",
    );
}

#[test]
fn the_mint_operation_is_the_only_introduction() {
    // The control for the row above: the SAME constructor, reached through the gate,
    // loads. A refusal that also refused this would have made the capability
    // unconstructible rather than contained.
    let errs = load_errors(&program(
        "  operation legal() -> Oracle\n    effects {Permission[Model]} = Oracle.acquire()",
    ));
    expect_clean(&errs, "minting through the `Permission`-carrying operation");
}

// ── 3. The two not-widen legs ────────────────────────────────────────────────────────

/// A spec sort granting `spec_row`, and a carrier providing it with `impl_row` and the
/// body `impl_body`. This is the shape both legs are measured in — the same one
/// `examples/guardians` uses for `wide_row` (the DECLARED leg) and `bad_checker` (the
/// BODY leg).
fn provider(spec_row: &str, impl_row: &str, impl_body: &str) -> String {
    format!(
        "{CAPS}\n\
         sort cbrsw.Gate\n  \
         import anthill.prelude.{{Permission, Unit}}\n  \
         import cbrsw.{{Model, GptModel, Fs, AdminFs}}\n  \
         sort C = ?\n  \
         operation act(self: C) -> Unit\n    effects {spec_row}\nend\n\
         \n\
         sort cbrsw.Impl\n  \
         import anthill.prelude.{{Permission, Unit}}\n  \
         import cbrsw.{{Model, GptModel, Fs, AdminFs, Gate, Oracle, SubOracle}}\n  \
         entity impl\n  \
         operation act(self: Impl) -> Unit\n    effects {impl_row} = {impl_body}\n  \
         provides Gate\nend\n"
    )
}

#[test]
fn a_provider_declaring_a_permission_the_spec_never_granted_is_refused() {
    // THE DECLARED LEG. The spec's row bounds the provider's row, and `Permission` rides
    // it as an ordinary member — no family algebra, no rank. This is what makes "a
    // generated implementation cannot grant itself a permission" true without a new
    // mechanism: the permission budget is fixed by the party that wrote the spec.
    let errs = load_errors(&provider(
        "{External, Error}",
        "{External, Error, Permission[Model]}",
        "()",
    ));
    expect_refusal(
        &errs,
        &["effects must not widen", "Permission[T = Model]"],
        "a provider declaring a `Permission` its spec's row lacks",
    );
}

#[test]
fn a_provider_minting_in_its_body_while_declaring_the_specs_row_is_refused() {
    // THE BODY LEG, and it is the one a generated implementation actually trips: the
    // declaration is copied from the spec (so the leg above is silent) and the BODY
    // reaches for the capability. `Impl.act` declares exactly `{External, Error}` and
    // calls the `Permission[Model]`-carrying mint.
    let errs = load_errors(&provider(
        "{External, Error}",
        "{External, Error}",
        "let o = Oracle.acquire()\n    ()",
    ));
    expect_refusal(
        &errs,
        &["undeclared effect", "Permission[T = Model]"],
        "a provider whose body mints a capability its declared row does not carry",
    );
}

#[test]
fn a_denied_permission_minted_in_the_body_is_refused() {
    // 064's headline claim, and the reason the label exists: `-Permission[Model]` on an
    // operation whose body mints a model capability. The declaration says the body
    // provably never consults a model; the body does; the load fails.
    //
    // THE MESSAGE IS ASSERTED, not just the refusal, because the two failures have
    // DIFFERENT REPAIRS and the generic one names the wrong repair. An undeclared effect
    // is fixed by adding the label; a denied one cannot be — the row says the body must
    // not perform it. The refusal itself is not new (the label is simply not among the
    // declared atoms, so the ordinary body leg already refused it); what this ticket
    // adds is that the row is printed AS WRITTEN (`-Permission[…]`, not the internal
    // `absent[label = …]`) and the verdict says which of the two failures it is.
    let errs = load_errors(&program(
        "  operation check_it() -> Unit\n    \
         effects {External, Error, -Permission[Model]} =\n      \
         let o = Oracle.acquire()\n      ()",
    ));
    expect_refusal(
        &errs,
        &[
            "denied effect: Permission[T = Model]",
            "the row DECLARES `-Permission[T = Model]`",
            "declared: [External, Error, -Permission[T = Model]]",
        ],
        "a body minting a capability the row denies",
    );
}

#[test]
fn a_body_minting_a_sub_capability_of_a_denied_one_is_refused_as_denied() {
    // The downward closure reaching the BODY leg's diagnostic: `-Permission[Model]` with
    // a body that mints `Permission[GptModel]`. The refusal itself passes either way —
    // the sub-capability is not among the declared atoms, so it was already refused as
    // undeclared — but naming it a DENIAL is the sharp reading, and it is the same
    // `label_violates_absence` verdict the row-instantiation site uses. A body author
    // who reads "undeclared" here would try to add the label and be refused again.
    let errs = load_errors(&program(
        "  operation check_it() -> Unit\n    \
         effects {External, Error, -Permission[Model]} =\n      \
         let o = SubOracle.acquire()\n      ()",
    ));
    expect_refusal(
        &errs,
        &[
            "denied effect: Permission[T = GptModel]",
            "the row DECLARES `-Permission[T = Model]`",
        ],
        "a body minting a SUB-capability of a denied one",
    );
}

// ── 4. Controls: `{} <: {Permission[X]} <: {Permission[X], Permission[Y]}` ───────────

#[test]
fn an_operation_acquiring_nothing_loads_where_a_permission_is_granted() {
    // `{} <: {Permission[X]}`. A SUITE OF REFUSALS ALONE IS CONSISTENT WITH A CHECKER
    // THAT REFUSES EVERYTHING, which is what this row and the next exist to rule out.
    let errs = load_errors(&provider("{Permission[Model]}", "{}", "()"));
    expect_clean(&errs, "a provider acquiring nothing under a granted permission");
}

#[test]
fn a_provider_acquiring_one_permission_loads_where_two_are_granted() {
    // `{Permission[X]} <: {Permission[X], Permission[Y]}`. Two distinct capabilities
    // coexist in one row by set union — there is no join and no rank, so taking a subset
    // is ordinary subsumption.
    let errs = load_errors(&provider(
        "{Permission[Model], Permission[Fs]}",
        "{Permission[Model]}",
        "let o = Oracle.acquire()\n    ()",
    ));
    expect_clean(&errs, "a provider taking one of two granted permissions");
}

// ── 5. Contravariance, both directions ──────────────────────────────────────────────

#[test]
fn a_spec_granting_the_sub_capability_accepts_an_implementation_acquiring_the_super() {
    // `AdminFs <: Fs`, so `Permission[Fs] <: Permission[AdminFs]`: a spec granting
    // `Permission[AdminFs]` accepts an implementation that acquires only
    // `Permission[Fs]` — IT TAKES LESS.
    //
    // RED WITHOUT (B), and red under covariance too. Under name equality the two labels
    // never match; under invariance the flipped direction is also demanded and fails;
    // under covariance the demanded direction is `Fs <: AdminFs`, which is false. Only
    // contravariance admits it.
    let errs = load_errors(&provider(
        "{Permission[AdminFs]}",
        "{Permission[Fs]}",
        "()",
    ));
    expect_clean(
        &errs,
        "an implementation acquiring the SUPER capability under a spec granting the SUB",
    );
}

#[test]
fn a_spec_granting_the_super_capability_refuses_an_implementation_acquiring_the_sub() {
    // The safety half of the same rule: a spec granting `Permission[Fs]` REFUSES an
    // implementation acquiring `Permission[AdminFs]`. COVARIANCE INVERTS EXACTLY THIS
    // and admits the privilege escalation.
    //
    // PASSES WITHOUT (B) — invariance refuses it too — and FAILS under covariance. That
    // asymmetry is why the pair is written both ways: this row alone does not pin the
    // variance, and neither does its twin.
    let errs = load_errors(&provider(
        "{Permission[Fs]}",
        "{Permission[AdminFs]}",
        "()",
    ));
    expect_refusal(
        &errs,
        &["effects must not widen", "Permission[T = AdminFs]"],
        "an implementation acquiring the SUB capability under a spec granting the SUPER",
    );
}

// ── 6. The negative form is downward-closed in the capability ───────────────────────

/// A callback slot whose row DENIES `lacked`, and a call passing `arg` at row `row`.
///
/// WHY AN OPEN ROW. On a CLOSED row a denial is mostly redundant with omission — "not in
/// the row" already means "not incurred", so `{External, Error, -Permission[Model]}` with
/// a minting body is caught by the body leg whether or not the `-` atom is written. The
/// place a denial is the ONLY thing between a program and a capability is an OPEN row
/// whose instantiation supplies it, which is this shape, and it is also 045's own
/// spelling for the constraint — so this is where the escalation lives.
///
/// "MOSTLY", not "entirely, and the gap was the cheapest possible evasion: writing the
/// label PRESENT beside its own denial silenced both legs at once (the body leg because
/// the label IS declared, WI-705 because nothing was instantiated). Closed at load by
/// `check_declared_row_contradiction`; `a_row_that_admits_and_lacks_one_permission_is_
/// refused_at_load` is that program, and it loaded completely clean before. Found by
/// `/code-review`.
fn denial(lacked: &str, row: &str, arg: &str) -> String {
    format!(
        "{CAPS}\nnamespace cbrsw\n  \
         import anthill.prelude.{{Permission, Unit}}\n  \
         import cbrsw.{{Model, GptModel, Fs, AdminFs, Oracle, SubOracle}}\n  \
         operation guarded[Rho](f: () -> Unit @ {{Rho, -{lacked}}}) -> Unit\n  \
         operation mints_model() -> Unit\n    effects {{Permission[Model]}} =\n      \
         let o = Oracle.acquire()\n      ()\n  \
         operation mints_sub() -> Unit\n    effects {{Permission[GptModel]}} =\n      \
         let o = SubOracle.acquire()\n      ()\n  \
         operation mints_fs() -> Unit\n    effects {{Permission[Fs]}}\n  \
         operation call() -> Unit = guarded[Rho = {row}]({arg})\nend\n"
    )
}

#[test]
fn a_denial_forbids_the_capability_it_names() {
    // The baseline the escalation row is measured against: `-Permission[Model]` against
    // an instantiation supplying `Permission[Model]`. PASSES EITHER WAY — equality
    // already decided this one, which is exactly why the next row was invisible.
    let errs = load_errors(&denial(
        "Permission[Model]",
        "{Permission[Model]}",
        "mints_model",
    ));
    expect_refusal(
        &errs,
        &["lacks-constraint", "Permission[T = Model]"],
        "an instantiation supplying the denied permission",
    );
}

#[test]
fn permission_denial_is_not_evaded_by_a_sub_capability() {
    // THE ESCALATION, and it LOADED CLEAN before this ticket — measured, not predicted.
    // `GptModel <: Model`, so acquiring a GPT capability IS acquiring a model
    // capability, and `-Permission[Model]` must forbid `Permission[GptModel]`. Under
    // equality the two labels are simply different and the denial was evadable by naming
    // a sub-capability, which is precisely what makes `-Permission[Model]` worth writing
    // in the first place.
    //
    // RED WITHOUT (B) — invariance cannot relate the two labels — AND RED WITHOUT (C):
    // it needs both the declared variance and the directional present-vs-absent verdict.
    let errs = load_errors(&denial(
        "Permission[Model]",
        "{Permission[GptModel]}",
        "mints_sub",
    ));
    expect_refusal(
        &errs,
        &["lacks-constraint", "Permission[T = Model]"],
        "an instantiation acquiring a SUB-capability of a denied one",
    );
}

#[test]
fn a_denial_of_a_sub_capability_does_not_forbid_the_super_capability() {
    // ONE DIRECTION, NOT BOTH — the control that a symmetric reading would break.
    // `-Permission[AdminFs]` denies the STRONGER demand; acquiring `Permission[Fs]` asks
    // for less, and demanding some `Fs` does not entail demanding an `AdminFs`. A
    // `label_violates_absence` written as an `||` of the two subtype directions passes
    // every refusal row in this file and fails here.
    let errs = load_errors(&denial(
        "Permission[AdminFs]",
        "{Permission[Fs]}",
        "mints_fs",
    ));
    expect_clean(
        &errs,
        "acquiring the weaker demand under a denial of the stronger one",
    );
}

#[test]
fn a_bare_permission_denial_forbids_every_capability() {
    // THE GENERAL DENIAL — 064 open question 1 — and the answer is that it needs no
    // variable in a lacks-constraint at all. A BARE `-Permission` is the whole claim
    // "acquires no authority whatsoever": bare-vs-parameterized subsumption makes
    // `Permission <: Permission[X]` for every `X`, so the directional verdict forbids
    // every capability at once, with no capability order and no root assumed.
    //
    // RED WITHOUT (C). Equality never relates a bare label to a parameterized one.
    let errs = load_errors(&denial("Permission", "{Permission[Model]}", "mints_model"));
    expect_refusal(
        &errs,
        &["lacks-constraint", "Permission"],
        "a bare `-Permission` against an acquired `Permission[Model]`",
    );
}

#[test]
fn a_row_that_admits_and_lacks_one_permission_is_refused_at_load() {
    // THE CHEAPEST EVASION OF A DENIAL, and it LOADED COMPLETELY CLEAN before this
    // ticket — no error at all, from either leg. Writing `Permission[Model]` PRESENT
    // beside its own `-Permission[Model]` silences both: the body leg because the label
    // IS among the declared atoms, and WI-705's call-site check because it is gated on
    // an op type parameter actually being BOUND and this operation has none.
    //
    // WI-705's own comment named the missing site — "a literal `{X, -X}` is a load-time
    // concern, not this call-site one" — and no load-time site asked. Now one does, and
    // it shares WI-705's verdict (`uninhabitable_row_clash`) rather than re-deriving it.
    //
    // NOT PERMISSION-SPECIFIC: the refusal is about any label, which is why the guarded
    // control below sits beside it. Found by `/code-review`.
    let errs = load_errors(&program(
        "  operation evade() -> Oracle\n    \
         effects {Permission[Model], -Permission[Model]} = Oracle.acquire()",
    ));
    expect_refusal(
        &errs,
        &["both ADMITS and LACKS", "Permission[T = Model]"],
        "a row admitting and lacking one permission",
    );
}

#[test]
fn a_guarded_occurrence_beside_a_denial_defers_to_discharge() {
    // THE CONTROL FOR THE ROW ABOVE, and the one it could most easily have broken. A
    // GUARDED atom is only CONDITIONALLY present — WI-067 discharge may refute the guard
    // and drop it — so `{K :- g, -K}` is not a contradiction and must keep loading. The
    // load-time check inherits that deferral by sharing WI-705's multiset counting
    // (present occurrences > guarded ones), rather than by re-stating it.
    //
    // Written with an ORDINARY label rather than `Permission`, because the guarded
    // spelling is where the deferral rule lives and it is not this label's business.
    let errs = load_errors(&program(
        "  operation risky(x: Int64) -> Unit\n    \
         effects {Permission[Model] :- eq(x, 0), -Permission[Model]} = ()",
    ));
    expect_clean(
        &errs,
        "a guarded occurrence beside a denial (defers to WI-067 discharge)",
    );
}

// ── 7. The three questions 064 left open ────────────────────────────────────────────

#[test]
fn a_grant_is_an_ordinary_handler_and_discharges_the_label() {
    // 064 OPEN QUESTION 2 — "does handler discharge come free per-label?" — ANSWERED
    // YES, and it is the cheapest part of the design. A grant is §5.5's ordinary handler
    // shape (the label present on the body side, absent from the result, sharing the
    // tail `Rho`) with NO kernel semantics of its own: `mints` performs
    // `{Permission[Model], Error}`, and under `with_model_grant` the call's row is
    // exactly the residual `{Error}`.
    //
    // The `over_claimed` half is what makes this non-vacuous: the residual is REAL, not
    // dropped along with the handled label. Without it, a handler that discharged
    // everything would satisfy the first half.
    let discharged = load_errors(&program(
        "  operation with_model_grant[Rho](body: () -> Int64 @ {Permission[Model], Rho}) -> Int64\n    \
         effects {Rho}\n  = 0\n  \
         operation mints() -> Int64\n    effects {Permission[Model], Error} =\n      \
         let o = Oracle.acquire()\n      1\n  \
         operation granted() -> Int64\n    effects {Error} = with_model_grant(lambda () -> mints())",
    ));
    expect_clean(&discharged, "a granted call carrying only the residual row");

    let over_claimed = load_errors(&program(
        "  operation with_model_grant[Rho](body: () -> Int64 @ {Permission[Model], Rho}) -> Int64\n    \
         effects {Rho}\n  = 0\n  \
         operation mints() -> Int64\n    effects {Permission[Model], Error} =\n      \
         let o = Oracle.acquire()\n      1\n  \
         operation over_claimed() -> Int64\n    effects {} = with_model_grant(lambda () -> mints())",
    ));
    expect_refusal(
        &over_claimed,
        &["undeclared effect: Error"],
        "a granted call claiming to discharge the residual too",
    );
}

#[test]
fn a_variable_argument_in_a_lacks_constraint_constrains_nothing() {
    // 064 OPEN QUESTION 1 — "does a lacks-constraint admit a VARIABLE argument?" — and
    // this row RECORDS A TRAP rather than a capability. `-Permission[?]` parses, loads,
    // and forbids NOTHING: the pair (`Permission[?]`, `Permission[GptModel]`) is
    // undecided, so the directional verdict withholds, exactly as it does for a row
    // parameter. A reader who writes it gets the general denial they wanted in
    // appearance only.
    //
    // THE WORKING SPELLING IS THE BARE ONE, which is the actual answer to the question:
    // `-Permission` subsumes every application of the label
    // (`a_bare_permission_denial_forbids_every_capability`), so the general denial needs
    // no variable in a lacks-constraint at all, and assumes neither a capability order
    // nor a root. Closing the variable spelling means telling an ANONYMOUS wildcard
    // apart from a rigid type parameter (`-Error[T]`, where an undecided argument must
    // stay undecided) inside 045's row algebra — a question about every label, not about
    // `Permission`, and not one this ticket measured a population for.
    //
    // PASSES EITHER WAY. It is here so that a later change which DOES close the variable
    // spelling trips this row and reads the note, rather than quietly widening a
    // constraint nobody had measured.
    let errs = load_errors(&denial(
        "Permission[?]",
        "{Permission[GptModel]}",
        "mints_sub",
    ));
    expect_clean(
        &errs,
        "a variable-argument lacks constraint (INERT — see this row's note)",
    );
}

// ── 8. The program RUNS ─────────────────────────────────────────────────────────────

#[test]
fn a_minted_capability_is_a_value_the_program_can_carry() {
    // LOADING IS NOT THE CAPABILITY. `Permission` has no runtime semantics in this
    // increment — it is threaded as an ordinary row member and no handler interprets it
    // — so what a run establishes is the other half of the design: the mint returns an
    // ORDINARY VALUE, and holding it is the authority thereafter. `use_it` takes the
    // capability and carries NO `Permission`, which is the whole point of putting the
    // label on the mint.
    //
    // PASSES EITHER WAY by design: neither piece of this change is on the evaluator's
    // path.
    let src = program(
        "  operation use_it(o: Oracle) -> Int64 = 7\n  \
         operation run_it() -> Int64\n    effects {Permission[Model]} =\n      \
         let o = Oracle.acquire()\n      use_it(o)",
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp
        .call("cbrsw.run_it", &[])
        .unwrap_or_else(|e| panic!("call run_it: {e:?}"));
    assert_eq!(
        got.as_int(),
        Some(7),
        "the minted capability flows into an operation that carries no `Permission`"
    );
}

#[test]
fn a_nullary_capability_handle_carries_no_identity_of_its_own() {
    // 064 OPEN QUESTION 3 — "does the capability handle have identity?" — ANSWERED for
    // the shape the proposal's own example uses, and the answer is NO. `oracle` is a
    // NULLARY constructor, hence a constant of its sort, so two mints produce two
    // structurally-equal values and there is nothing for a CSE to observe: the question
    // "is the CALL de-duplicable, as distinct from the CHECK being idempotent" is
    // VACUOUS here rather than answered in the affirmative.
    //
    // A capability that wants identity must therefore carry it in a FIELD, and nothing
    // in this increment supplies freshness to put there — which is the honest scope
    // note, not a defect. Separately, the effect does not LICENSE dedup outside one
    // grant's extent (§5.5's licence paragraph); nothing enforces that today because
    // nothing optimises effect-carrying calls.
    //
    // PASSES EITHER WAY by design: neither piece of this change is on the evaluator's
    // path.
    let src = program(
        "  operation twice() -> Bool\n    effects {Permission[Model]} =\n      \
         let a = Oracle.acquire()\n      let b = Oracle.acquire()\n      eq(a, b)",
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp
        .call("cbrsw.twice", &[])
        .unwrap_or_else(|e| panic!("call twice: {e:?}"));
    assert_eq!(
        got.as_bool(),
        Some(true),
        "two mints of a nullary capability are the same value — the handle has no identity"
    );
}
