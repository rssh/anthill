//! WI-20260823-VM3YB — an effect-row label must name a REGISTERED effect kind.
//!
//! `stdlib/anthill/prelude/effects.anthill` has documented the registration since it was
//! written ("Effect kinds are registered via `fact Effect[T = Kind[?]]`") and proposal
//! 013 says what it is for ("Unknown effect kind = missing fact"). Nothing asked, at any
//! site, so the declaration was inert everywhere it appeared and a MISSPELLED label was a
//! silent new effect. `typing::check_effect_registration` is the site that asks; this
//! file drives it.
//!
//! CONTROL, FILE-WIDE, stated per section below. The five rows under "The refusal" fail
//! the moment `check_effect_registration` is backed out of `load_phase_inner` — they are
//! the whole of what this ticket changes. Every other row passes EITHER WAY BY DESIGN:
//! the two registration spellings, the wildcard, the row-parameter exemption, the arrow
//! boundary and the prelude sweep all describe programs that loaded clean before this
//! pass and must keep doing so. They are here because the value of a new refusal is
//! entirely in where it STOPS, and a file holding only the five red rows would let the
//! refusal widen without anything noticing.
//!
//! Every row loads the real stdlib, so each is also a standing assertion that the
//! prelude's own rows stay registered.

use anthill_core::kb::KnowledgeBase;

/// Load `src` beside the full stdlib, returning the rendered load errors (empty on a
/// clean load).
fn load_errors(src: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => vec![],
        Err(errs) => errs,
    }
}

/// Did the load refuse `label` as unregistered? Matches on BOTH halves the ticket's
/// acceptance names — the label and the repair — so a refusal that merely mentions the
/// operation cannot satisfy these rows.
fn refused_unregistered(errs: &[String], label: &str) -> bool {
    errs.iter().any(|e| {
        e.contains("is not a REGISTERED effect kind")
            && e.contains(label)
            && e.contains("fact Effect[T =")
    })
}

fn expect_clean(errs: &[String], what: &str) {
    assert!(errs.is_empty(), "{what} must load clean; got: {errs:#?}");
}

// ── The refusal ──────────────────────────────────────────────────────

#[test]
fn an_unregistered_label_is_refused_naming_the_label_and_the_registration() {
    // THE TICKET'S HEADLINE ROW. `Unregistered` is a perfectly real sort — it resolves,
    // so the loader's unresolved-name refusal never sees it (a label naming NOTHING was
    // already loud, which is why this defect could only be found by reading). What was
    // missing is that resolving is not the same as being an effect.
    let errs = load_errors(
        r#"
        namespace vm3yb.plain
          import anthill.prelude.{Unit}
          sort Unregistered end
          sort W
            entity w
            operation ping(x: W) -> Unit effects Unregistered
          end
        end
    "#,
    );
    assert!(
        refused_unregistered(&errs, "Unregistered"),
        "an unregistered label must be refused, naming the label and `fact Effect[…]`; \
         got: {errs:#?}"
    );
}

#[test]
fn a_parameterized_label_is_judged_by_its_base_sort() {
    // A label carrying bindings is judged on the sort it APPLIES, not on the
    // application: `Tag[T = Int64]` asks whether `Tag` is an effect kind. Kept apart from
    // the bare row above because the two arrive as different `TypeHead`s
    // (`Parameterized` vs `SortRef`), and a predicate written against one of them would
    // pass this file while admitting the other — the trap `check_modify_targets`'
    // neighbouring pair records.
    let errs = load_errors(
        r#"
        namespace vm3yb.parameterized
          import anthill.prelude.{Unit, Int64}
          sort Tag
            sort T = ?
          end
          sort W
            entity w
            operation ping(x: W) -> Unit effects Tag[T = Int64]
          end
        end
    "#,
    );
    assert!(
        refused_unregistered(&errs, "vm3yb.parameterized.Tag"),
        "a parameterized label must be judged by its base sort; got: {errs:#?}"
    );
}

#[test]
fn a_guarded_atom_is_judged_on_its_label() {
    // A row element is not always the bare label — a guarded atom rides a
    // `guarded(label, guard)` wrapper (WI-478) whose own functor is what a naive
    // predicate would answer about. `peel_effect_atom` is shared with
    // `check_modify_targets` precisely so this rule holds for one spelling only by
    // accident of implementation.
    //
    // CONTROL: drop the `guarded` arm from `peel_effect_atom` and this row loads clean
    // while `an_unregistered_label_is_refused_…` stays red.
    let errs = load_errors(
        r#"
        namespace vm3yb.guarded
          import anthill.prelude.{Unit, Int64}
          sort Boom end
          sort W
            entity w
            operation ping(x: W, b: Int64) -> Unit
              effects { Boom :- eq(b, 0) }
            = ()
          end
        end
    "#,
    );
    assert!(
        refused_unregistered(&errs, "vm3yb.guarded.Boom"),
        "a guard must not hide an unregistered label; got: {errs:#?}"
    );
}

#[test]
fn a_lacks_atom_is_judged_on_its_label() {
    // `-Boom` is a LACKS constraint (§5.5), and a misspelled one constrains nothing while
    // reading as though it did — the same silent-wrong-answer this pass exists for, in
    // the one row position where the label is asserted ABSENT. Included deliberately
    // rather than by inheritance: `peel_effect_atom` reaches it, and this row is what
    // says that reach is intended.
    let errs = load_errors(
        r#"
        namespace vm3yb.lacks
          import anthill.prelude.{Unit}
          sort Boom end
          sort W
            entity w
            operation ping(x: W) -> Unit effects { -Boom }
          end
        end
    "#,
    );
    assert!(
        refused_unregistered(&errs, "vm3yb.lacks.Boom"),
        "a lacks atom must be judged on its label too; got: {errs:#?}"
    );
}

#[test]
fn an_unimported_effect_registers_nothing_and_the_label_is_refused() {
    // THE SHAPE THAT SHIPPED A REVIEW CYCLE. `wi698_row_param_refinement_test`'s fixture
    // wrote exactly this — `fact Effect[T = Reg]` with `Effect` MISSING from the import
    // list — where the head mints a bare global predicate that is not
    // `anthill.prelude.Effect`, so no provision is emitted and nothing is registered. The
    // suite was green throughout.
    //
    // The FACT half of that (a fact whose functor resolves to nothing, admitted silently)
    // is NOT fixed here and is not this pass's to fix: it is `remap_name_str`'s bare-
    // `intern` fallback being final at a fact head, WI-20260821-RDGQC's first measured
    // bullet. What this row pins is that its effects CONSEQUENCE is no longer invisible —
    // the label fails even though the registration line is present and looks right.
    let errs = load_errors(
        r#"
        namespace vm3yb.unimported
          import anthill.prelude.{Unit}
          sort Reg end
          fact Effect[T = Reg]
          sort W
            entity w
            operation ping(x: W) -> Unit effects Reg
          end
        end
    "#,
    );
    assert!(
        refused_unregistered(&errs, "vm3yb.unimported.Reg"),
        "an un-imported `Effect` registers nothing, so the label must still be refused; \
         got: {errs:#?}"
    );
}

#[test]
fn an_alias_is_followed_to_its_target() {
    // AN ALIAS IS A NAME, NOT AN EXEMPTION. `sort Nope = Boom` makes `Nope` another way
    // to write `Boom`, so `effects Nope` asks the registration question about `Boom`.
    //
    // CONTROL, and it is why this row exists: the pass's first cut exempted every
    // `resolve_sort_alias` hit — meaning to exempt row parameters, and catching declared
    // aliases with them. MEASURED, this exact program loaded CLEAN under it, laundering an
    // unregistered kind one indirection away from the refusal. Nothing in the corpus
    // exercises it (every prelude row parameter is a hole), so only this row does.
    let errs = load_errors(
        r#"
        namespace vm3yb.alias
          import anthill.prelude.{Unit}
          sort Boom end
          sort W
            sort Nope = Boom
            entity w
            operation ping(x: W) -> Unit effects Nope
          end
        end
    "#,
    );
    assert!(
        refused_unregistered(&errs, "vm3yb.alias.Boom"),
        "an alias must be followed to the kind it names; got: {errs:#?}"
    );
}

#[test]
fn a_bound_effect_row_parameter_is_judged_on_its_binding() {
    // `effects E = Kind` is a documented spelling (`effects-runtime.anthill:6` —
    // `effects E = X ≡ sort E = X requires EffectsRuntime[Effects = E]`), and its BOUND is
    // judged nowhere else: the declaration site is not walked, so if the use site were
    // exempt as a row parameter the binding would never be asked about at all. Its
    // control is `a_sorts_own_effect_row_parameter_is_not_a_label` — the same declaration
    // left as a HOLE, which must keep loading.
    let errs = load_errors(
        r#"
        namespace vm3yb.bound_row_param
          import anthill.prelude.{Unit}
          sort Boom end
          sort W
            effects E = Boom
            entity w
            operation ping(x: W) -> Unit effects E
          end
        end
    "#,
    );
    assert!(
        refused_unregistered(&errs, "vm3yb.bound_row_param.Boom"),
        "a BOUND row parameter must be judged on what it is bound to; got: {errs:#?}"
    );
}

#[test]
fn the_repair_the_message_names_actually_loads() {
    // A LOAD-BLOCKING REFUSAL OWES WORKING ADVICE, and for a sort-NESTED kind the obvious
    // wording does not work: "write `fact Effect[T = Beep]` at namespace level" sends the
    // author to a line that yields `unresolved name 'Beep'` plus a carrier-less provision
    // error, with the original refusal still standing. So the message says WHERE the short
    // name is in scope, and this row drives that by applying the advice: the same program,
    // refused, then repaired with the `provides` form the message names, must load.
    let refused = load_errors(
        r#"
        namespace vm3yb.nested_kind
          import anthill.prelude.{Unit}
          sort Host
            sort Beep end
          end
          sort W
            import vm3yb.nested_kind.Host.{Beep}
            entity w
            operation ping(x: W) -> Unit effects Beep
          end
        end
    "#,
    );
    assert!(
        refused_unregistered(&refused, "vm3yb.nested_kind.Host.Beep"),
        "a sort-nested kind must be refused like any other; got: {refused:#?}"
    );
    assert!(
        refused
            .iter()
            .any(|e| e.contains("inside the sort that declares it")),
        "the message must say WHERE the short name is in scope; got: {refused:#?}"
    );
    let repaired = load_errors(
        r#"
        namespace vm3yb.nested_kind_fixed
          import anthill.prelude.{Unit, Effect}
          sort Host
            sort Beep end
            provides Effect[T = Beep]
          end
          sort W
            import vm3yb.nested_kind_fixed.Host.{Beep}
            entity w
            operation ping(x: W) -> Unit effects Beep
          end
        end
    "#,
    );
    expect_clean(&repaired, "the repair the message names");
}

// ── The two registration spellings ───────────────────────────────────

#[test]
fn a_namespace_level_fact_registers_the_kind() {
    // The CONTROL for `an_unregistered_label_is_refused_…`: the same program with the
    // registration written. Load-bearing now — deleting the `fact` line turns this row
    // red, which is exactly what `wi329_handler_discharge_test` and
    // `wi698_row_param_refinement_test` MEASURED as untrue before this ticket.
    let errs = load_errors(
        r#"
        namespace vm3yb.fact_spelling
          import anthill.prelude.{Effect, Unit}
          sort Beep end
          fact Effect[T = Beep]
          sort W
            entity w
            operation ping(x: W) -> Unit effects Beep
          end
        end
    "#,
    );
    expect_clean(&errs, "a `fact Effect[T = Beep]`-registered label");
}

#[test]
fn a_sort_level_provides_registers_the_kind() {
    // THE SPELLING THE TICKET'S CENSUS MISSED, and the reason this check could be
    // switched on rather than staged. `provides Effect[T = K]` inside a sort is how
    // `Clock` (time.anthill) and the three Console kinds (console.anthill) are registered
    // — the ticket counted `fact Effect[…]` only and concluded those labels were
    // unregistered and that the corpus would be refused.
    //
    // It is not a second reader in the pass, either: both spellings land as one
    // `SortProvidesInfo` provision, which is what `registered_effect_kinds` walks. The
    // row above and this one are therefore the SAME leg reached two ways, and that is the
    // claim being pinned.
    let errs = load_errors(
        r#"
        namespace vm3yb.provides_spelling
          import anthill.prelude.{Effect, Unit}
          sort Host
            sort Beep end
            provides Effect[T = Beep]
          end
          sort W
            import vm3yb.provides_spelling.Host.{Beep}
            entity w
            operation ping(x: W) -> Unit effects Beep
          end
        end
    "#,
    );
    expect_clean(&errs, "a `provides Effect[T = Beep]`-registered label");
}

#[test]
fn a_wildcard_registration_admits_every_application() {
    // `fact Effect[T = Tag[?]]` — the prelude's own spelling for `Modify` and `Error` —
    // registers the KIND, so any application of it is admitted. This is also where the
    // pass's one measured design decision is driven: the raw fact head carries `Tag[?]`
    // POSITIONALLY, which `type_head` reads as malformed, and only the provision path's
    // `canonicalize_fact_binding_value` re-lowers it onto `Tag`'s declared params
    // (WI-449). A clause-walking reader finds the bare registrations and misses this one
    // — measured over the corpus at 5 kinds of 11.
    let errs = load_errors(
        r#"
        namespace vm3yb.wildcard
          import anthill.prelude.{Effect, Unit, Int64}
          sort Tag
            sort T = ?
          end
          fact Effect[T = Tag[?]]
          sort W
            entity w
            operation ping(x: W) -> Unit effects Tag[T = Int64]
          end
        end
    "#,
    );
    expect_clean(&errs, "an application of a wildcard-registered kind");
}

// ── The boundary: what is NOT a label ────────────────────────────────

#[test]
fn a_sorts_own_effect_row_parameter_is_not_a_label() {
    // `effects E = ?` (WI-320) lowers to a type parameter, so `effects E` heads as a
    // `SortRef` to `W.E` — indistinguishable from a sort reference except by its
    // `SortAlias`, which is what the pass's one exemption reads. A row VARIABLE is a hole
    // for a row, not a label naming a kind.
    //
    // CONTROL: drop the `resolve_sort_alias` exemption from `effect_label_kind` and this
    // row is refused — along with seven prelude sorts (`Function.E`, `Iterable.E`,
    // `MappedStream.EF`/`ES`, `FiniteCollection.E`, `Iteration.Effect`,
    // `PersistentCollection.Effect`), i.e. the stdlib stops loading and every row in this
    // file fails with it.
    let errs = load_errors(
        r#"
        namespace vm3yb.row_param
          import anthill.prelude.{Unit}
          sort W
            effects E = ?
            entity w
            operation ping(x: W) -> Unit effects E
          end
        end
    "#,
    );
    expect_clean(&errs, "a sort's own declared effect row parameter");
}

#[test]
fn a_label_inside_a_parameters_arrow_row_is_not_checked() {
    // THE SCOPE BOUNDARY, MEASURED RATHER THAN STATED — the twin of
    // `wi347_override_refinement_test::a_type_target_inside_a_parameters_arrow_row_is_
    // not_checked`, and the same limit for the same reason: `all_operation_effects` walks
    // an OPERATION's own declared row, and an effect row nested in a PARAMETER's arrow
    // type is a different position it does not reach. The exact spelling refused by
    // `an_unregistered_label_is_refused_…` loads clean one level in.
    //
    // NOT a claim the arrow position is lawful — it is unmeasured. This row exists so the
    // asymmetry cannot drift silently: it fails the day that position starts being
    // checked, which is when the pass doc must change with it.
    let errs = load_errors(
        r#"
        namespace vm3yb.arrow_row
          import anthill.prelude.{Int64}
          sort Boom end
          sort W
            operation handle(body: (Int64) -> Int64 @ {Boom}) -> Int64
          end
        end
    "#,
    );
    assert!(
        !refused_unregistered(&errs, "Boom"),
        "the arrow position is NOT checked today — if this now refuses, update \
         `check_effect_registration`'s scope paragraph with it; got: {errs:#?}"
    );
}

#[test]
fn the_prelude_effect_kinds_are_all_registered() {
    // DRIVES THE REGISTRATION READER ITSELF rather than inferring it from a clean load: a
    // pass that read NOTHING would also leave every row above green except the refusals.
    // Asserts the set the corpus census recorded — the four in effects.anthill, `External`
    // (a `fact`), and `Clock` plus the three Console kinds (all `provides`) — through
    // operations that declare each one.
    //
    // TWO operations, not one, and the split is a real rule rather than tidiness:
    // proposal 054 §"Branch and External" refuses a row carrying BOTH `Branch` and
    // `External`, so the nine labels do not fit on one row. Measured — a single-row first
    // draft was refused for exactly that, by a check this ticket does not touch.
    let src = r#"
        namespace vm3yb.every_prelude_kind
          import anthill.prelude.{Unit, Int64, Console, Time, External, Error,
                                  Suspension, Branch, Modify}
          import anthill.prelude.Console.{ConsoleOutput, ConsoleError, ConsoleInput}
          import anthill.prelude.Time.{Clock}
          sort W
            entity w
            operation ping(x: W) -> Unit
              effects {Modify[x], Error[Int64], Suspension, External,
                       Clock, ConsoleOutput, ConsoleError, ConsoleInput}
            operation pong(x: W) -> Unit
              effects {Branch}
          end
        end
    "#;
    let errs = load_errors(src);
    expect_clean(&errs, "every registered prelude effect kind");
    // And the KB really finished loading — `try_load_kb_with` returns `Ok` only then, so
    // this also pins that the rows above were type-checked rather than skipped.
    let kb: KnowledgeBase = crate::common::try_load_kb_with(src).expect("loads");
    for op in ["vm3yb.every_prelude_kind.W.ping", "vm3yb.every_prelude_kind.W.pong"] {
        assert!(
            kb.try_resolve_symbol(op).is_some(),
            "the operation carrying the registered labels must be in the KB: {op}"
        );
    }
}
