//! WI-20260911-7TN1Q — THE OCCURS CHECK IS ALIAS-AWARE: a bracket binding whose VALUE
//! MENTIONS the parameter it binds is a LOAD ERROR, not a stack overflow.
//!
//! THE DEFECT. A call-site bracket written inside the sort whose parameter it names, with
//! a value mentioning that parameter — `Box.empty[T = Option[T = T]]()` inside
//! `sort Box[T]` — did not terminate. `anthill load` aborted:
//!
//! ```text
//! thread 'main' has overflowed its stack
//! fatal runtime error: stack overflow, aborting
//! ```
//!
//! MEASURED at 189f7603 on all six programs below (three values × two spellings), and at
//! its parent b7896119 on the three CALLEE ones — the receiver spelling loaded clean
//! there only because WI-20260911-RS2G4 had not yet made its bracket BIND, so the value
//! was dropped. This is therefore a defect WI-841 opened and RS2G4 widened by one
//! spelling, and RS2G4's own header says so in prose rather than as a row, because a row
//! whose failure mode is an ABORT takes the whole test binary with it.
//!
//! THE CAUSE. The written inner `T` does not lower to `Term::Var(?T_Box)`; it lowers to
//! `Term::Ref(Box.T)`, the parameter's SYMBOL. `occurs_in` walked `Term::Var` and
//! `Term::Fn` and had no `Term::Ref` arm, so it saw nothing and `bind_resolved` accepted
//! `?T_Box := Option[T = Ref(Box.T)]`. `walk_type` DOES resolve that `Ref` — through
//! `is_sort_param_symbol` + `resolve_sort_alias` — back to `?T_Box`, so the binding is
//! cyclic THROUGH THE ALIAS and `walk_type_deep_g` chases it until the stack ends. Three
//! measurements ON THE TICKET located it rather than guessing, each with a temporary
//! tripwire since removed: a depth tripwire in `unify_types` never
//! fired while the same tripwire in `walk_type_deep_g` fired immediately on the same `T`;
//! tripwires asserting `occurs_in` / `occurs_in_view` of every incoming value at
//! `Substitution::bind_term` / `bind_value` NEVER fired (no single binding is cyclic *to
//! the check as it was*); and at the seeding site `occurs_in_view` answered FALSE on the
//! written value. Back-out (B) below is this file's own confirmation of which reader the
//! cycle runs through.
//!
//! THE FIX, two parts, and the second is not cosmetic:
//!   1. `occurs_in` gains a `Term::Ref(s)` arm and `occurs_in_view`'s bare head asks the
//!      same question, both through `sort_param_ref_is_var` — which mirrors `walk_type`'s
//!      alias hop EXACTLY (the same `is_sort_param_symbol` gate, the same
//!      `resolve_sort_alias` read), so the occurs check refuses precisely the bindings
//!      the walk can chase. That ends the abort. Of the two halves of that predicate only
//!      the VID COMPARISON is load-bearing: the gate forced open leaves all three corpora
//!      loading with identical counts and `anthill-core`'s 6045 tests green, while
//!      dropping the comparison costs a control — back-out (E) below. The gate stays for
//!      the correspondence with the walk, which is this arm's whole justification, and the
//!      predicate's doc says that rather than implying a row needs it.
//!   2. With the binding refused, the CALLEE spelling LOADED CLEAN — `seed_op_type_args`
//!      discards `unify_types`' verdict, so the refusal was silent and the call typed at
//!      whatever the context wanted. That is the RS2G4 defect one channel over, so the
//!      callee site now reads the verdict for this ONE fault and reports it; the
//!      WI-367 / WI-379 discard of a disagreement with an ALREADY-PINNED parameter is
//!      untouched. The receiver spelling already had the message (RS2G4 wrote it against
//!      exactly this refusal); both now render it from one builder.
//!
//! FIVE BACK-OUTS, EACH A MUTATION (the site still runs, its answer is discarded), each
//! measured separately over this file's 8 rows. TWO OF THEM ABORT THE BINARY rather than
//! turning rows red — a stronger signal than a failure count, and the reason RS2G4 could
//! not write these rows before the fix:
//!
//! **(A) `sort_param_ref_is_var` answers `false`** — the alias-aware occurs check off
//! entirely: the binary DIES. `fatal runtime error: stack overflow, aborting`, SIGABRT,
//! no `test result:` line at all, at whichever arm row runs first.
//!
//! **(B) `occurs_in`'s `Term::Ref` arm alone off**: the SAME abort. That arm is the one
//! the cycle actually runs through — a bracket value arrives hash-consed, so the binding
//! is refused (or not) in the `TermId` reader. Which makes (A) and (B) one measurement of
//! two spellings, and (C) below the one that isolates the other reader.
//!
//! **(C) `occurs_in_view`'s bare-head arm alone off**: **5 red, NO abort** — every arm
//! row, both channels ([`the_callee_bracket_mentioning_its_own_parameter_is_refused`],
//! [`the_receiver_bracket_mentioning_its_own_parameter_is_refused`],
//! [`the_mention_is_found_at_depth`], [`the_two_spellings_refuse_alike`],
//! [`the_refusal_says_why_it_is_a_representation_limit`]). No abort, because (B) still
//! refuses the binding; they are red because this is the reader BOTH seeding legs'
//! `mentions` question goes through, so without it the refusal is SILENT again — the
//! defect part 2 exists for, arriving from the other side.
//!
//! **(D) the callee seeding leg off** (`if !agreed && !prior && mentions` never taken):
//! **4 red** — the same set minus the receiver row, whose own leg still reports. (C) and
//! (D) sit in SERIES on the callee path — the view reader asks the question, the leg
//! reports the answer — so each is necessary for those 4 and they are not two independent
//! mechanisms: backing out both gives the same 4, not 8.
//!
//! **(E) the vid comparison dropped** — `sort_param_ref_is_var` answers "is `sym` ANY
//! sort parameter" instead of "is it THIS one", the single most plausible way to write
//! this check wrong: **1 red**, [`another_sorts_parameter_in_the_value_still_loads`]
//! alone, with every arm row green. That control is therefore the only thing standing
//! between the delivered check and one that refuses a legitimate program — the thing the
//! ticket's census was for. By contrast the OTHER half of that predicate, the
//! `is_sort_param_symbol` gate, is NOT load-bearing: forced open, the three corpora load
//! with identical fact/rule counts and `anthill-core`'s 6045 tests pass. It stays for the
//! correspondence with `walk_type`, which is this arm's whole justification, and its doc
//! says exactly that rather than implying a row needs it.
//!
//! The RECEIVER rows are red under (A) and (B) BY ABORT, not by message: the receiver
//! spelling has reached the cycle since RS2G4. Their message is RS2G4's own arm, reached
//! at last now that the binding is refused, and [`the_two_spellings_refuse_alike`] is a
//! PIN on the two channels rendering from one builder rather than a measurement of a
//! mechanism.
//!
//! WHAT NO ROW DRIVES, and it is one of `/code-review`'s findings: the receiver leg reads
//! `mentions` as a FACT instead of inferring it from `prior` being `None`, because
//! `bind_resolved` also answers `false` on σ's STICKY contradiction flag — which
//! `seed_op_type_args` runs FIRST on the same σ and can have set, so a CORRECT receiver
//! binding of a free parameter used to render the cyclic-value message. No program here
//! reaches that state (it needs a conflict recorded earlier in the same expression on the
//! shared canonical parameter var), so the change is reasoned, not measured; what the
//! rows above do show is that reading the fact costs the honest rows nothing. The
//! `continue` it enables is not a silent skip: the re-bind that set the flag also recorded
//! a `contradiction_details` entry, and `enforce_member_tie` renders THAT as the refusal.
//!
//! WHAT NO ROW MEASURES, said rather than implied: `occurs_in_view`'s bare-head arm in
//! its OTHER role, inside `bind_resolved`'s non-`Term` carrier path. Nothing in `stdlib/`,
//! the examples, or this file brings a bracket value to that reader with a bare parameter
//! head — a `Value::Node` type routes its interned children back to `occurs_in`. The arm
//! is there because the two readers must not disagree about what an occurrence IS: the
//! moment one does, the same cyclic binding lands unrefused on whichever carrier the
//! producer happened to mint. That is the invariant `occurs_in_view`'s own doc already
//! states for nested bindings, one shape wider.
//!
//! CONTROLS, green under (A)–(D) and each stated at its site:
//! [`the_parameter_bound_to_itself_still_loads`] (the value IS the parameter — what
//! separates "cyclic" from "self-referential at all", and the row a seeding leg that
//! asked `mentions` WITHOUT the verdict gate would fail),
//! [`another_sorts_parameter_in_the_value_still_loads`] (the mention is of a parameter
//! this binding does NOT bind) and [`a_concrete_bracket_value_still_loads`].

//!
//! THE CENSUS the ticket asked for — "how many bindings are newly refused, and whether
//! any of them is a legitimate program" — over all three corpora and the full suite, with
//! a temporary probe (since removed) appending one line per firing of the new arm; every
//! row of it loads `stdlib/`. `stdlib` + an empty program: **0 firings**.
//! `examples/github-todo` (7 files, 3004 facts): **0**. `rustland/anthill-todo/anthill`
//! (7 files, 4487 facts): **0**. The full workspace suite: **6877 passed, 0 failed, 0
//! firings**. Measured with part 1 in and part 2 not yet written, so the suite figure is
//! what the OCCURS WIDENING alone does to a corpus that predates this file — it refuses
//! nothing that existed, which is why there was no newly-refused program to judge
//! legitimate. The gate is what makes that true; see `sort_param_ref_is_var`.
//!
//! REFERENCE: `occurs_in` / `occurs_in_view` / `sort_param_ref_is_var` and
//! `bracket_binding_mentions_its_parameter` (typing.rs); `resolve_sort_alias` +
//! `build_sort_alias_index` (WI-659); WI-841 (the bracket's sort scope);
//! WI-20260911-RS2G4 (the receiver spelling).

use crate::common::try_load_kb_with;

/// One KB per row. The arms are LOAD ERRORS, so a shared namespace would kill the
/// controls with them and the measurement would discriminate nothing.
fn load_errors(member: &str) -> Vec<String> {
    let src = format!(
        r#"
namespace test.tn1q
  import anthill.prelude.{{Option, none, List, Int64}}

  sort Letter
    entity la
    entity lb
  end

  sort Duo[A, B]
    entity duo(x: A, y: B)
    operation pairOf() -> Option[T = Duo[A = A, B = B]] = none()
  end

  sort Box[T]
    entity box(v: T)
    operation empty() -> Option[T = T] = none()
{member}
  end
end
"#
    );
    match try_load_kb_with(&src) {
        Ok(_) => Vec::new(),
        Err(es) => es.to_vec(),
    }
}

/// Strip the leading `<line>:<col>: ` so the two spellings can be compared for the
/// MESSAGE, which is what "one fault, two spellings" claims.
fn message_only(errs: Vec<String>) -> Vec<String> {
    errs.into_iter()
        .map(|e| e.split_once(": ").map(|(_, m)| m.to_string()).unwrap_or(e))
        .collect()
}

// ── THE ARMS ─────────────────────────────────────────────────────────────────────

/// The three values the ticket names, in the CALLEE spelling. Each ABORTED the loader
/// before this delivery; each is now one load error naming the parameter and the value.
/// `Box`, `Option` and `List` because a single constructor could not tell "the sort's own
/// parameter" from "any application".
#[test]
fn the_callee_bracket_mentioning_its_own_parameter_is_refused() {
    for value in ["Box[T = T]", "Option[T = T]", "List[T = T]"] {
        let errs = load_errors(&format!(
            "    operation probe() -> Option[T = T] = Box.empty[T = {value}]()"
        ));
        assert_eq!(errs.len(), 1, "{value}: {errs:#?}");
        assert!(
            errs[0].contains("expected a type argument for 'T' that does not mention 'T' itself"),
            "{value}: {errs:#?}"
        );
        assert!(
            errs[0].ends_with(&format!("got {value}")),
            "{value}: {errs:#?}"
        );
    }
}

/// The same three in the RECEIVER spelling — the one WI-20260911-RS2G4 made bind. Its
/// message was written against exactly this refusal and had never been reachable: before
/// the occurs check saw the alias, the binding was ACCEPTED and the loader overflowed.
#[test]
fn the_receiver_bracket_mentioning_its_own_parameter_is_refused() {
    for value in ["Box[T = T]", "Option[T = T]", "List[T = T]"] {
        let errs = load_errors(&format!(
            "    operation probe() -> Option[T = T] = Box[T = {value}].empty()"
        ));
        assert_eq!(errs.len(), 1, "{value}: {errs:#?}");
        assert!(
            errs[0]
                .contains("expected a receiver binding for 'T' that does not mention 'T' itself"),
            "{value}: {errs:#?}"
        );
        assert!(
            errs[0].ends_with(&format!("got {value}")),
            "{value}: {errs:#?}"
        );
    }
}

/// THE MENTION IS FOUND AT DEPTH, both spellings. `Option[T = Option[T = T]]` puts the
/// `Ref(Box.T)` two constructors down, so a check that only looked at the value's own head
/// — the shape a reader might expect from "the value IS the parameter" — passes every row
/// above and fails this one.
#[test]
fn the_mention_is_found_at_depth() {
    let value = "Option[T = Option[T = T]]";
    for (spelling, channel) in [
        (format!("Box.empty[T = {value}]()"), "a type argument"),
        (format!("Box[T = {value}].empty()"), "a receiver binding"),
    ] {
        let errs = load_errors(&format!(
            "    operation probe() -> Option[T = T] = {spelling}"
        ));
        assert_eq!(errs.len(), 1, "{spelling}: {errs:#?}");
        assert!(
            errs[0].contains(&format!(
                "{channel} for 'T' that does not mention 'T' itself"
            )),
            "{spelling}: {errs:#?}"
        );
        assert!(
            errs[0].ends_with(&format!("got {value}")),
            "{spelling}: {errs:#?}"
        );
    }
}

/// ONE FAULT, TWO SPELLINGS. Proposal 035 lists the receiver and the callee bracket as two
/// ways of writing one thing, so it is not enough that both refuse: they must refuse at
/// the same SITE with the same bytes but for the noun naming which bracket was written.
/// Compared as whole messages, not by `contains`, so a difference anywhere in them fails.
#[test]
fn the_two_spellings_refuse_alike() {
    let callee = message_only(load_errors(
        "    operation probe() -> Option[T = T] = Box.empty[T = Option[T = T]]()",
    ));
    let recv = message_only(load_errors(
        "    operation probe() -> Option[T = T] = Box[T = Option[T = T]].empty()",
    ));
    assert_eq!(callee.len(), 1, "{callee:#?}");
    assert_eq!(
        callee[0].replace("a type argument", "a receiver binding"),
        recv[0],
        "the two spellings differ by more than the channel noun"
    );
}

/// THE MESSAGE SAYS WHY, and the clause is pinned because it is the whole difference
/// between "you wrote something illegal" and "the kernel cannot represent this".
/// `Box.empty[T = List[T = T]]()` — the same operation at the instance whose element is a
/// `List` of my own `T` — is a well-formed INTENT; it is unexpressible only because a
/// bracket binds the ENCLOSING sort's canonical parameter variable, so the callee's `T`
/// and this instance's `T` are one variable. Found by `/code-review`, which read the bare
/// refusal as blaming the author. Giving the callee's parameters fresh variables is what
/// would make the family expressible; that is a design change and is NOT in this ticket.
#[test]
fn the_refusal_says_why_it_is_a_representation_limit() {
    let errs = load_errors("    operation probe() -> Option[T = T] = Box.empty[T = List[T = T]]()");
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(
        errs[0].contains(
            "the bracket binds the ENCLOSING sort's own 'T', so a value mentioning it \
             would be cyclic"
        ),
        "{errs:#?}"
    );
}

// ── THE CONTROLS ─────────────────────────────────────────────────────────────────

/// THE CONTROL THAT SEPARATES "CYCLIC" FROM "SELF-REFERENTIAL AT ALL": the value IS the
/// parameter. `?T := ?T` is the identity, not a cycle, and `unify_types` returns on its
/// identity fast-path before `bind_resolved` is reached — which is why the seeding legs
/// gate on the VERDICT and not on the occurs question alone (they would refuse this row).
/// GREEN UNDER ALL FIVE BACK-OUTS: the row a seeding leg that asked `mentions` WITHOUT
/// the verdict gate would fail.
#[test]
fn the_parameter_bound_to_itself_still_loads() {
    assert_eq!(
        load_errors("    operation probe() -> Option[T = T] = Box.empty[T = T]()"),
        Vec::<String>::new(),
    );
    assert_eq!(
        load_errors("    operation probe() -> Option[T = T] = Box[T = T].empty()"),
        Vec::<String>::new(),
    );
}

/// THE CONTROL THAT SEPARATES "THIS PARAMETER" FROM "A PARAMETER". The value mentions
/// `Box`'s `T` while the binding it is a value FOR is `Duo`'s `A` — nothing cyclic, so it
/// must be accepted. And the row DRIVES that acceptance rather than only observing a clean
/// load: a disagreeing annotation reports `A = Box[T = …]`, which only the bracket could
/// have put in the `A` slot. (The inner `T` prints as `?_` — the enclosing instance's
/// parameter is unbound in this body, which is not what this row measures.)
#[test]
fn another_sorts_parameter_in_the_value_still_loads() {
    let errs = load_errors(
        "    operation probe() -> Int64 =\n      \
         let v: Option[T = Duo[A = Letter, B = Int64]] = Duo.pairOf[A = Box[T = T], B = Int64]()\n      0",
    );
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains("v.annotation (let-binding)"), "{errs:#?}");
    assert!(
        errs[0].contains("got Option[T = Duo[A = Box[T = ?_], B = Int64]]"),
        "the bracket's value must have reached Duo's A: {errs:#?}"
    );
}

/// The ordinary case, kept as a smoke control: a bracket value that names no parameter at
/// all is untouched by any of this, in both spellings.
#[test]
fn a_concrete_bracket_value_still_loads() {
    assert_eq!(
        load_errors("    operation probe() -> Option[T = Letter] = Box.empty[T = Letter]()"),
        Vec::<String>::new(),
    );
    assert_eq!(
        load_errors("    operation probe() -> Option[T = Letter] = Box[T = Letter].empty()"),
        Vec::<String>::new(),
    );
}
