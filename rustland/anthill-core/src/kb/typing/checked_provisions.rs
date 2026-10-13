//! WI-20261011-A3NND — A SEALED LOAD'S PROVISIONS ARE CHECKED ONCE: which rows a run of
//! [`check_provider_requires`] reads, what makes it read all of them, and the two
//! instruments that say it skipped nothing it should have checked.
//!
//! The check took no list of what a load added: every provision of the KB was resolved
//! again at every load. MEASURED (`docs/measurements/test-infrastructure/
//! provider-requires-2026-10-11.txt`), a one-operation file into a copy of the sealed
//! standard library: 27 ms of that 65 ms load, 93 % of it the resolver answering 127
//! goals whose answers the library's own load had already had — each a walk of every
//! provision of the goal's spec.
//!
//! So behind a seal the check reads the rows a seal does NOT hold as checked
//! ([`crate::kb::load::SealedDeclarations::checked_provisions`]) — everything asserted
//! since, a refused load's rows included, at every run: it reads the KB and not the
//! load, for the reason `typing::sealed`'s refusals do. Nothing sealed, nothing
//! skipped: a plain sequence of loads, and `KB.loaded` over one, checks every provision
//! at every load as before.
//!
//! WHAT A LATER LOAD CAN CHANGE OF A HELD VERDICT, and what the check does about each
//! (user, 2026-10-11: it checks EVERY row then, as it did; no new refusal). A verdict is
//! the resolver's answer to each `requires` of the provided spec at the provision's
//! bindings ([`Reaches`] names each way in):
//!
//!   * a `requires` — the spec's own, which are the goals, or the carrier's, which are
//!     the assumptions. One written since for a sort that was there already changes
//!     both. (The loader refuses that where it is written, and asserts the fact all the
//!     same: this check is what refuses the KB at the load after.)
//!   * a TYPE PARAMETER declared since for a sort that was there. A `requires` naming a
//!     sort with no type parameter is a refinement and asks for no dictionary
//!     (`clause_is_dispatchable`); given one, and no constructor, it is a demand nothing
//!     answers. Found by
//!     /code-review, reproduced: `namespace lib.Boom  sort U = ?  end` over a sealed
//!     `sort Narrow requires Boom` is refused where it is written and the parameter is
//!     registered all the same.
//!   * a provision's CLAUSES — a condition written since for a provider that was there;
//!   * WHO ANSWERS A GOAL. A goal of a held provision names types that existed when it
//!     was checked, and its carrier's own parameters. A provision asserted since is no
//!     candidate at such a goal when its provider is the later load's own and one of its
//!     bindings is headed by a type of the later load's own that is nothing but itself
//!     ([`is_inert`]): a concrete type matches a head that is that type, a parameter, a
//!     spec it provides, or an alias of one of those, and a rigid matches a parameter.
//!     Every other provision asserted since — for an earlier provider, with no such
//!     binding, with one a goal could reach through a provision — is taken to be one.
//!
//! A clause of those relations that their one decoder does not read is read by no
//! reader of them — the check's own, the candidate search, the chain — and reaches no
//! verdict.
//!
//! ONE GOAL SHAPE BREAKS THAT ARGUMENT, and is why a load may not be held at all: a goal
//! with a binding left OPEN — an unbound variable no σ makes rigid — matches any head.
//! A run that puts such a goal to the candidate search is not held checked
//! ([`ProvisionCheck::held`]), so every later load checks its rows again.
//! MEASURED: the standard library's own load puts none, and of the 10 939 loads of
//! `anthill-core`'s suite nine put one each (the raw file's §12). NO ROW DRIVES THIS
//! GUARD: six of the nine are fixtures this check refuses, which is not held for that
//! reason already, and no fixture was found that puts an open goal to the search and
//! loads clean. It is kept because the argument above is false without it.
//!
//! WHAT THIS DOES NOT DO. A fact that reaches a held verdict stays in the KB, so every
//! later load into that KB reads every row again — a program with one witness of a
//! library spec for a library type pays the full check at each load after it, as every
//! load did. And a seal that holds no provision says so nowhere but the timing line
//! (`ANTHILL_LOAD_TIMING=1`, [`ProvisionCheck::why`]): a library whose own check puts an
//! open goal is loaded as before, at the old cost.
//!
//! THE CONTROLS. A row skipped that should have been checked fails in silence — the
//! provision loads clean and dies at eval on an unbound dictionary slot. So:
//! `ANTHILL_PROVISION_ORACLE=1` makes every narrowed run check every row as well and
//! panics where the two disagree ([`provision_oracle_on`]); and
//! [`provisions_checked_by_this_thread`] counts the rows a run read, for a test that a
//! row was NOT.

use super::*;
use crate::kb::load::CheckedProvisions;
use std::cell::Cell;

thread_local! {
    /// Provision rows the check has read on this thread.
    static ROWS_CHECKED: Cell<usize> = const { Cell::new(0) };
    /// NARROWED runs of the check the oracle compared with a full one on this thread.
    static ORACLE_RUNS: Cell<usize> = const { Cell::new(0) };
    /// `Some(n)` while a run is in flight: the goals it has put to the candidate search
    /// with a binding left open.
    static OPEN_GOALS: Cell<Option<usize>> = const { Cell::new(None) };
}

/// How many provision rows [`check_provider_requires`] has read ON THIS THREAD, ever.
/// The instrument for the one thing a load's verdict cannot show: that a row was NOT
/// checked again. A test reads it before and after a load and asserts on the
/// difference (`wi_a3nnd_checked_provisions_test`); a libtest thread runs one test.
pub fn provisions_checked_by_this_thread() -> usize {
    ROWS_CHECKED.with(|n| n.get())
}

pub(super) fn count_rows_checked(rows: usize) {
    ROWS_CHECKED.with(|n| n.set(n.get() + rows));
}

/// `ANTHILL_PROVISION_ORACLE=1` — check every provision AS WELL, as every load did
/// before this ticket, and panic when the narrowed run's errors are not the full run's.
/// A TEST INSTRUMENT, read once per run of the check.
///
/// WHAT A CLEAN RUN SAYS, so that it is not read for more: where the suite holds a load
/// that changes a held verdict, the narrowed check saw it. A way in that no test writes
/// is one this cannot see.
pub(super) fn provision_oracle_on() -> bool {
    std::env::var("ANTHILL_PROVISION_ORACLE").is_ok_and(|v| v == "1")
}

/// How many NARROWED runs of the check the oracle has compared with a full one ON THIS
/// THREAD — none unless `ANTHILL_PROVISION_ORACLE=1`, and none for a run that read
/// every row anyway: there is nothing to compare such a run with, and counting it was
/// how an oracle run of a suite in which nothing was narrowed read as one that had
/// looked (/code-review). THE INSTRUMENT'S OWN CONTROL: a run under the switch that
/// compared nothing was not an oracle run, whatever colour it finished
/// (`the_oracle_runs_when_it_is_asked_for`).
pub fn provision_oracle_runs_by_this_thread() -> usize {
    ORACLE_RUNS.with(|n| n.get())
}

/// The oracle's verdict on one narrowed run: `narrowed` is what it reported, `every`
/// what a run over every row reports of the same KB.
pub(super) fn provision_oracle_verdict(
    kb: &KnowledgeBase,
    rows: &RowsToRead,
    narrowed: &[crate::kb::load::LoadError],
    every: &[crate::kb::load::LoadError],
) {
    ORACLE_RUNS.with(|n| n.set(n.get() + 1));
    let rendered = |errors: &[crate::kb::load::LoadError]| {
        let mut lines: Vec<String> = errors.iter().map(|e| e.to_string()).collect();
        lines.sort();
        lines
    };
    let (narrowed, every) = (rendered(narrowed), rendered(every));
    if narrowed == every {
        return;
    }
    // As multisets: the same line twice in one run and once in the other is a
    // difference, and is printed as one.
    let only = |a: &[String], b: &[String]| -> String {
        let mut rest: Vec<&String> = b.iter().collect();
        let lines: Vec<String> = a
            .iter()
            .filter(|l| match rest.iter().position(|r| r == l) {
                Some(at) => {
                    rest.swap_remove(at);
                    false
                }
                None => true,
            })
            .map(|l| format!("    {l}"))
            .collect();
        if lines.is_empty() {
            "    (none)".to_string()
        } else {
            lines.join("\n")
        }
    };
    panic!(
        "ANTHILL_PROVISION_ORACLE: checking EVERY provision gives something else than \
         checking the ones no seal holds (from rule slot {} of {}; {}).\n  \
         only when every row is checked:\n{}\n  only when the held rows are skipped:\n{}",
        rows.first_slot,
        kb.rules.len(),
        rows.why.said(kb),
        only(&every, &narrowed),
        only(&narrowed, &every),
    );
}

/// What one run of the check found.
pub struct ProvisionCheck {
    pub errors: Vec<crate::kb::load::LoadError>,
    /// Every row the run read HOLDS, and holds whatever a later load provides: no
    /// requirement failed, and no goal reached the candidate search with a binding left
    /// open (the module doc). What a seal needs of a load before it tells later ones
    /// not to check its provisions again.
    pub(crate) held: bool,
    /// The rows the run read, the goals it put to the candidate search with a binding
    /// left open, and from which rule slot it read and why — the timing line's
    /// (`ANTHILL_LOAD_TIMING=1`), which is how a run of the suite is counted for the
    /// loads that read every row.
    pub(crate) rows_read: usize,
    pub(crate) open_goals: usize,
    pub(crate) first_slot: usize,
    pub(crate) why: WhyTheseRows,
}

/// The goals one run of the check puts to the candidate search with a binding left
/// open, counted from [`OpenGoalCount::begin`] to [`OpenGoalCount::end`]. One run at a
/// time on a thread: a second begun inside a first is a bug in the caller, said so.
pub(super) struct OpenGoalCount {
    ended: bool,
}

impl OpenGoalCount {
    pub(super) fn begin() -> Self {
        let before = OPEN_GOALS.with(|c| c.replace(Some(0)));
        assert!(
            before.is_none(),
            "a run of the provision check began inside another on this thread"
        );
        OpenGoalCount { ended: false }
    }

    /// The open goals the run put to the candidate search.
    pub(super) fn end(mut self) -> usize {
        self.ended = true;
        OPEN_GOALS
            .with(|c| c.take())
            .expect("the count this run began is the one it ends")
    }
}

impl Drop for OpenGoalCount {
    /// A run that unwinds leaves no count behind for the next search on the thread to
    /// report to.
    fn drop(&mut self) {
        if !self.ended {
            OPEN_GOALS.with(|c| c.set(None));
        }
    }
}

/// Called by `collect_provides_candidates` for every goal it is put: one read of a
/// thread-local when no run of the check is in flight. THE GUARD RESTS ON THAT CALL: a
/// goal's candidates answered by anything that does not go through that function — a
/// memo in front of it — owes this the goal.
pub(super) fn note_candidate_search(kb: &KnowledgeBase, goal: &SortGoal, sigma: Option<&SigmaCtx>) {
    let Some(seen) = OPEN_GOALS.with(|c| c.get()) else {
        return;
    };
    let open = goal.bindings.iter().any(|(_, value)| match sigma {
        Some(ctx) => matches!(sigma_class_terminal(kb, ctx, value), Some((_, false))),
        None => matches!(elem_var_step(kb, value), Some((_, false))),
    });
    if open {
        OPEN_GOALS.with(|c| c.set(Some(seen + 1)));
    }
}

/// Which rows a run reads: those in a rule slot at or above `first_slot`.
pub(super) struct RowsToRead {
    pub(super) first_slot: usize,
    pub(super) why: WhyTheseRows,
}

/// Why a run reads from the slot it does — kept as what was found, and said only where
/// it is printed (the timing line, the oracle's report).
#[derive(Clone, Copy)]
pub(crate) enum WhyTheseRows {
    /// No seal holds a provision as checked: every row.
    NothingHeld,
    /// Something asserted since the seal can change a held verdict: every row.
    Reached(Reaches),
    /// Nothing asserted since the seal does: the rows asserted since.
    NothingReaches,
    /// The second call of a load: the rows a pass below the check asserted.
    DerivedBelowTheCheck,
}

/// A fact asserted since the seal that can change the verdict of a provision the seal
/// holds as checked — the module doc has the argument for each.
#[derive(Clone, Copy)]
pub(crate) enum Reaches {
    /// A `requires` for a sort that was there before the seal.
    Requires { sort: Symbol },
    /// A type parameter for a sort (or an operation) that was there before the seal.
    TypeParameter { owner: Symbol },
    /// A provision's condition for a provider that was there before the seal.
    Condition { provider: Symbol },
    /// A provision by a provider that was there before the seal: its chain if this is a
    /// conversion, the provision its own goals are answered by first (locality), an
    /// edge of the provides relation a goal's type is matched through.
    EarlierProvider { provider: Symbol, spec: Symbol },
    /// A provision of a spec that was there before the seal, with no binding headed by
    /// a type only a later load's goal can name.
    NoBindingOfItsOwn { provider: Symbol, spec: Symbol },
}

impl WhyTheseRows {
    pub(crate) fn said(&self, kb: &KnowledgeBase) -> String {
        let name = |s: &Symbol| kb.qualified_name_of(*s);
        match self {
            WhyTheseRows::NothingHeld => "no sealed load's provisions are held checked".to_string(),
            WhyTheseRows::NothingReaches => {
                "nothing asserted since the seal reaches a held provision".to_string()
            }
            WhyTheseRows::DerivedBelowTheCheck => "the rows asserted below the check".to_string(),
            WhyTheseRows::Reached(Reaches::Requires { sort }) => format!(
                "a `requires` was asserted since the seal for '{}', which was there before it",
                name(sort)
            ),
            WhyTheseRows::Reached(Reaches::TypeParameter { owner }) => format!(
                "a type parameter was declared since the seal for '{}', which was there before it",
                name(owner)
            ),
            WhyTheseRows::Reached(Reaches::Condition { provider }) => format!(
                "a provision's condition was asserted since the seal for '{}', which was there \
                 before it",
                name(provider)
            ),
            WhyTheseRows::Reached(Reaches::EarlierProvider { provider, spec }) => format!(
                "'{}' provides '{}' since the seal, and the provider was there before it",
                name(provider),
                name(spec)
            ),
            WhyTheseRows::Reached(Reaches::NoBindingOfItsOwn { provider, spec }) => format!(
                "'{}' provides '{}' since the seal, a spec that was there before it, at no \
                 binding headed by a type that only a later load's goal can name",
                name(provider),
                name(spec)
            ),
        }
    }
}

/// The rows a run of the check reads over `kb` as it stands.
pub(super) fn rows_a_run_reads(kb: &mut KnowledgeBase) -> RowsToRead {
    let Some(held) = kb.sealed.checked_provisions() else {
        return RowsToRead {
            first_slot: 0,
            why: WhyTheseRows::NothingHeld,
        };
    };
    match later_fact_that_reaches_a_held_verdict(kb, held) {
        Some(reaches) => RowsToRead {
            first_slot: 0,
            why: WhyTheseRows::Reached(reaches),
        },
        None => RowsToRead {
            first_slot: held.rule_slots,
            why: WhyTheseRows::NothingReaches,
        },
    }
}

/// The first fact asserted since the seal that can change the verdict of a provision the
/// seal holds as checked — the module doc has the argument. `None`: the held rows need
/// not be read.
fn later_fact_that_reaches_a_held_verdict(
    kb: &mut KnowledgeBase,
    held: CheckedProvisions,
) -> Option<Reaches> {
    // A type parameter declared since for an owner that was there.
    if let Some(owner) = kb
        .symbols
        .type_param_owners_since(held.type_params)
        .iter()
        .map(|scope| scope.owner())
        .find(|owner| !is_later(kb, held, *owner))
    {
        return Some(Reaches::TypeParameter { owner });
    }
    let later_rids = |kb: &KnowledgeBase, relation: &str| -> Vec<crate::kb::RuleId> {
        kb.try_resolve_symbol(relation)
            .map(|rel| {
                kb.rules_by_functor_iter(rel)
                    .filter(|rid| rid.index() >= held.rule_slots)
                    .collect()
            })
            .unwrap_or_default()
    };
    // A `requires` for a sort that is not the later load's own. Through the relations'
    // one decoder (`sort_clause_fields`): what it does not read, no reader does.
    for rid in later_rids(kb, "anthill.reflect.SortRequiresInfo") {
        if let Some((sort, _)) = sort_clause_fields(kb, rid, "spec") {
            if !is_later(kb, held, sort) {
                return Some(Reaches::Requires { sort });
            }
        }
    }
    // A provision's condition for a provider that is not.
    //
    // DRIVEN BY NO ROW (`wi_a3nnd_checked_provisions_test`, measured): a written
    // `provides … :- goals` files its `SortProvidesInfo` row beside the condition, and
    // the provider clause below answers for that row. Kept for a `ProvidesConditionInfo`
    // fact with no row beside it, which can be written.
    for rid in later_rids(kb, "anthill.reflect.ProvidesConditionInfo") {
        if let Some((provider, _, _)) = decoded_condition_row(kb, rid) {
            if !is_later(kb, held, provider) {
                return Some(Reaches::Condition { provider });
            }
        }
    }
    let rows: Vec<ProvidesRow> = provides_rows_from(kb, held.rule_slots).collect();
    for row in rows {
        let (provider, spec) = (row.provider, row.spec_base);
        if !is_later(kb, held, provider) {
            return Some(Reaches::EarlierProvider { provider, spec });
        }
        // A spec of the later load's own is asked by no held goal; a conversion is a
        // candidate at none, and is a chain entry of its provider alone.
        if is_later(kb, held, spec) || is_conversion_row(kb, &row) {
            continue;
        }
        let type_params = kb.type_params_of_sort(spec);
        let mut inert = false;
        for (param, value) in row.bindings(kb) {
            let name = kb.local_name_of(param).to_string();
            // An effect-row parameter a goal leaves out does not discriminate, so a
            // binding there keeps the row from no goal.
            if !type_params.contains(&name) || sort_param_is_effect_row(kb, spec, &name) {
                continue;
            }
            if sort_sym_of_view(kb, &value).is_some_and(|head| is_inert(kb, held, head)) {
                inert = true;
                break;
            }
        }
        if !inert {
            return Some(Reaches::NoBindingOfItsOwn { provider, spec });
        }
    }
    None
}

/// `sym` names something a load after the seal brought: it, and the symbol its name
/// resolves to, were interned since. Erring toward "it was there": a name an earlier
/// load spelled before a later one declared it reads as earlier. The canonical half is
/// driven by no row — no fixture was found that puts a second symbol of an earlier sort
/// in a later row's head — and can only make the check read more.
fn is_later(kb: &KnowledgeBase, held: CheckedProvisions, sym: Symbol) -> bool {
    sym.index() >= held.symbols && kb.canonical_sort_sym(sym).index() >= held.symbols
}

/// A type of the later load's own that is nothing but itself: no parameter, no alias of
/// another type, and no spec that anything provides — so no type an earlier goal names
/// IS it, stands for it, or is admitted as it through a provision.
///
/// The alias clause is driven by no row: a head written through an alias is read through
/// the view as the type it stands for, and is an earlier type before this is asked
/// (`a_provision_at_an_alias_of_a_sealed_type_reads_every_provision` passes without the
/// clause). It is for an alias a carrier leaves as its own symbol, which
/// `bare_sort_compatible` resolves to its shape when it matches a head.
fn is_inert(kb: &KnowledgeBase, held: CheckedProvisions, head: Symbol) -> bool {
    is_later(kb, held, head)
        && !is_sort_param_symbol(kb, head)
        && resolve_alias_shape(kb, head).is_none()
        && provides_rows_of_spec(kb, head).next().is_none()
}

#[cfg(test)]
mod a3nnd_seal_tests {
    use crate::kb::load;
    use crate::kb::test_support::load_stdlib;

    /// Two specs, the second requiring the first, and a type that provides neither.
    const LIB: &str = r#"
namespace test.a3seal
  import anthill.prelude.{Int64}

  sort Low
    sort T = ?
    operation low(x: T) -> Int64
  end

  sort High
    sort T = ?
    requires Low[T = T]
    operation high(x: T) -> Int64
  end

  sort Twig
    entity twig
  end
end
"#;

    const AN_INNOCENT_PROGRAM: &str = r#"
namespace test.a3seal.later
  import anthill.prelude.{Int64}
  operation eight() -> Int64 = 8
end
"#;

    /// A PROVISION ASSERTED BETWEEN A LOAD'S CHECK AND ITS SEAL IS NOT HELD AS CHECKED
    /// (/code-review). What a seal holds is the KB as the check LEFT it
    /// ([`load::LastLoad::provisions_checked`]), not as the seal finds it: a row asserted
    /// in between — here by hand; by a pass placed below the check's second call, were
    /// one written — has been read by no run, and the next load reads it. The row is
    /// `Twig provides High`, whose contract (`Low[T = Twig]`) nothing answers.
    ///
    /// FAILS with the seal taking its slot count where it is taken (`rule_slots` read at
    /// the seal for [`load::CheckedProvisions`]): the row is below it, the next load
    /// reads nothing, and loads clean.
    #[test]
    fn a_provision_asserted_between_the_check_and_the_seal_is_read_by_the_next_load() {
        let mut kb = load_stdlib(Some(LIB));
        let twig = kb.resolve_symbol("test.a3seal.Twig");
        let high = kb.resolve_symbol("test.a3seal.High");
        crate::kb::eq_derive::assert_provides(&mut kb, twig, high);
        load::seal_declarations(&mut kb);

        let parsed = crate::parse::parse(AN_INNOCENT_PROGRAM).expect("the later program parses");
        let errors: Vec<String> = load::load_all(&mut kb, &[&parsed], &load::NullResolver)
            .map(|_| ())
            .expect_err("the provision no run has read is read now, and does not hold")
            .iter()
            .map(|e| e.to_string())
            .collect();
        assert!(
            errors.iter().any(|e| {
                e.contains("'test.a3seal.Twig' provides 'test.a3seal.High'")
                    && e.contains("test.a3seal.Low")
            }),
            "got {errors:?}"
        );
    }
}
