//! WI-20260822-AK2AJ — `typed_var` IS A MARKER BECAUSE THE CONVERTER MINTED IT, NOT
//! BECAUSE OF ITS NAME.
//!
//! `?x: T` on a rule LHS is lowered to a `typed_var(?x, type: T)` MARKER node
//! (`convert.rs`'s `typed_var_arg` arm, WI-582). `typed_var` is ALSO an ordinary
//! identifier a user may write, and both of the marker's readers recognised it by
//! `local_name(functor) == "typed_var"` alone — WI-948's "a name, not a verdict" trap,
//! which `SimpleTermStore::is_minted` (WI-618) exists to answer instead. The converter
//! did not `mark_minted` the node it built, so there was no provenance to pair with:
//!
//!   * `is_typed_column` (`kb/load.rs`), which `declaration_clause_carrier` asks of a
//!     BODY-LESS head's arguments. MEASURED: `rule pa(typed_var(1))` was refused citing
//!     "A typed column `?x: T` has exactly one enforcer …" — a column the source does
//!     not contain. A FALSE REFUSAL and not merely a misleading sentence: under
//!     proposal 061 that head DECLARES `pa`.
//!   * `convert_term`'s `typed_var` STRIP, the sibling reader, found the same way as
//!     the first (by driving the shape through a rule that HAS a body, where the
//!     declaration path never runs). MEASURED: `rule pc(typed_var(?x, type: 7)) :- qc(?x)`
//!     took the strip, found no `ParseAux::TypeExpr` behind the user's ordinary `type:`
//!     argument, and reported "WI-582: typed rule pattern `?x: T` is missing its type"
//!     — after which the `Bottom` bound it invented tripped the rewrite-shape refusal
//!     too. Two errors, neither about anything in the source.
//!
//! The repair is one new `mark_minted` producer plus the pairing at each reader. Adding
//! a producer is a CENSUSED change — `is_minted` has nine readers and "was this written
//! as a call" is not the same question at each — and the census is recorded at the mint
//! site in `convert.rs`. Its answer: NO EXISTING READER'S VERDICT MOVES. Every one of
//! the nine pairs the mint with a NAME or a POSITION a `typed_var` marker fails —
//! `rule_heads` is `commaSep1($._goal)` while `typed_var_arg` sits only in
//! `_positional_fn_arg`, so the three head/subject readers can never see one, and the
//! other six additionally require `is_equality_family_functor`, `is_arrow_functor`,
//! `binder_form_layout`, or `field_access` | `dot_apply`.
//!
//! # THE THREE BACK-OUTS — one per edit, because the three do not overlap
//!
//! Each was RUN, not predicted; the counts below are what the runs printed.
//!
//! * **THE MINT** — replace `self.terms.mark_minted(tid)` in `convert.rs`'s
//!   `typed_var_arg` arm with nothing, keeping both pairings. NO marker is recognised any
//!   more, so **`a_genuine_typed_column_still_declares_nothing_to_attach_to` and
//!   `a_genuine_typed_column_still_gates_a_rewrite` fail (2 of 5)**: the body-less genuine
//!   column loads clean, and `keep` fires over `Bool` because the bound is never
//!   installed. The two written-`typed_var` tests and the control PASS — a user's call is
//!   un-minted either way. `wi582_typed_rule_pattern_test` drops **4 of 5** in the same
//!   run: it is the standing pin for the genuine annotation, and this back-out is the one
//!   that reaches it.
//! * **THE DECLARATION READER** — `parse_terms.is_minted(tid)` → `true` in
//!   `is_typed_column`. **`a_written_typed_var_argument_declares_its_predicate` fails
//!   (1 of 5)**, on the load, with the WI-903 typed-column refusal. The other four pass.
//! * **THE STRIP** — `self.parsed.terms.is_minted(parse_id)` → `true` in `convert_term`'s
//!   `typed_var` arm. **`a_written_typed_var_in_a_clause_keeps_its_shape` fails (1 of
//!   5)**, again on the load. The other four pass.
//!
//! Backed out by MUTATING each guard rather than deleting the code around it: a deletion
//! back-out measures loadability, not capability. The three do not overlap — no row fails
//! under two of them — which is what says the three edits answer three questions.
//!
//! `wi903_typed_bound_dot_rule_test` is the other standing pin for the genuine
//! annotation. The rows here are this file's own so it does not have to credit a
//! neighbour for the half of its claim that says the marker path still works.

use anthill_core::intern::SymbolKind;
use anthill_core::kb::term::{Literal, Term};
use smallvec::SmallVec;

/// The clauses stored under the symbol `qn` names — `None` when nothing is named `qn`
/// at all. A DECLARED predicate with no clauses is `Some(0)`; an absent one is `None`.
/// (Same shape as `wi_fqc85_rule_declaration_test`'s, which is what 061 asserts with.)
fn clauses(kb: &anthill_core::kb::KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

/// The DECLARATION itself, asked separately from the clause count: 061's body-less head
/// mints a [`SymbolKind::Goal`] in pass 1, and `Some(0)` above would also be true of a
/// symbol some OTHER construct owned. The ticket asks for both questions, so both are
/// asked.
fn declares_a_goal(kb: &anthill_core::kb::KnowledgeBase, qn: &str) -> bool {
    kb.try_resolve_symbol(qn)
        .is_some_and(|sym| kb.has_kind(sym, SymbolKind::Goal))
}

fn errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

/// THE TICKET'S HEADLINE. A body-less head whose argument is a user-written CALL named
/// `typed_var` carries no typed column, so 061's declaration reading applies to it like
/// any other: it brings `pa` into existence and stores no clause.
///
/// The assertions DRIVE the declaration rather than reading the load's `Ok` — `Some(0)`
/// separates a declared-and-empty predicate from an absent one, which "it loads clean"
/// cannot.
#[test]
fn a_written_typed_var_argument_declares_its_predicate() {
    const SRC: &str = "namespace ak2aj.decl\n  rule pa(typed_var(1))\n  \
                       rule uses(?y) :- pa(?y)\nend\n";
    let mut kb = crate::common::load_kb_with(SRC);
    assert!(
        declares_a_goal(&kb, "ak2aj.decl.pa"),
        "the head must DECLARE `pa` — a Goal symbol at this scope"
    );
    assert_eq!(
        clauses(&kb, "ak2aj.decl.pa"),
        Some(0),
        "and the declaration holds no clause"
    );
    assert!(
        crate::common::definite_unary(&mut kb, "ak2aj.decl.uses").is_empty(),
        "a declaration asserts nothing, so its reader decides nothing"
    );
}

/// THE CONTROL FOR THE ROW ABOVE, IN ITS OWN FIXTURE AND ITS OWN LOAD — a plain
/// body-less head, which declares under every one of the three back-outs. It PASSES
/// EITHER WAY BY DESIGN: without it, "`pa` is `Some(0)`" would be equally true of a
/// loader that had stopped declaring body-less heads altogether.
///
/// Sharing a namespace with the arm would make this worthless: the refusal the back-out
/// restores is a LOAD error, and one load error fails the whole file.
#[test]
fn control_a_plain_body_less_head_declares() {
    const SRC: &str = "namespace ak2aj.ctrl\n  rule pf(1)\n  \
                       rule uses(?y) :- pf(?y)\nend\n";
    let mut kb = crate::common::load_kb_with(SRC);
    assert!(declares_a_goal(&kb, "ak2aj.ctrl.pf"), "CONTROL: declared");
    assert_eq!(clauses(&kb, "ak2aj.ctrl.pf"), Some(0), "CONTROL: and no clause");
    assert!(
        crate::common::definite_unary(&mut kb, "ak2aj.ctrl.uses").is_empty(),
        "CONTROL: and asserts nothing"
    );
}

/// THE SIBLING READER, reached through a rule that HAS a body so the declaration path
/// never runs. The claim is stronger than "it loads": the head must keep the `typed_var`
/// APPLICATION the author wrote, so a goal spelling the marker matches it and a goal
/// spelling the bare value 1 does NOT.
///
/// THAT PAIR IS THE MEASUREMENT, and `reaches_bare` is the half that carries it. Under
/// the pre-fix strip the head is rewritten to `pc(?x)` — which matches `pc(1)` — so this
/// row's answer INVERTS: `[9]` where it must be empty. `reaches_marker` is what keeps the
/// emptiness honest; without it, "no answer" would be equally true of a `pc` that had
/// been dropped. (In fact the pre-fix loader never gets that far: the strip finds no
/// `ParseAux::TypeExpr` behind the user's ordinary `type: 7` and errors out. The row
/// fails on the load, and the inverted reading is what it would have been.)
///
/// `rule typed_var(?a, type: ?b)` is fixture scaffolding, not part of the claim: a
/// rule-BODY term must name something declared, and a head may introduce a data name
/// (WI-476) while a body may not. The constant rides in the HEAD (`reaches_marker(9)`,
/// not `, ?m = 9`) because `=` never binds and would SUSPEND — WI-20260822-WZX6B.
#[test]
fn a_written_typed_var_in_a_clause_keeps_its_shape() {
    const SRC: &str = r#"
namespace ak2aj.clause
  rule typed_var(?a, type: ?b)
  rule pc(typed_var(1, type: 7)) :- true
  rule reaches_marker(9) :- pc(typed_var(1, type: 7))
  rule reaches_bare(9) :- pc(1)
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        crate::common::definite_unary(&mut kb, "ak2aj.clause.reaches_marker").len(),
        1,
        "the head kept its `typed_var(...)` argument, so the marker-shaped goal decides"
    );
    assert!(
        crate::common::definite_unary(&mut kb, "ak2aj.clause.reaches_bare").is_empty(),
        "and the BARE goal must not — a stripped head would be `pc(?x)` and answer this one"
    );
}

/// THE OTHER DIRECTION AT THE DECLARATION READER: a GENUINE `?x: Int64` column on a
/// body-less head is still refused, with the same message. The narrowing must be to the
/// marker, not away from the check.
///
/// `wi_fqc85_rule_declaration_test::a_declaration_carries_no_clause_text` carries the
/// same claim as one row of a loop; this is a fixture of its own so a change to that
/// loop cannot silently take this file's guard with it.
#[test]
fn a_genuine_typed_column_still_declares_nothing_to_attach_to() {
    const SRC: &str =
        "namespace ak2aj.column\n  import anthill.prelude.{Int64}\n  rule pe(?x: Int64)\nend\n";
    let errors = errs(SRC);
    assert!(
        errors.iter().any(|e| e.contains(
            "A typed column `?x: T` has exactly one enforcer, a rewrite's typed-pattern bound"
        )),
        "the genuine column keeps the WI-903 refusal, verbatim; got {errors:#?}"
    );
}

/// AND THE GENUINE COLUMN STILL GATES A REWRITE — the enforcement WI-903's message names,
/// driven rather than asserted: `keep(?x: Summable, ?y) <=> ?x [simp]` fires where the
/// matched value's carried type provides `Summable` and suspends where it does not.
///
/// This is the row that says the mint reached the marker path. It is `wi582`'s fixture in
/// this file's namespace, deliberately: the strip is what installs the bound, and the
/// strip is now gated on the very flag this ticket adds.
#[test]
fn a_genuine_typed_column_still_gates_a_rewrite() {
    const SRC: &str = r#"
namespace ak2aj.gate
  import anthill.prelude.{Int64, Bool, Eq}
  import ak2aj.gate.Lib.{keep}

  sort Summable
    sort T = ?
    requires Eq[T]
  end

  fact Summable[T = Int64]

  sort Lib
    sort A = ?
    operation {
      keep(x: A, y: A) -> A
    }
    rule {
      keep_id: keep(?x: Summable, ?y) <=> ?x [simp]
    }
  end
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    let keep = kb
        .try_resolve_symbol("ak2aj.gate.Lib.keep")
        .expect("keep symbol");
    let call = |kb: &mut anthill_core::kb::KnowledgeBase, a: Literal, b: Literal| {
        let a = kb.alloc(Term::Const(a));
        let b = kb.alloc(Term::Const(b));
        kb.alloc(Term::Fn {
            functor: keep,
            pos_args: SmallVec::from_slice(&[a, b]),
            named_args: SmallVec::new(),
        })
    };

    // Int64 provides Summable → the bound holds → the rewrite fires → 5.
    let fires = call(&mut kb, Literal::Int(5), Literal::Int(7));
    let fired = kb.simplify(fires);
    assert_eq!(
        kb.get_term(fired),
        &Term::Const(Literal::Int(5)),
        "the bound is INSTALLED and holds: keep(5, 7) → 5"
    );

    // Bool does not → the redex is left intact. Without the mint the bound is never
    // installed at all and this one fires too, which is the failure that separates
    // "the annotation is read" from "the annotation is enforced".
    let suspends = call(&mut kb, Literal::Bool(true), Literal::Bool(false));
    assert_eq!(
        kb.simplify(suspends),
        suspends,
        "and FAILS over Bool: keep(true, false) is left intact"
    );
}
