//! WI-1000 / proposal 059 R3 — A SECONDARY ENTRY MAY ADD MEMBERS AND SPEC CLAIMS,
//! NEVER IDENTITY. The direct content of every `namespace X … end` written at the
//! address of a sort `X` is classified with DEFAULT-DENY semantics.
//!
//! WHAT A SECONDARY ENTRY IS, and why the same text is two different things: 059's
//! classification is `has_kind(X, Sort)` — an ADDRESS question, not a text one. The
//! very same `namespace Utils { rule p(1) }` is an ordinary namespace whose rule is
//! legal, until someone in another file declares `sort Utils` at that address and it
//! becomes a secondary entry whose rule R3 refuses. That is uncomfortable and 059
//! records it as such; here it is the CONTROL, driven by
//! [`an_ordinary_namespace_keeps_its_content_rules`], which loads byte-identical
//! entry text at an address no sort occupies and expects silence.
//!
//! WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT — measured by deleting the
//! sub-pass 1b block from `scan_definitions` and re-running, not predicted.
//!
//!   * [`a_fresh_bodyless_operation_is_refused`] — FAILS (loads clean). R4 clause 2.
//!   * [`the_operation_rule_reaches_operation_block_sugar`] — FAILS on its refusing
//!     row, the sugar half of the same rule.
//!   * [`every_refused_production_is_refused`] — FAILS in all ten rows. The matrix
//!     reports every row rather than panicking on the first, so "all ten" is a
//!     measurement and not an inference from the row that happened to run.
//!   * [`an_ordinary_namespace_keeps_its_content_rules`] — FAILS on its second half
//!     (the entry expects six refusals and gets none); its first half, the ordinary
//!     namespace, passes either way and is the control.
//!   * [`the_provides_block_interior_is_classified`] — FAILS on both refusing rows;
//!     059's recursion rule.
//!   * [`a_proof_reaches_only_its_own_entry`] / [`a_describe_reaches_only_its_own_entry`]
//!     — FAIL on the foreign-target rows.
//!   * [`a_type_parameter_is_refused_and_the_control_says_why`] — FAILS on the
//!     refusal; its `SortInfo` half is the measurement that motivates it and passes
//!     either way.
//!   * [`a_provides_clause_needs_a_type_at_its_address`] — FAILS. Not R3 itself but
//!     the other half of the grammar change R3 forced (see below).
//!   * [`a_dotted_declaration_name_is_not_the_entrys_content`] — FAILS on its third
//!     row only (the dotted type-parameter binder); its first two rows are the pair
//!     that must stay silent and pass either way.
//!   * [`a_qualified_target_naming_this_entry_is_admitted`] — FAILS on its second row
//!     (the nested sort's member); its first row passes either way.
//!   * [`a_valueless_const_in_an_entry_is_refused`] — FAILS on its first row.
//!
//! PASS EITHER WAY, BY DESIGN — the controls, and what each one is for:
//!
//!   * [`a_fresh_body_having_operation_dispatches`] — the CAPABILITY R3 must not have
//!     taken. If a refusal were too wide this is the row that catches it.
//!   * [`a_bodyless_operation_in_the_main_entry_is_legal`] — the population R4
//!     clause 2 must NOT reach. The host carriers declare body-less operations
//!     deliberately and back them from `operation_map`; the row drives one of them
//!     out of the real stdlib, so it is not a hypothetical.
//!   * [`a_duplicate_declaration_is_refused_by_wi1049`] — freshness has ONE owner.
//!     R3 deliberately does not re-derive it, and this pins that the other rule still
//!     fires (with its own message) rather than being shadowed by this one.
//!   * [`every_allowed_production_loads`] — the other side of default-deny: a list
//!     that refuses everything would pass every refusal row.
//!   * [`a_claim_about_another_carrier_is_written_one_level_out`] — the fact ban's
//!     blast radius, measured rather than argued.
//!
//! THE GRAMMAR HAD TO CHANGE, and it is part of this ticket rather than a detour.
//! R3 allows a spec claim written `provides Spec[X]` in a secondary entry and refuses
//! the `fact Spec[X]` spelling there (a `fact` cannot be told from an ordinary fact
//! over a parameterized data sort; `provides` is a declaration the grammar
//! recognises). But `provides_clause` was admitted only in `_sort_content`, so the
//! ALLOWED spelling was unwritable in the one place 059 calls the point of the
//! mechanism — and refusing the `fact` one would have removed a capability WI-978 and
//! WI-1008 delivered. `_namespace_content` now admits it, and because the grammar
//! cannot tell a secondary entry from an ordinary namespace, the loader classifies:
//! written where no sort occupies the address it is refused, naming the namespace.
//!
//! WHAT IS RETIRED IS ONE SENSE OF `fact`, NOT THE SPELLING. The two are not
//! interchangeable: `provides` takes its carrier from the enclosing scope and `fact`
//! from the bindings, so only `fact Spec[Carrier]` can say that some OTHER sort
//! satisfies a spec. They coincide exactly when the carrier is the entry's own sort,
//! and that coincidence is all the refusal removes — the orphan claim is written one
//! block outward, where nothing is refused, and
//! [`a_claim_about_another_carrier_is_written_one_level_out`] drives it.

use anthill_core::eval::{self, Interpreter, Value};

/// One spec with one operation, shared by every fixture that needs dispatch.
const SPEC: &str = r#"
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
"#;

/// The GENERIC caller. It knows nothing of `Rec` and reaches the carrier's `show`
/// through the requirement dictionary its `requires` builds — so a row that answers
/// here has driven the secondary entry's member through DISPATCH, not merely resolved
/// its name.
const CALLER: &str = r#"
  sort Caller
    sort T = ?
    requires Show[T = T]
    operation useIt(x: T) -> Int64 = show(x)
  end
"#;

/// Distinct from any default, so a wrong dispatch cannot coincide with a right one.
const ANSWER: i64 = 111;

/// ONE PROGRAM SKELETON, so a row differs from the control in exactly what it passes
/// in. `entry` is the secondary entry's body; everything else is fixed.
///
/// WI-1102 — THE PROVISION IS PART OF THE SKELETON NOW, and that is content rather than
/// plumbing. `driveGeneric` calls `Caller.useIt(rec(n: 7))`, which pins `Show[T = Rec]`,
/// and a call whose pinned carrier provides NOTHING is refused at LOAD (058 §3.10). Every
/// test in this file that DRIVES the value already wrote the line for exactly that
/// reason; the rows that only assert the load had not needed to, and without it each
/// would now be measuring that refusal instead of its own production. Appended only when
/// absent, so a row whose SUBJECT is the `provides` clause keeps its own single copy.
fn fixture(ns: &str, entry: &str) -> String {
    let entry = if entry.contains("provides Show[T = Rec]") {
        entry.to_string()
    } else {
        format!("{entry}\n    provides Show[T = Rec]")
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
{SPEC}
  sort Rec
    entity rec(n: Int64)
  end
  namespace Rec
{entry}
  end
{CALLER}
  operation driveGeneric() -> Int64 = Caller.useIt(rec(n: 7))
end
"#
    )
}

/// The load errors of `src`, or an empty vec when it loads clean.
fn errors_of(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

/// The R3 refusals only — so a row can say "R3 was silent here" without asserting
/// that nothing else in the program had anything to say.
fn r3_errors(src: &str) -> Vec<String> {
    errors_of(src)
        .into_iter()
        .filter(|e| e.contains("is not allowed in a secondary entry"))
        .collect()
}

fn eval_int(src: &str, op: &str) -> Result<i64, String> {
    let kb = crate::common::try_load_kb_with(src)
        .unwrap_or_else(|errs| panic!("fixture must load clean; got {errs:#?}"));
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("register eval builtins");
    match interp.call(op, &[]) {
        Ok(Value::Int(n)) => Ok(n),
        Ok(other) => Err(format!("expected Int, got {}", other.type_name())),
        Err(e) => Err(format!("{e}")),
    }
}

// ── The capability, and the rule that bounds it ─────────────────────────────

/// THE CAPABILITY. A fresh, body-having operation declared in a secondary entry,
/// plus the sort's spec claim written `provides` beside it — R3's two allowed
/// members together — reached by a generic caller through the requirement
/// dictionary. Drives the value, because "it loads clean" is what the whole defect
/// class this file guards looks like.
#[test]
fn a_fresh_body_having_operation_dispatches() {
    let src = fixture(
        "test.wi1000.ok",
        &format!("    operation show(x: Rec) -> Int64 = {ANSWER}\n    provides Show[T = Rec]"),
    );
    assert_eq!(eval_int(&src, "test.wi1000.ok.driveGeneric"), Ok(ANSWER));
}

/// R4 clause 2 — the operation rule. A body-less declaration reserves an
/// implementation slot for a later builtin or host `operation_map`; a secondary entry
/// adds a COMPLETE new member instead, so the same declaration without `= 111` is
/// refused, naming the sort and the declaration.
#[test]
fn a_fresh_bodyless_operation_is_refused() {
    let src = fixture("test.wi1000.nobody", "    operation show(x: Rec) -> Int64");
    let errs = r3_errors(&src);
    assert_eq!(
        errs.len(),
        1,
        "expected exactly one R3 refusal, got {errs:#?}"
    );
    assert!(
        errs[0].contains("`operation` 'show'") && errs[0].contains("'test.wi1000.nobody.Rec'"),
        "the diagnostic must name the declaration AND the sort whose entry this is; got {:?}",
        errs[0]
    );
    assert!(
        errs[0].contains("runnable Anthill body"),
        "and say what is missing; got {:?}",
        errs[0]
    );
}

/// THE SUGAR. An `operation { … }` block is sugar for its entries and follows them —
/// both halves, so the row is a pair rather than a single refusal: the block form
/// with a body dispatches, and the same block without one is refused identically.
#[test]
fn the_operation_rule_reaches_operation_block_sugar() {
    let bodied = fixture(
        "test.wi1000.sugarok",
        &format!(
            "    operation {{\n      show(x: Rec) -> Int64 = {ANSWER}\n    }}\n    \
             provides Show[T = Rec]"
        ),
    );
    assert_eq!(
        eval_int(&bodied, "test.wi1000.sugarok.driveGeneric"),
        Ok(ANSWER),
        "the block form of an allowed operation must dispatch exactly as the long form does",
    );

    let bare = fixture(
        "test.wi1000.sugarbad",
        "    operation {\n      show(x: Rec) -> Int64\n    }",
    );
    let errs = r3_errors(&bare);
    assert_eq!(
        errs.len(),
        1,
        "expected exactly one R3 refusal, got {errs:#?}"
    );
    assert!(
        errs[0].contains("`operation` 'show'") && errs[0].contains("runnable Anthill body"),
        "the sugar must reach the SAME rule with the same words; got {:?}",
        errs[0]
    );
}

// ── The controls ────────────────────────────────────────────────────────────

/// THE POPULATION R4 CLAUSE 2 MUST NOT REACH. A body-less operation in a MAIN entry
/// is the one declaration of an interface and may be backed by a builtin or by an
/// `operation_map` in another file — the host carriers do exactly this. Two rows: a
/// fixture, and a real stdlib member driven to a value, so the claim is about the
/// corpus and not about a shape invented here.
#[test]
fn a_bodyless_operation_in_the_main_entry_is_legal() {
    let src = r#"
namespace test.wi1000.mainentry
  import anthill.prelude.{Int64}
  sort Rec
    entity rec(n: Int64)
    operation show(x: Rec) -> Int64
  end
end
"#;
    assert!(
        r3_errors(src).is_empty(),
        "R3 governs a secondary entry's content, never a sort body's: {:?}",
        r3_errors(src)
    );

    // `anthill.prelude.String.isEmpty` is declared body-less in its sort body and
    // realized by `operation_map` in `anthill-stl`. If the rule had reached main
    // entries the whole stdlib would stop loading; this drives one such member to a
    // value so the row fails loudly rather than by absence.
    let drive = r#"
namespace test.wi1000.host
  import anthill.prelude.{Int64, String}
  operation driveHost() -> Int64 = if "".isEmpty() then 1 else 0
end
"#;
    assert_eq!(eval_int(drive, "test.wi1000.host.driveHost"), Ok(1));
}

/// FRESHNESS HAS ONE OWNER. R3 deliberately does not re-derive "is this name already
/// declared" — WI-1049 answers it as a whole-KB pass over `OperationInfo` records,
/// and it already crosses the main/secondary boundary because one written name is one
/// symbol. Two implementations of one rule could disagree; this pins that the other
/// one still fires, and with ITS message.
#[test]
fn a_duplicate_declaration_is_refused_by_wi1049() {
    let src = r#"
namespace test.wi1000.dup
  import anthill.prelude.{Int64}
  sort Rec
    entity rec(n: Int64)
    operation show(x: Rec) -> Int64 = 1
  end
  namespace Rec
    operation show(x: Rec) -> Int64 = 2
  end
end
"#;
    let errs = errors_of(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("is declared more than once in its scope")),
        "WI-1049's rule must be the one that fires; got {errs:#?}"
    );
    assert!(
        r3_errors(src).is_empty(),
        "…and R3 must not also refuse it: both declarations have bodies, so R3 has \
         nothing to say. Got {:?}",
        r3_errors(src)
    );
}

/// THE ADDRESS IS THE CLASSIFIER — the control that makes every refusal above
/// attributable to 059's rule rather than to the constructs themselves. The two
/// namespaces below have BYTE-IDENTICAL bodies; one sits at the address of a sort and
/// one does not, and only the first is a secondary entry. Nothing in R3 reaches an
/// ordinary namespace.
#[test]
fn an_ordinary_namespace_keeps_its_content_rules() {
    // Everything R3 refuses in an entry, all of it long-standing legal namespace
    // content. `Utils` has no sort at its address.
    let body = r#"
    entity Thing(n: Int64)
    sort Param = ?
    rule p(1)
    fact q(2)
    constraint no_three :- p(3)
    describe p {< a rule someone else could own >}
"#;
    let plain = format!(
        r#"
namespace test.wi1000.plain
  import anthill.prelude.{{Int64}}
  namespace Utils
{body}
  end
end
"#
    );
    assert!(
        errors_of(&plain).is_empty(),
        "an ordinary namespace's content rules are unchanged; got {:?}",
        errors_of(&plain)
    );

    // The SAME text, at an address a sort occupies. Only the sort's presence differs.
    let entry = format!(
        r#"
namespace test.wi1000.entry
  import anthill.prelude.{{Int64}}
  sort Utils
    entity util(n: Int64)
  end
  namespace Utils
{body}
  end
end
"#
    );
    // Six refusals, one per declaration. The `describe p` row counts because an
    // UNLABELED rule contributes no citation handle to the entry's declared-name set —
    // it is not a thing a proof or a description can name either — so its target reads
    // as foreign. See [`a_describe_reaches_only_its_own_entry`]'s last row for the
    // case where the target IS recorded despite being refused itself.
    assert_eq!(
        r3_errors(&entry).len(),
        6,
        "the identical text at a sort's address is a secondary entry, and each of its \
         six declarations is refused; got {:#?}",
        r3_errors(&entry)
    );
}

// ── The two lists ───────────────────────────────────────────────────────────

/// EVERY REFUSED PRODUCTION, one row each, every row reported. A matrix rather than
/// nine tests so that backing the change out names all nine rather than the first.
#[test]
fn every_refused_production_is_refused() {
    let rows: &[(&str, &str, &str)] = &[
        // (label, entry body, a fragment the diagnostic must carry)
        ("entity", "    entity Extra(n: Int64)", "`entity` 'Extra'"),
        ("type param `= ?`", "    sort P = ?", "`sort` 'P'"),
        ("type param `?T`", "    sort ?P", "`sort` 'P'"),
        ("type param `[T]`", "    sort [P]", "`sort` 'P'"),
        ("braced binder", "    sort [F] { sort [T] }", "`sort` 'F'"),
        (
            "sort-level requires",
            "    requires Show[T = Rec]",
            "`requires`",
        ),
        ("rule", "    rule freshp(1)", "`rule`"),
        ("rule block", "    rule {\n      freshp(1)\n    }", "`rule`"),
        ("fact", "    fact freshq(2)", "`fact`"),
        (
            "constraint",
            "    constraint no_three :- Rec.show(rec(n: 3))",
            "`constraint`",
        ),
    ];
    let mut bad = Vec::new();
    for (i, (label, body, want)) in rows.iter().enumerate() {
        let src = fixture(
            &format!("test.wi1000.r{i}"),
            &format!("    operation show(x: Rec) -> Int64 = {ANSWER}\n{body}"),
        );
        let errs = r3_errors(&src);
        match errs.iter().find(|e| e.contains(want)) {
            Some(e) if e.contains(&format!("test.wi1000.r{i}.Rec")) => {}
            Some(e) => bad.push(format!(
                "{label}: refused, but the message names no sort: {e}"
            )),
            None => bad.push(format!(
                "{label}: expected an R3 refusal carrying {want:?}, got {errs:#?}"
            )),
        }
    }
    assert!(
        bad.is_empty(),
        "rows not refused as R3 requires:\n  {}",
        bad.join("\n  ")
    );
}

/// THE OTHER SIDE OF DEFAULT-DENY. A classifier that refused everything would pass
/// every row above, so the allowed list needs driving too: each row is R3's allowed
/// content, and each must load with R3 silent.
///
/// Two of these are WI-1000's own calls on productions 059 left unclassified. A
/// BODYLESS TYPE ALIAS is allowed for the same reason a nested `sort … end` is: it
/// declares a NEW TYPE at its own address (`X.Code`), so it is that type's main entry
/// rather than a statement about `X` — and it works, which the `usesTheAlias` row
/// drives rather than asserts. A nested NAMESPACE is allowed and not recursed into,
/// being an ordinary namespace at `X.Inner`.
#[test]
fn every_allowed_production_loads() {
    let rows: &[(&str, &str)] = &[
        ("const", "    const LIMIT: Int64 = 5"),
        (
            "nested sort with a body",
            "    sort Code\n      entity code(v: Int64)\n    end",
        ),
        ("bodyless type alias", "    sort Code = Int64"),
        (
            "the alias USED by a sibling member",
            "    sort Code = Int64\n    operation widen(x: Rec) -> Code = 5",
        ),
        (
            "nested namespace",
            "    namespace Inner\n      rule inner_p(1)\n    end",
        ),
        ("provides clause", "    provides Show[T = Rec]"),
        (
            "host provides block",
            "    provides Rec language rust\n      artifact \"nowhere.rs\"\n      \
             carrier { Rec: \"Rec\" }\n    end",
        ),
        (
            "inline description block",
            "    {< a description block is inert >}\n    const C: Int64 = 1",
        ),
    ];
    let mut bad = Vec::new();
    for (i, (label, body)) in rows.iter().enumerate() {
        let src = fixture(
            &format!("test.wi1000.a{i}"),
            &format!("    operation show(x: Rec) -> Int64 = {ANSWER}\n{body}"),
        );
        let errs = errors_of(&src);
        if !errs.is_empty() {
            bad.push(format!("{label}: must load clean, got {errs:#?}"));
        }
    }
    assert!(
        bad.is_empty(),
        "allowed rows that did not load:\n  {}",
        bad.join("\n  ")
    );
}

/// 059's RECURSION RULE. A `provides … language L … end` block is a REALIZATION, not
/// a second place to define predicates, so its interior is governed by the same two
/// lists: the realization clauses pass, a rule and a fact written inside it are
/// refused exactly as they would be one level out.
///
/// The `fact` row is the one place these lists cost something rather than nothing: a
/// block carries its lawfulness claims as `fact Spec[T = Carrier]`, and `ProvidesItem`
/// admits no `provides` spelling — so inside a secondary entry those claims move out
/// of the block and are written `provides Spec[…]` as the entry's direct content,
/// which the last row drives.
#[test]
fn the_provides_block_interior_is_classified() {
    let block = |inner: &str| {
        fixture(
            "test.wi1000.pb",
            &format!(
                "    operation show(x: Rec) -> Int64 = {ANSWER}\n    \
                 provides Rec language rust\n      artifact \"nowhere.rs\"\n      \
                 carrier {{ Rec: \"Rec\" }}\n{inner}    end"
            ),
        )
    };
    assert!(
        errors_of(&block("")).is_empty(),
        "the realization clauses are the block's whole legal content: {:?}",
        errors_of(&block(""))
    );
    for (label, inner, want) in [
        ("a rule", "      rule freshp(1)\n", "`rule`"),
        ("a fact", "      fact Show[T = Rec]\n", "`fact`"),
    ] {
        let errs = r3_errors(&block(inner));
        assert!(
            errs.iter()
                .any(|e| e.contains(want) && e.contains("test.wi1000.pb.Rec")),
            "{label} inside the block must be refused as it would be one level out; got {errs:#?}"
        );
    }
    // The migration the `fact` refusal prescribes, driven: the claim moves out of the
    // block and is spelled `provides`, and the carrier still dispatches.
    let migrated = fixture(
        "test.wi1000.pbok",
        &format!(
            "    operation show(x: Rec) -> Int64 = {ANSWER}\n    provides Show[T = Rec]\n    \
             provides Rec language rust\n      artifact \"nowhere.rs\"\n      \
             carrier {{ Rec: \"Rec\" }}\n    end"
        ),
    );
    assert_eq!(
        eval_int(&migrated, "test.wi1000.pbok.driveGeneric"),
        Ok(ANSWER)
    );
}

/// THE ORPHAN CLAIM — the capability the fact ban must NOT have taken, and the reason
/// the ban is narrow rather than a retirement of the `fact` spelling.
///
/// The two spellings differ ONLY WHERE THE SCOPE NAMES NO TYPE — WI-1069 measured it
/// and corrected what this comment used to say. `provides Show[T = Other]` in a
/// namespace with a sort at its address records `(Rec, Show-for-Other)`: provider from
/// the scope, carrier from the binding, i.e. a witness. So does `fact Show[T = Other]`
/// written in that same body. At an address NO type occupies the `provides` clause has
/// no provider to be about and is refused, while `fact Show[T = Other]` still derives
/// its carrier from the bindings — which is why the one-level-out `fact` spelling must
/// stay writable, and it is the only thing that must.
///
/// It does. R3 reaches a `namespace X` block's DIRECT content and nothing else, so a
/// claim about a foreign carrier — which is not a claim about `X` at all — is written
/// one level out exactly as the corpus already writes it. This drives that: the entry
/// supplies `Rec`'s member, the enclosing namespace claims for `Other`, and the
/// provision is recorded under `Other`.
///
/// Passes either way by design. It is here because the fact ban's blast radius is the
/// question this row answers, and an argument is not a measurement.
#[test]
fn a_claim_about_another_carrier_is_written_one_level_out() {
    let src = r#"
namespace test.wi1000.orphanclaim
  import anthill.prelude.{Int64}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort Rec
    entity rec(n: Int64)
  end
  sort Other
    entity other(n: Int64)
    operation show(x: Other) -> Int64 = 5
  end
  namespace Rec
    operation show(x: Rec) -> Int64 = 7
  end
  fact Show[T = Other]
end
"#;
    let kb = crate::common::load_kb_with(src);
    // WI-1098: outside the equality family, because `Rec` and `Other` are composites
    // and every composite now derives `PartialEq`+`Eq` — rows about structural
    // equality, not about where a `fact Show[…]` filed.
    let carriers: Vec<String> = crate::common::sort_provisions_outside_equality(&kb)
        .into_iter()
        .filter(|(c, _)| c.starts_with("test.wi1000.orphanclaim."))
        .map(|(c, _)| c)
        .collect();
    assert_eq!(
        carriers,
        vec!["test.wi1000.orphanclaim.Other".to_string()],
        "a `fact Spec[Carrier]` one level out still files under the CARRIER its \
         bindings name — the orphan-instance route R3 must not have taken",
    );
}

// ── The two target-bearing productions ──────────────────────────────────────

/// A PROOF REACHES ONLY ITS OWN ENTRY. Verification calls `set_proof_result`, writing
/// the verdict BACK onto the target declaration, so a proof mutates the state of
/// something the entry may not own. Three rows, differing only in where the target is
/// declared:
///
///   * target in the SAME block — admitted;
///   * target in a SECOND `namespace Rec` block IN THE SAME FILE — admitted, because
///     059 individuates an entry as one file's text at one address: two blocks in one
///     file are ONE entry, one author writing two paragraphs;
///   * target in the MAIN entry — refused. The main entry is another entry.
///
/// Asserted on the R3 verdict rather than on a clean load: whether the prover then
/// discharges the proof is another subsystem's business, and a row that demanded a
/// clean load would be measuring that instead of this.
#[test]
fn a_proof_reaches_only_its_own_entry() {
    let same_block = fixture(
        "test.wi1000.psame",
        &format!("    operation show(x: Rec) -> Int64 = {ANSWER}\n    proof show end"),
    );
    assert!(
        r3_errors(&same_block).is_empty(),
        "a proof about a declaration of this same entry is admitted: {:?}",
        r3_errors(&same_block)
    );

    let second_block = format!(
        r#"
namespace test.wi1000.p2
  import anthill.prelude.{{Int64}}
  sort Rec
    entity rec(n: Int64)
  end
  namespace Rec
    proof show end
  end
  namespace Rec
    operation show(x: Rec) -> Int64 = {ANSWER}
  end
end
"#
    );
    assert!(
        r3_errors(&second_block).is_empty(),
        "two blocks at one address IN ONE FILE are ONE entry, so the proof's target is \
         its own entry's: {:?}",
        r3_errors(&second_block)
    );

    let foreign = format!(
        r#"
namespace test.wi1000.pforeign
  import anthill.prelude.{{Int64}}
  sort Rec
    entity rec(n: Int64)
    operation other(x: Rec) -> Int64 = 1
  end
  namespace Rec
    operation show(x: Rec) -> Int64 = {ANSWER}
    proof other end
  end
end
"#
    );
    let errs = r3_errors(&foreign);
    assert!(
        errs.iter()
            .any(|e| e.contains("`proof` 'other'") && e.contains("set_proof_result")),
        "a proof whose target the MAIN entry declares is refused, naming the target and \
         saying what a proof writes; got {errs:#?}"
    );

    // THE FILE IS THE UNIT, and this is the row that makes that load-bearing rather
    // than decorative. The same two blocks as `second_block` above — one holding the
    // proof, one the operation — split across two FILES are TWO entries, and the proof
    // is refused. Byte-identical text, one difference: where the file boundary falls.
    let file_a = r#"
namespace test.wi1000.pcross
  import anthill.prelude.{Int64}
  sort Rec
    entity rec(n: Int64)
  end
  namespace Rec
    proof show end
  end
end
"#;
    let file_b = format!(
        r#"
namespace test.wi1000.pcross
  import anthill.prelude.{{Int64}}
  namespace Rec
    operation show(x: Rec) -> Int64 = {ANSWER}
  end
end
"#
    );
    let errs: Vec<String> = crate::common::try_load_kb_with_files(&[file_a, &file_b])
        .err()
        .unwrap_or_default()
        .into_iter()
        .filter(|e| e.contains("is not allowed in a secondary entry"))
        .collect();
    assert!(
        errs.iter().any(|e| e.contains("`proof` 'show'")),
        "the same text in TWO files is two entries, so the proof's target is another \
         entry's and is refused; got {errs:#?}"
    );
}

/// A `describe` REACHES ONLY ITS OWN ENTRY — the same condition as a proof, and 059's
/// own second objection to it: it names a TARGET, so it writes about a declaration
/// another entry may own.
///
/// WHY NOT REFUSED OUTRIGHT, though the fact ban would reach it (it asserts
/// `DescriptionInfo`): that objection does not single `describe` out, because the
/// inline `{< … >}` block R3 calls "inert and always allowed" asserts the very same
/// predicate from a nested sort or an alias in the same entry.
///
/// A SECOND reason once stood here and is now FALSE: that refusing `describe` would
/// cost a real capability, because an operation's own inline block emitted no
/// `DescriptionInfo` at all and `describe` was therefore the only way to document a
/// member. WI-1070 closed that drop — an `operation`'s and a `const`'s own block now
/// emits like a sort's, in both operation spellings — so `describe` is no longer the
/// only route. The verdict below is UNCHANGED, and surviving the loss of that reason
/// is the test of it: it keys on the TARGET, not on the absence of an alternative.
#[test]
fn a_describe_reaches_only_its_own_entry() {
    let own = fixture(
        "test.wi1000.dsame",
        &format!(
            "    operation show(x: Rec) -> Int64 = {ANSWER}\n    \
             describe show {{< documents this entry's own member >}}"
        ),
    );
    assert!(
        r3_errors(&own).is_empty(),
        "a description of this entry's own member is admitted: {:?}",
        r3_errors(&own)
    );

    let foreign = format!(
        r#"
namespace test.wi1000.dforeign
  import anthill.prelude.{{Int64}}
  sort Rec
    entity rec(n: Int64)
    operation other(x: Rec) -> Int64 = 1
  end
  namespace Rec
    operation show(x: Rec) -> Int64 = {ANSWER}
    describe other {{< written about someone else's declaration >}}
  end
end
"#
    );
    let errs = r3_errors(&foreign);
    assert!(
        errs.iter().any(|e| e.contains("`describe` 'other'")),
        "a `describe` about the main entry's declaration is refused, naming the target; \
         got {errs:#?}"
    );

    // WRITTEN HERE, NOT LEGAL HERE — the target set's question. An `entity` in an
    // entry is refused, but it IS this entry's declaration, so a `describe` about it
    // must not raise a SECOND error blaming a foreign target: one root cause, one
    // diagnostic, and the one that names the real problem.
    let refused_target = fixture(
        "test.wi1000.dwritten",
        &format!(
            "    operation show(x: Rec) -> Int64 = {ANSWER}\n    entity Extra(n: Int64)\n    \
             describe Extra {{< about a declaration this entry does make >}}"
        ),
    );
    let errs = r3_errors(&refused_target);
    assert_eq!(
        errs.len(),
        1,
        "exactly the entity's own refusal, and nothing about the `describe`; got {errs:#?}"
    );
    assert!(
        errs[0].contains("`entity` 'Extra'"),
        "and it is the entity's; got {:?}",
        errs[0]
    );
}

// ── The address a declaration's NAME lands at ───────────────────────────────

/// A DOTTED DECLARATION NAME DECLARES AT ANOTHER ADDRESS, so R3 does not reach it.
/// `operation Inner.helper` written in a secondary entry to `Rec` declares
/// `Rec.Inner.helper` — a member of the ordinary namespace `Rec.Inner`, and 059 says
/// "nothing in R3 or R4 reaches" one.
///
/// THE EXPERIMENT IS THE PAIR, because either row alone proves nothing: the dotted
/// spelling and the nested-`namespace` spelling are the SAME declaration, so a rule
/// that classified one and not the other would give one declaration two verdicts.
/// Driven on the shape that discriminates — a BODY-LESS operation, which R3 refuses
/// at the entry's own address and must not refuse at `Rec.Inner`'s.
///
/// ONE EXCEPTION, and it is measured rather than reasoned: a dotted `sort <p>.T = ?`
/// still registers `T` as a type PARAMETER of the ENCLOSING sort — `DefinePass` calls
/// `add_type_param` with the scope the declaration is WRITTEN in, not the one its name
/// lands in, so `type_params_of_sort(Rec)` reads `["T"]` for the main-entry spelling
/// while the symbol sits at `Rec.Inner.T`. It touches identity wherever its symbol
/// goes, so the last row pins that it stays refused.
#[test]
fn a_dotted_declaration_name_is_not_the_entrys_content() {
    let dotted = fixture(
        "test.wi1000.dot",
        "    operation Inner.helper(x: Rec) -> Int64",
    );
    assert!(
        r3_errors(&dotted).is_empty(),
        "a dotted name declares into `Rec.Inner`, an ordinary namespace R3 does not \
         reach; got {:?}",
        r3_errors(&dotted)
    );

    let nested = fixture(
        "test.wi1000.nest",
        "    namespace Inner\n      operation helper(x: Rec) -> Int64\n    end",
    );
    assert!(
        r3_errors(&nested).is_empty(),
        "the CONTROL — the same declaration, nested-namespace spelling. The pair is \
         the point: one declaration, one verdict; got {:?}",
        r3_errors(&nested)
    );

    // And the shape that shows the rule is not "skip anything dotted".
    let dotted_param = fixture("test.wi1000.dotp", "    sort Inner.T = ?");
    assert!(
        r3_errors(&dotted_param)
            .iter()
            .any(|e| e.contains("`sort` 'Inner.T'")),
        "a dotted type-parameter binder still binds THIS sort, so it stays refused; \
         got {:?}",
        r3_errors(&dotted_param)
    );
}

/// A QUALIFIED TARGET NAMING THIS ENTRY'S OWN DECLARATION IS ADMITTED. `describe Rec.g`
/// inside `namespace Rec` is a qualified self-reference and means what `describe g`
/// means; the first cut of the target check tested `!contains('.')` and refused every
/// qualified spelling, asserting a condition that in fact held.
///
/// THE SECOND ROW IS WHY THE FIX IS NOT "ALLOW ANY DOTTED TARGET": a NESTED SORT's
/// member stays foreign. 059 makes a nested `sort … end` the MAIN ENTRY OF ITS OWN
/// TYPE, so `Code.widen` belongs to that entry and not to this one, even though the
/// same author wrote both in the same block.
#[test]
fn a_qualified_target_naming_this_entry_is_admitted() {
    let own = fixture(
        "test.wi1000.qself",
        &format!(
            "    operation show(x: Rec) -> Int64 = {ANSWER}\n    \
             describe Rec.show {{< the entry's own member, named qualified >}}"
        ),
    );
    assert!(
        r3_errors(&own).is_empty(),
        "a qualified self-reference is the entry's own declaration; got {:?}",
        r3_errors(&own)
    );

    let nested_member = fixture(
        "test.wi1000.qnest",
        &format!(
            "    operation show(x: Rec) -> Int64 = {ANSWER}\n    \
             sort Code\n      entity code(v: Int64)\n      \
             operation widen(c: Code) -> Int64 = 1\n    end\n    \
             describe Code.widen {{< about a NESTED SORT's member >}}"
        ),
    );
    assert!(
        r3_errors(&nested_member)
            .iter()
            .any(|e| e.contains("`describe` 'Code.widen'")),
        "a nested sort is its own type's MAIN entry, so its member is another entry's; \
         got {:?}",
        r3_errors(&nested_member)
    );
}

/// R4 CLAUSE 2 REACHES A `const` TOO. A value-less `const` reserves a HOST-FACING slot
/// exactly as a body-less operation does — `const_map` is the const-level peer of
/// `operation_map` (§10.2 / WI-889) — and reserving a slot on a type one is extending
/// is a main entry's to do. 059's allowed list says only "consts", written before that
/// peer was weighed.
///
/// The pair is the measurement: a const WITH a value is admitted (it is also a row of
/// [`every_allowed_production_loads`]), and only the value-less one is refused.
#[test]
fn a_valueless_const_in_an_entry_is_refused() {
    let bare = fixture("test.wi1000.cbare", "    const LIMIT: Int64");
    let errs = r3_errors(&bare);
    assert!(
        errs.iter()
            .any(|e| e.contains("`const` 'LIMIT'") && e.contains("const_map")),
        "a value-less const is refused, naming the declaration and the host channel it \
         would be reserving; got {errs:#?}"
    );

    let valued = fixture("test.wi1000.cval", "    const LIMIT: Int64 = 5");
    assert!(
        r3_errors(&valued).is_empty(),
        "…and a const with a value is a complete new member; got {:?}",
        r3_errors(&valued)
    );

    // The population the clause must NOT reach, same as for an operation: a MAIN
    // entry's value-less const is the one declaration of a host-supplied value, which
    // is exactly what `const_map` exists to back (`Float.infinity` / `nan`).
    let main_entry = r#"
namespace test.wi1000.cmain
  import anthill.prelude.{Int64}
  sort Rec
    entity rec(n: Int64)
    const LIMIT: Int64
  end
end
"#;
    assert!(
        r3_errors(main_entry).is_empty(),
        "R3 governs a secondary entry's content, never a sort body's; got {:?}",
        r3_errors(main_entry)
    );
}

// ── The type-parameter refusal, and the measurement behind it ───────────────

/// A TYPE PARAMETER IS THE TYPE'S IDENTITY, so R3 refuses it — and the second half of
/// this test is the measured harm rather than the principle. Written in the MAIN
/// entry, `sort T = ?` reaches `SortInfo(name: Rec).parameters` as `[T]`. Written in
/// a secondary entry it reached `SymbolTable::add_type_param` all the same (the
/// entry's scope IS the sort's scope) while `SortInfo.parameters` stayed EMPTY: the
/// declaration half-registered, in exactly the field R3 says must never be written
/// from an entry. That is WI-1008's split again, and it is why the refusal is the
/// answer rather than completing the record.
///
/// The `SortInfo` row passes either way by design — it is the control that says the
/// main-entry spelling still records what the entry spelling could not.
#[test]
fn a_type_parameter_is_refused_and_the_control_says_why() {
    let entry = fixture("test.wi1000.tp", "    sort T = ?");
    let errs = r3_errors(&entry);
    assert!(
        errs.iter()
            .any(|e| e.contains("`sort` 'T'") && e.contains("identity")),
        "a type parameter in a secondary entry is refused; got {errs:#?}"
    );

    let main_entry = r#"
namespace test.wi1000.tpmain
  import anthill.prelude.{Int64}
  sort Rec
    sort T = ?
    entity rec(n: Int64)
  end
end
"#;
    let kb = crate::common::load_kb_with(main_entry);
    let rec = kb
        .try_resolve_symbol("test.wi1000.tpmain.Rec")
        .expect("Rec");
    assert_eq!(
        kb.type_params_of_sort(rec),
        vec!["T".to_string()],
        "the main-entry spelling records the parameter — which is the thing the entry \
         spelling could not do, and the reason it is refused rather than completed",
    );
}

// ── The grammar change's other half ─────────────────────────────────────────

/// A `provides` CLAUSE NEEDS A TYPE AT ITS ADDRESS. The clause names its subject by
/// WHERE it stands, so admitting the production in a namespace body — which R3's
/// allowed spelling required — puts it within reach of an address no sort occupies,
/// where it would file a provision under the namespace itself. The loader classifies
/// what the grammar cannot: refused there, and named.
///
/// The control is the row above it: the SAME clause at a sort's address loads and
/// dispatches ([`a_fresh_body_having_operation_dispatches`]).
#[test]
fn a_provides_clause_needs_a_type_at_its_address() {
    let src = r#"
namespace test.wi1000.orphan
  import anthill.prelude.{Int64}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort Rec
    entity rec(n: Int64)
    operation show(x: Rec) -> Int64 = 111
  end
  namespace Utils
    provides Show[T = Rec]
  end
end
"#;
    let errs = errors_of(src);
    assert!(
        errs.iter().any(|e| {
            e.contains("a `provides` clause needs a type at its address")
                && e.contains("test.wi1000.orphan.Utils")
        }),
        "a `provides` in a namespace naming no type is refused, naming the namespace; \
         got {errs:#?}"
    );
}
