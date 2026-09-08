## Attributes

- id: WI-20260821-SBZ2A-scaland-s-rule-head-binding
- created: 2026-08-21T20:23:24Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-08T10:55:19Z

- acceptance: cargo-test, scaland-sbt-test

## Description

SCALAND'S RULE-HEAD BINDING STILL DEPENDS ON DECLARATION ORDER — port WI-980. The
divergence is marked at the site (`Loader.scala`, pass 3) but had no owner, which is what
this ticket is.

MEASURED SHAPE (the rustland defect, verbatim, and scaland still has it):
  namespace demo { rule p(1); sort Rec { entity r(n: Int64); rule p(2) } }
  -> ONE predicate with two clauses.
  Move `rule p(1)` BELOW the sort -> TWO predicates, `demo.p` and `demo.Rec.p`, one clause
  each. Both load clean, and the split silently decides whether a rule EXTENDS someone
  else's predicate, which is non-monotone.

MECHANISM, identical in both implementations before the fix: `scanRuleGoal`'s guard asks
whether the name ALREADY DENOTES, and pass 3 mints as it walks, so the table it reads is
the one it is filling. This is the one pass whose own work changes its own answer.

WHAT RUSTLAND DOES NOW, and what a port has to reproduce (kb/load.rs, `Ownership`):
 * THREE PHASES — collect every head across every file; freeze every ladder answer BEFORE
   any mint; then decide and mint. Nothing reads a half-built table.
 * THE DECISION IS "does some scope this one can SEE already INTRODUCE the name" — a
   property of the finished text, not of how much of the scan has run.
 * "CAN SEE" IS THE RESOLVER'S OWN WALK, told about names that are not symbols yet
   (`SymbolTable::resolve_captured_name_with_overlay`). NOT a second traversal built from
   the parent-eligibility filter: `EnclosingLinks`/`ExposureLinks` are PATH properties
   recomputed per hop, the `internal` filter runs on the matched symbol, and a scope
   short-circuits on its own locals first. A hand-built walk REFUSED THREE PROGRAMS THAT
   LOAD CLEAN.
 * A ROUND-BASED FIXPOINT, NOT A RECURSION, and this is the part most likely to be got
   wrong on a port. The relation is NOT monotone — the more scopes own a name, the more
   heads yield, so the fewer own it — so a demand-driven recursion must break cycles
   provisionally, and caching anything computed under such a break reintroduces the order
   dependence. MEASURED on rustland's first attempt: six permutations of three files gave
   two different programs. The three rules are: (1) a scope that can see NOTHING even when
   every other candidate is treated as an owner OWNS; (2) a scope that sees a SETTLED
   owner from every one of its files YIELDS; (3) a remaining tie is broken inside ONE
   strongly-connected component — a member nested inside another member yields, and with
   no nesting among them every member introduces its own.
 * PER-SCOPE SENTINELS in the overlay, so the resolver's own `Ambiguous` signal survives
   `matches.dedup()`; one shared sentinel collapsed two distinct owners into one `Found`.
 * `<global>` MAY OWN what is written at it and is NEVER YIELDED TO. Fusing the two roles
   fails either way round, both measured.
 * PER (scope, name, FILE), because imports are file-local (WI-995).
 * NO DEPTH BOUND is needed, because there is no recursion. Rustland's first version
   aborted the process (SIGABRT, stack overflow) at 700 chained scopes sharing one head
   name and had to carry an arbitrary limit; the fixpoint does not.

ALSO PORT THE ERROR PATH: an ambiguous head must not be answered with a fresh intern of
the short name. For a TOP-LEVEL candidate the short name IS the qualified name, so that
mints a second symbol with the same FQN; rustland aborted on its WI-581 assert and, in
release, stored the clause under a functor that silently no-matches. Answer with one of
the real candidates.

REFERENCE: docs/kernel-language.md §"A rule head functor is resolved, not declared" states
the rule for BOTH implementations, and it is the acceptance spec. proposal 059 R6.
rustland's `wi980_rule_head_order_test.rs` is 24 rows with four stated back-outs, each
naming the line and the rows it fells — port the rows, not just the code.

AMENDED 2026-08-21 (WI-20260821-FQC85 shipped proposal 061 in rustland). THE PORT IS NOW
TWO RULES, AND THE SECOND ONE SHRINKS THE FIRST:
 * A BODY-LESS RULE DECLARES its head's predicate and asserts NOTHING; the name is minted
   in pass 1, like every other name. `fact` is the body-less ASSERTION, and it desugars to
   an explicit `:- true` — which scaland must also read as the EMPTY CONJUNCTION, or every
   migrated site loads clean and answers nothing (measured on rustland before the fix:
   `true` is a boolean_literal, so the body carried a constant goal nothing resolves).
 * A PREDICATE WHOSE HEADS SPAN MORE THAN ONE FILE must be declared, or the load is
   refused naming the files. Every cross-FILE shape in the list above is now that refusal
   in rustland, so the fixpoint's remaining job is the single-file case — which is still
   the whole of rules 1-3 and still needs the port.
 * A body-less rule that can declare NOTHING (a `⊥` denial, a multi-head rule, a qualified
   head, a paren-less nullary) is refused, as is a declaration carrying a label, a
   description, a `[…]` tag, a `[t]` introducer or a typed column `?x: T`.
DIVERGENCE TODAY, and it is silent: scaland's `Loader.scala` still reads `rule.body.isEmpty`
as a FACT, so the stdlib's 11 intuitionistic axioms — now DECLARATIONS in the shipped
source — are asserted there as universally-true facts, and every `:- true` clause loads as
a bodied rule whose `true` goal never resolves. The shipped stdlib PARSES in scaland
(`ParserIntegrationTest`), which is what keeps sbt green; nothing drives those predicates.

REFERENCE for the amendment: docs/kernel-language.md §5.3 ("No body ⇒ DECLARES"), §6.1 and
§8.6 ("Auto-declaration, and where it stops"); rustland's
`wi_fqc85_rule_declaration_test.rs` is 12 rows with four stated back-outs.

ACCEPTANCE: sbt test green; the shape above gives ONE predicate in BOTH text orders and,
WITH A DECLARATION, across two FILES at one address; the same pair WITHOUT one is a
located refusal naming both files; a mutual-import pair each introduce their own in either
file order; a facade importing its own submodule joins at TWO and THREE levels of nesting;
`<global>` is never yielded to, with the documented top-level form still loading; a
body-less rule asserts nothing and `rule H :- true` asserts exactly what `fact H` does. Say
at each site which rows fail when the change is backed out.

## Changes

### 2026-09-08T10:54:59Z — feedback — claude

DELIVERED (scaland). Both halves are ported and DRIVEN; `sbt test` is 564 rows, 562 pass.
The two failures are PRE-EXISTING AT HEAD — `BootstrapTest`'s WI-1066 / WI-1055, cb875e77's
`field.anthill` cross-package `requires Ring`, recorded as untouched in WI-20260906-6BX85
and re-verified here in a clean worktree.

THE TICKET'S ALGORITHM WAS STALE, and correcting it is the first thing this delivery did.
It prescribes WI-980's `Ownership` fixpoint — the optimistic overlay, three settling rules,
the SCC tie-break, the `(scope, name, FILE)` key, the `<global>` two-roles exception and the
depth bound. WI-20260822-845G7 DELETED all of it in rustland the day after this ticket was
amended: 061 made a predicate DECLARED rather than discovered, and the census then said the
fixpoint computed a CONSTANT — 234,078 head decisions, 233,917 "introduce here", every one
of the 161 joins in a fixture written to exercise the fixpoint itself, zero in the shipped
corpus. What is ported is therefore the CURRENT rustland shape:

  A rule head whose functor RESOLVES is a clause of what it resolves to. One that resolves
  to NOTHING declares its predicate at the scope it is WRITTEN IN.

Nothing is asked about any other head, so no order can enter; order-freedom is a property
of the rule rather than a result. What replaced the decision is a REFUSAL — two scopes that
can see each other may not both introduce one name.

WHAT LANDED
 * 061'S READING — `RuleReading` (Declaration / Clause / DeclaresNothing), ONE decider
   shared by the mint and the load. A body-less rule DECLARES and asserts nothing; a
   body-less head that can declare nothing is refused; a declaration carrying a label, a
   `[…]` tag or a typed column is refused; a declaration of a name another construct owns
   is refused.
 * `:- true` IS THE EMPTY CONJUNCTION (§6.1), at the introduced-functor reader and at the
   body build, so `rule H :- true` asserts exactly what `fact H` does.
 * PASS 3 IN THREE PHASES — collect every head, freeze every ladder answer off the pre-mint
   table, then decide and mint.
 * THE VISIBILITY REFUSAL (845G7) — `headNameCollisions` over a new
   `SymbolTable.resolveWithOverlay`: the resolver's OWN walk, told about names that are not
   symbols yet through PER-SCOPE sentinels. Weakly-connected groups; the named owner is the
   member REACHED BY every other, per (scope, FILE); `<global>` excluded from the CANDIDATE
   SET, not only from the overlay.
 * 061'S FILE RULE — a predicate with heads in more than one file must be declared, refused
   naming the files, suppressed where the visibility refusal already asks for a declaration.

THE PORT NEEDED ONE PASS RUSTLAND DOES NOT, AND A ROW FOUND IT. rustland mints a declaration
inside pass 1, which is safe because its `SymbolTable::define` merges a KIND SET. A scaland
symbol carries ONE kind and an `operation` mint goes through `defineSymbolOnce`, so an
interleaved walk let TEXT ORDER decide the kind: MEASURED, `operation has(x) -> Bool` beside
`rule has(?x)` was refused with the operation written first and LOADED CLEAN with the rule
written first, stamping `has` a `Goal` and swallowing the no-op line — a NEW order dependence,
introduced by the fix for the old one. `DeclarePredicatePass` is now its own walk over every
file, after pass 1 and before pass 2, which restores the WI-321 invariant for this kind too.

AND ONE SWITCH THE PORT DOES NOT NEED. rustland's `resolve_captured_name_with_overlay` passes
`ExposureLinks::Skipped`; scaland's walk already refuses a non-variant name at the exposure
edge (`exposed.contains(name)`), and a name that IS a variant makes the head DENOTE so it
never becomes a candidate. Stated at `resolveWithOverlay` rather than left as a silent
omission.

CORPUS COST OF BOTH REFUSALS IN SCALAND: ZERO, the same as rustland measured.

WHAT WAS SILENTLY WRONG BEFORE — the half the amendment named, now measured here:
`logic/constructive.anthill`'s eight intuitionistic axioms (DECLARATIONS in the shipped
source) were asserted as universally-true facts whose two-variable heads answer any goal,
and every `:- true` clause (`reflect/typing.anthill`, `realization/realization.anthill`,
`prelude/set.anthill`, `prelude/lattice.anthill`) loaded as a BODIED rule whose `true` goal
nothing resolves, so those predicates answered NOTHING. One row reads the shipped corpus and
drives `modus_ponens(7, 8)` to 0 at the axiom's own arity.

TESTS. `RuleHeadDeclarationTest`, 23 rows: 061's reading (8), the five visibility channels,
the named-owner chain, the equation-subject party, the file rule with its single-file and
equation controls, the file-shaped LIMIT below, and four CONTROLs. Four `LoaderTest` fixtures
migrated to `fact` / `:- true`, each with a note saying which reading changed.

BACK-OUTS, ALL APPLIED AND RUN over the whole suite, listed at the file header with the rows
each fells: the 061 reading 11, the empty conjunction 14, the pass-1b mint 8, the collision
refusal 8, THE PHASE FREEZE 10, the asking file 4, the named owner (sink) 3, the per-file
owner 1, the per-scope sentinels 8, `<global>` as a candidate 1, `DeclaresNothing` 1, the
file rule's equation exemption 1. TWO LINES HAVE NO TARGETED BACK-OUT and say so: the
connective guard in `ruleReading` (121 rows — the stdlib stops loading) and the visibility
test itself.

WHAT `/code-review` FOUND — four findings, three acted on and one that is not this port's:
 * THE COLLISION REFUSAL HAS A FILE-SHAPED BLIND SPOT. Reach is asked only from the files a
   candidate WRITES A HEAD IN, so a scope re-opened across files with the `import` in one
   file and the head in another produces no edge and no refusal — while the same program
   with that import line moved into the head-writing file IS refused. NOT A PORT DEFECT:
   rustland answers identically, MEASURED on the same three files through `anthill load`
   (`loaded: 2848 facts, 182 rules` versus the same `ns.A, ns.B` refusal at the same head).
   Closing it in scaland alone would make the two loaders disagree about which programs
   load, which is the divergence class this ticket removes. Recorded at the site and DRIVEN
   by a row that asserts the silence, including `reads(2)` = 0 against a control of 1.
 * PASS 1b USED PLAIN `define`, reopening the unconditional `byQualifiedName` write that
   `defineSymbolOnce` is documented to guard "by any route to a colliding qualified name".
   Switched; every measured behaviour is unchanged (the idempotent second declaration and
   the operation-kind clash both still work), and the unreachable case becomes a loud
   refusal instead of a silent remapping.
 * A `provides … language anthill` BODY-LESS RULE whose name the enclosing scope already
   holds is NOT refused — and that is right, not a hole: the block opens no scope, so it IS
   that scope, and the rule is 061's admitted second declaration of one predicate at one
   address. Said at the arm so the next reader does not re-derive it.
 * FOUR DOC-DRIFT SITES still naming `DefinePass.defineRule`, `RuleHeadPass` and "the three
   scan passes". Corrected.

TWO RUSTLAND REFUSALS ARE STILL NOT PORTED, and one is now DRIVEN as a gap rather than left
unsaid:
 * C666A (an unguarded non-enclosing predicate join). The named-owner row loads the chain
   `zzA -> zzB -> zzC` with a declaration at the sink and asserts that `zzC.cp` absorbs only
   `zzB` while `zzA.cp` stays split — rustland refuses that program; scaland is silent. The
   silence makes the row a SHARPER measurement of the owner test, and it is recorded there.
 * WI-20260821-D0EXD (an equation subject may not resolve to another scope's PREDICATE).
   Out of scope; the part of it that is WI-898 rather than a refusal — the collision
   message's `equationElsewhere` branch — IS ported and driven.

rustland is byte-for-byte untouched, so `cargo-test` was not re-run: it would measure HEAD
rather than this work, and the volume is at 98%.

### 2026-09-08T11:12:23Z — feedback — claude

#### AMENDED AFTER REVIEW (2026-09-08)

USER CORRECTION: "empty conjunction in a rule does not mean `true` now". Right, and the
delivery's prose was one ticket out of date. 061 introduced the top-level `:- true` strip
under the reading "`true` IS the empty conjunction"; WI-20260822-J38JE then settled the
MEANING one rung lower — a boolean constant in GOAL position is a SEARCH, `true`
succeeding and `false` failing, at EVERY goal position — and put it in the RESOLVER,
because a loader strip over the body's top-level goal list can never reach a goal nested
under `not` or `|`. The strip survives as a BODY-SHAPE device only: 061 item 5, since only
an EMPTY body makes `fact H` and `rule H :- true` one clause.

SCALAND HAS THE STRIP AND NOT THE ARM, and that is now DRIVEN rather than implied.
MEASURED here against J38JE's own table:

    :- true             1   (correct — the strip)
    :- false            0   (correct BY ACCIDENT — a constant names no name)
    :- not(false)       0   <- logic says 1
    :- base(9) | true   0   <- logic says 1
    :- 42               0, loads clean   <- rustland REFUSES it, located (J38JE item 4)

Recorded at `isEmptyConjunctionGoal` and driven by the row `J38JE GAP: a boolean constant
goal has no reading below the top level`, asserted at the values scaland actually gives so
it fails the day the arm lands.

AND THE BACK-OUT NUMBER IS RELABELLED, because it was measuring the wrong thing: dropping
the strip fells 15 rows HERE and **zero** in rustland, where the resolver arm answers every
`true` the strip stops seeing (rustland corrected `wi_fqc85`'s own back-out list when
J38JE shipped). The 15 measures the MISSING ARM, not the strip.

USER QUESTION: were scaland symbols given many kinds, as in rust, for a sort sharing a
free-standing entity's name? NO — verified in both trees. rustland's `SymbolDef::Resolved`
carries `kinds: SmallVec<[SymbolKind; 2]>` with `add_kind`/`kinds()`; scaland's carries a
single `kind: SymbolKind`, and there is no `addKind`/`hasKind` anywhere in `core/src`. What
scaland has instead is SEPARATE REGISTRIES, one role each: a free-standing `entity E(…)`
gets `SymbolKind.Entity` on the symbol PLUS `registerSort(E, SortKind.Constructor)` in the
KB's per-TERM sort registry, plus `constructorSymbols_` and `entityParent_`. None of them
is a second kind on the symbol — which is why `hasTypeReading` reads only
`SymbolKind.Sort`, and why a namespace-level entity has no type reading (one of the five
splits WI-20260902-CZJ2N's note already names). The single-kind field is exactly what
forced `DeclarePredicatePass` into its own walk; the alternative — porting rustland's kind
SET — is named at that pass as a ticket of its own, since ~20 sites pattern-match
`SymbolDef.Resolved` by kind.

Suite after the amendment: 565 rows, 563 pass, same two pre-existing failures.

