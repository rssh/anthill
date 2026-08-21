## Attributes

- id: WI-20260821-SBZ2A-scaland-s-rule-head-binding
- created: 2026-08-21T20:23:24Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T20:23:24Z

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

ACCEPTANCE: sbt test green; the shape above gives ONE predicate in BOTH text orders and
across two FILES at one address; a mutual-import pair each introduce their own in either
file order; a facade importing its own submodule joins at TWO and THREE levels of nesting;
`<global>` is never yielded to, with the documented top-level form still loading. Say at
each site which rows fail when the change is backed out.

