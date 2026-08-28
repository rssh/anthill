## Attributes

- id: WI-20260827-14EV6-value-as-str-as-int-as-bool
- created: 2026-08-27T22:50:02Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T22:50:02Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`Value::as_str` / `as_int` / `as_bool` ARE CARRIER-NARROW AND SAY SO NOWHERE, so a scalar that rides on a foreign carrier reads as ABSENT rather than as itself -- the silent-drop class WI-477 already removed from this same file's `as_term`.

Each of the three matches only its own variant:

  pub fn as_str(&self) -> Option<&str> {
      if let Value::Str(s) = self { Some(s.as_str()) } else { None }
  }

The SAME string also arrives as `Value::Term(id)` over `Term::Const(Literal::String)` and as `Value::Node(occ)` over `Expr::Const`. On either, `as_str` answers `None`, and a caller reads that as "not a string" instead of "I cannot see this carrier". `as_int` and `as_bool` are the same shape.

THE PRECEDENT IS IN THE SAME FILE AND SETTLES THE DESIGN. WI-477 replaced a silent `as_term() -> Option<TermId>` with a loudly-panicking `expect_term`, and its doc states the reason verbatim: the `None` on a `Value::Node`/`Entity`/scalar "was read as 'no term' and silently dropped the carrier (the binding-erasure class)". This ticket is that decision applied to the three scalar readers.

THE SPLIT IS FORCED BY WHAT NEEDS A KB, and it is not the same for all carriers:
  * `Value::Node(occ)` -> `occ.as_expr()` -> `Expr::Const(Literal::…)` needs NO KnowledgeBase. Pure, and the three accessors can absorb it with no signature change.
  * `Value::Term(id)` needs the term store to look the literal up. It CANNOT be answered from `&self` alone.

SO: widen the three to the `Node` carrier; RAISE LOUDLY on `Value::Term`, naming the KB-taking variant to use instead (`expect_term`'s wording is the model); and add that variant -- `as_str_in(&self, kb)` or equivalent -- for callers that legitimately hold a Term. A caller narrowing deliberately still writes `if let Value::Str(_)`.

THE BLAST RADIUS IS THE POINT AND MUST BE MEASURED, NOT ASSUMED. `as_str` alone has 109 call sites in `rustland/*/src`. Two distinct flips, and they are NOT the same finding:
  * a site that starts ANSWERING where it answered `None` (a Node-carried scalar) -- a masked bug surfacing, which is the point;
  * a site that now PANICS on a `Value::Term` -- each one is a reader that was silently dropping a Term-carried scalar, and each needs its own verdict: pass the kb, or narrow deliberately.
Run the workspace with the change in and triage every panic individually. A blanket `unwrap_or_default()` at a panicking site re-creates the defect the ticket removes.

WHY IT IS FILED SEPARATELY rather than inline in WI-20260827-T2470, which surfaced it: that ticket's own delivery showed twice that two live changes make the attribution wrong (its regression in `wi733` was credited to a neighbouring guard because both were live in one run). This one changes the answer at up to 109 readers and must be measured against a tree where nothing else moved.

ACCEPTANCE: the three accessors driven on ALL THREE carriers per type -- a `Value::Str`, a `Value::Node` over `Expr::Const`, and a `Value::Term` over `Term::Const` -- with the Node row asserting the VALUE (not merely `is_some`) and the Term row asserting the LOUD failure; the KB-taking variant driven on the Term carrier; the count of call sites that flipped, stated, with each panicking site's verdict named; `common::scalar_str` in `rustland/anthill-core/tests/common/mod.rs` collapsed to a call to the widened API (it exists only because the API was narrow); full workspace green via rustland/scripts/test.sh.

REFERENCE: `Value::as_str` / `as_int` / `as_bool` / `expect_term` (rustland/anthill-core/src/eval/value.rs), `ViewHead::Const` and `impl TermView for Value` (rustland/anthill-core/src/kb/term_view.rs), `common::scalar_str` / `entity_field` (rustland/anthill-core/tests/common/mod.rs).

