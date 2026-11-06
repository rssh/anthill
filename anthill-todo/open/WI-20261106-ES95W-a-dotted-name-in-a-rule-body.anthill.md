## Attributes

- id: WI-20261106-ES95W-a-dotted-name-in-a-rule-body
- created: 2026-11-06T09:25:15Z

- status: Open
- status_agent: user
- status_at: 2026-11-06T09:25:15Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a dotted name in a rule-body DATA slot that names nothing loads clean: `rule q :- p(Bogus.zero)` — unresolved, the chain is an application of `field_access` over two bare names, and WI-1058's data-slot check asks only whether `field_access` names something

## Changes

### 2026-11-06T09:25:45Z — feedback — user

FOUND BESIDE WI-20260825-6RRVA (bd8eebdf), which closed the same blind spot in a clause HEAD. MEASURED on bd8eebdf: `fact p(1)` + `rule q(?x) :- p(Bogus.zero)` loads clean (4399 facts, 269 rules). In a rule body an unresolved paren-less dotted name falls through every rung of the body walk's field_access arm (rule / const / sort / ctor / op ref, then the two dot-field passes) to an ApplyOrConstructor of `field_access` over two bare names, and WI-1058's `data_functor_error` (typing/rule_dispatch.rs) asks `undefined_functor` of `field_access` only, which names something. WHY NOT FOLDED INTO 6RRVA: the head check reads the chain at the PARSE node (`dotted_name_rooted_at_no_binding`, the binding and value-prefix gates, the prefix rule naming a chain once); WI-1058 judges OCCURRENCES in the typer, where that provenance is gone, and a loader-side copy would be a second mechanism for WI-1058's question. A fix probably wants the body walk to keep the chain's dotted name on the occurrence (or record a site as the head does) and have one predicate judge both — and a census of the suites first: the body walk is shared with operation bodies, where the typer already refuses such a name ("expected resolved name, got unresolved").

