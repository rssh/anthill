## Attributes

- id: WI-20261030-0JWYF-a-site-that-lowers-a-value-to
- created: 2026-10-30T15:22:32Z

- status: Open
- status_agent: claude
- status_at: 2026-10-30T15:22:32Z

- acceptance: cargo-test

- depends_on: WI-20261030-BXMPK-a-goal-holding-a-value-with-no

- tags: value-to-term, typing

## Description

A SITE THAT LOWERS A VALUE TO A TERM AND CANNOT, DROPS THE VALUE OR PUTS A PLACEHOLDER IN ITS PLACE, IN SILENCE — step 3 of retiring `value_to_term`: every remaining site that drops or falls back raises an error instead, until its structure holds values. Filed by the user's decision, 2026-10-30.

THE SITES (READ, the audit of every caller after c541ef90; rustland/anthill-core/src, lines as of then; a lower bound). Each lowers a type or a value in a type, so a closure cannot arrive; what fails to lower is a value-in-type with no term form (an occurrence holding a `?param` read, an `if`, a lambda).
  DROP — the value, the binding or the reading is skipped:
  - `binding_grows_past` (typing/requires.rs ~357): answers `false`, so the "grows past" refusal is never raised (fails open).
  - `unified_column_types` (typing/relation.rs ~3363): parameter refs not collected; `clause_goal_columns` (~3978): `.ok()?`, the relation gets no column reading; (~4002) the column not marked unread; `first_column_read_apart` (~3659): `false`, which fails closed (the seal refuses).
  - `call_bracket_instances` (typing/rule_constraints.rs ~934): the binding filtered out; `constrain_domain_test` (~1221): no narrowing.
  - `ground_rigid_projection_if_concrete` (typing/unify.rs ~1781, ~1808) and `ground_sort_param_projection` (~2009): the projection left ungrounded.
  - `domain_field_type_term` (kb/load.rs ~43291): the sort's domain declined, the reason recorded by `record_sort_domain_declined`.
  - Refused at another site, by the comment: `build_default_provider_index` (kb/defaults.rs ~467), `scan_sort_carrier_bindings` (load.rs ~40141), `record_alias_target` (load.rs ~42197).
  FALLBACK — something else stands in its place:
  - `⊥` under a `debug_assert!(false)`, silent in release: `lower_pattern_annotation` (load.rs ~35731); `type_node_to_term`'s arrow binders, named-tuple fields, poly binders and context, `effect_node_to_term`'s guard list, `value_to_pattern_annotation` (kb/node_occurrence.rs ~5479–5651). Likewise a bare variable kept in `surface_node_binding_to_term` (typing/unify.rs ~1017) and a fresh `?_` in `reconstruct_sort_params` (typing/value_type.rs ~80); `entity_type_on_builders` (typing/result.rs ~459) errs, and its callers `debug_assert!` and fall back (~142, typing/carrier.rs ~664) or keep the entity (~237).
  - The type returned unchanged or unfilled: `fill_inferred_defaults` / `fill_term_defaults` (typing/slots.rs ~5676, ~5726), `read_unknowns_from_bound` (typing/value_type.rs ~2996); `generalize_columns` treats the pair as no join (typing/relation.rs ~3772).
  - The as-written occurrence discarded for the held term: `term_read_through_aliases` (load.rs ~29163), `contract_goal_as_written` (load.rs ~48996); a base-sort name term with no diagnostic from `plain_spec_term`'s caller (load.rs ~43145); an `Expr::Spliced` from `type_value_of` (typing/type_receiver.rs ~637).
  NOT HERE: the goal sites are WI-20261030-BXMPK; the store layer, `expect_term` and `read_facts_resolved` are WI-20261026-T51MG; the sites that already raise an error stay as they are. WI-20260929-TJ3G4 (the use-site Eq check keeps only `Value::Term` bindings) is the same shape at a site that does not call `value_to_term`.

THE CHANGE: each site reads through the view where its question can be asked of a value; where its destination needs a term (a `TermId` field, a hash-consed key), a value that does not lower is an error: a located load error at a written type, or a panic naming the invariant where no source can produce one — never a skipped value, a `false`, `⊥`, a fresh variable or the type returned as it was, and the same in release as in debug. A site whose refusal is raised elsewhere states which one and asserts it was raised.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh): a row per site a program reaches, with a value that does not lower written where the site reads it, refused (or answered through the view) and failing with the silent arm put back; for a site no row reaches, the arm replaced all the same and the measurement stated at the site. The full gate, the node-carrier control and the families unchanged otherwise.

