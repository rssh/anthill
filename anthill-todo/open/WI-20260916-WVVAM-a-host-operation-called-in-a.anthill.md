## Attributes

- id: WI-20260916-WVVAM-a-host-operation-called-in-a
- created: 2026-09-16T04:07:27Z

- status: Open
- status_agent: user
- status_at: 2026-09-16T04:07:27Z

- acceptance: cargo-test

- tags: reflect

## Description

A HOST OPERATION CALLED IN A RULE BODY WITH A STRING-LITERAL ARGUMENT DOES NOT REDUCE — it flounders, so the rule silently answers nothing instead of erroring. Found while delivering WI-20260914-Z73FX (its test module records the measurement); PRE-EXISTING, not introduced there.

MEASURED, WITH CONTROLS (2026-09-15, on the built tree, one file, through a rule body):
 * `term_functor_name(?m) = some("meta")` over a `DeclarationMeta` join answers 923 DEFINITE — a host op with a variable argument reduces.
 * `Bool.and(true, false) = false` answers 1 — a host op with two LITERAL arguments reduces, so it is not arity and not literal-ness as such.
 * `term_field(7, "x") = none()` FLOUNDERS — and this is the SHIPPED two-argument reflect accessor, not a probe invented for the ticket.
 * `meta_has_flag(?m, "internal") = true` flounders identically.
The distinguishing argument in every floundering row is a STRING literal. The same calls reduce from an OPERATION BODY, which is how Z73FX's readers are driven.

WHY IT MATTERS. Every reflect accessor that takes a `String` KEY is unusable from a rule body: `term_field`, `meta_has_flag`, `meta_value`. That is precisely the shape "select the declarations whose meta carries this flag" wants, so KB reflection stays operation-body-only and a rule cannot filter on a named thing. And it fails in the one direction this repo's principles exclude — a silent flounder reads as "no such fact", not as "this did not run" (`docs/kernel-language.md`; CLAUDE.md "prefer a loud error over a silent skip").

WHERE TO LOOK. The rule-body reduction path: `KnowledgeBase::host_op_reducible_at_a_value` and its `reduce_args` caller (`rustland/anthill-core/src/kb/resolve.rs` ~11269 and ~10178/10258), with `is_host_mapped_op` / `is_interpreter_mapped_op` (`kb/mod.rs` ~11073). WI-20260826-VPEWK (delivered) states the GOAL-position vs OPERAND-position asymmetry for host ops and is the nearest prior art; WI-20260822-F0HHB (open, deferred) owns what `=` should mean in a rule body and may subsume part of this. FIRST QUESTION FOR WHOEVER TAKES IT: is the string literal failing to reach the host op as a `Value::Str`, or is the op never selected for reduction because an argument carrier is not recognised? The two have different fixes and the measurement above does not separate them.

NOT ASSUMED: that the right answer is "make it reduce". A loud refusal at load — "this host operation cannot be called from a rule body" — would also satisfy the repo's rule and may be the honest fix if the reduction path cannot carry it; that choice wants discussion before implementation.

ACCEPTANCE:
 1. A rule body calling a shipped two-argument reflect accessor with a string-literal key (`term_field(?t, "x")`, `meta_has_flag(?m, "internal")`) either ANSWERS or is REFUSED with a message naming the position — never flounders.
 2. CONTROL: `term_functor_name(?m)` over a join still answers definite, and `Bool.and(true, false) = false` still answers 1 — the rows that already work are not broken by the fix.
 3. CONTROL: the same calls from an OPERATION BODY keep answering as they do today (Z73FX's `meta_readers_answer_from_a_body` and the `wi_z73fx` rows stay green).
 4. Whichever direction is taken is stated in `docs/kernel-language.md` beside VPEWK's asymmetry, so the next reader does not measure it again.
 5. Full workspace green via rustland/scripts/test.sh.

