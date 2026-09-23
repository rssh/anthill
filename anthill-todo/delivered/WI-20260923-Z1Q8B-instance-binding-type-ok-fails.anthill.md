## Attributes

- id: WI-20260923-Z1Q8B-instance-binding-type-ok-fails
- created: 2026-09-23T14:30:48Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-23T16:38:06Z

- acceptance: cargo-test

- tags: typing

## Description

INSTANCE_BINDING_TYPE_OK FAILS OPEN ON EVERY `Value::Node`, SO WI-1MAGR IS SILENT ON A DENOTED-BEARING SIGNATURE MISMATCH — the twin of the carrier gate 87246ea2 fixed in the override return leg.

WHAT EXISTS. `instance_binding_type_ok` (kb/typing/signature.rs, WI-431 B) decides only when BOTH types are `Value::Term` and neither `contains_type_param`; any `Value::Node` answers `None` ("not confident"). Its doc calls that "a non-ground / `Value::Node` parametric type — fail open". That reads the CARRIER where ABSTRACTNESS was meant: a type rides `Value::Node` whenever it carries a denoted (a literal type argument such as the `3` in `Foo[T = Int64, N = 3]`), not because it is parametric. It is the conflation WI-20260822-1TKN0 recorded for the effects leg of `check_override_refinement`, and that 87246ea2 removed from the same function's return leg (`a_denoted_return_type_mismatch_is_compared`).

Every caller fails open on such a type: `check_member_signature` (WI-1MAGR — each parameter, contravariant, and the return, covariant), `member_params_are_a_permutation`, and `check_instance_fact_op_signatures` (a bound op's parameters and return).

MEASURED (2026-09-23, at 87246ea2). This program loads with ZERO errors:

    sort Foo
      sort T = ?
      sort N = ?
      entity foo(v: T)
    end
    sort Sp
      sort T = ?
      operation op(x: T) -> Foo[T = Int64, N = 3]
    end
    sort Carrier
      entity c(id: Int64)
      provides Sp[T = Carrier]
      operation op(x: Carrier) -> Foo[T = String, N = 3] = foo(v: "s")
    end

The same program with `-> Int64` on the spec and `-> Bool = true` on the member IS refused by WI-1MAGR ("does not fit … the member returns `Bool`, which is not a subtype of the spec's `Int64`"). The spec op is body-less, so the member is the only thing that could back it — the case WI-1MAGR exists for.

WHY 87246ea2 DID NOT SIMPLY SWAP THIS GATE TOO. Two pieces, and only the first is a gate:
 (1) THE GATE. `!view_contains_type_param` on both Values (the effects leg's predicate, and now the return leg's) decides the MEASURED shape above, whose spec type mentions no spec parameter. `types_compatible` must then be asked of the two Values as they are, not of `Value::term(..)` rebuilt from TermIds.
 (2) σ OVER A `Value`. The comparison σ-substitutes the spec type first, and the only substituter is TermId-level (`substitute_impl_params_alloc`). `sigma_subst_effect` (kb/typing/synth.rs) substitutes a `Value::Term` and passes a `Value::Node` through UNSUBSTITUTED. So a Node-carried spec type that mentions a spec parameter (`-> Foo[T = T, N = 3]` under `provides Sp[T = Carrier]`) stays undecidable — safely, because the gate sees the parameter — here AND in the override return leg after 87246ea2. One Value-level σ (an occurrence rebuild or a view map), owned in one place and used by both `sigma_subst_effect` and this function, is what closes it.

WHAT TO DECIDE AT PICKUP.
 (a) Whether (2) lands here or is split off. (1) alone fixes the measured program; (2) is what makes the parametric shape decidable, in two readers at once.
 (b) `member_params_are_a_permutation` calls this too: check its "two parameters of the same type swapped are not decidable" semantics (`two_parameters_of_the_same_type_swapped_are_not_decidable`) survive a wider gate on Node-carried parameters.
 (c) MEASURE THE STDLIB AND THE CORPUS. A wider decision can refuse something that loads today. Record every newly refused program: each is either a real mismatch (fix the program) or a relation `types_compatible` gets wrong on a Node carrier (a separate defect, filed, not papered over by keeping the gate).

ACCEPTANCE: the MEASURED program above is refused by WI-1MAGR naming both return types; its control (`Foo[T = Int64, N = 3]` on both sides) loads; a parameter-position twin (the spec takes `f: Foo[T = Int64, N = 3]`, the member `f: Foo[T = String, N = 3]`) is refused; if (2) lands, a spec returning `Foo[T = T, N = 3]` under `provides Sp[T = Carrier]` refuses a member returning `Foo[T = Int64, N = 3]` and accepts `Foo[T = Carrier, N = 3]` — in WI-1MAGR and in the override return leg alike; each back-out measured and stated at its test; full workspace green via rustland/scripts/test.sh.

REFERENCE: kb/typing/signature.rs (`instance_binding_type_ok`, `check_member_signature`, `member_params_are_a_permutation`, `check_instance_fact_op_signatures`, and `check_override_refinement`'s return leg with its 87246ea2 comment); kb/typing/synth.rs (`sigma_subst_effect`, `substitute_impl_params_alloc`); tests/include/wi1magr_member_signature_test.rs; tests/include/wi347_override_refinement_test.rs (`a_denoted_return_type_mismatch_is_compared`, `denoted_ret_src`); commit 87246ea2.

## Changes

### 2026-09-23T16:38:00Z — feedback — user

DELIVERED in 5ec10808. A signature over a denoted-bearing type is compared, and σ grounds beneath it.

MEASURED FIRST (87246ea2, CLI): the ticket's program loaded clean; so did the parameter twin (spec f: Foo[T = Int64, N = 3], member f: Foo[T = String, N = 3]), the instance-fact binding twin, the σ shape in WI-1MAGR (spec -> Foo[T = T, N = 3] under provides Sp[T = Carrier], member -> Foo[T = Int64, N = 3]), the same in the override return leg (with a spec default body, so only that rule speaks), and a spec effect row {Tagged[T = T, N = 3]} widened by the override's {Tagged[T = Int64, N = 3]}.

(a) BOTH HALVES LANDED HERE.
  (1) GATE: instance_binding_type_ok asks view_contains_type_param of both Values and compares the Values as they are. On the term carrier it decides arm for arm what contains_type_param did.
  (2) σ: sigma_subst_effect is now sigma_subst_type, the one Value-level σ, reading the type through TermView. A hash-consed subtree still takes substitute_impl_params_alloc; any other carrier is read through the view and only the spine above a replaced leaf is rebuilt (Value::Entity); an untouched subtree keeps its carrier. Four readers use it: the signature rule, the override return leg, the override effects leg, the instance-fact bindings (whose refusal now prints the spec type at the provision's bindings).
(b) member_params_are_a_permutation: the same-type boundary survives. The order search is reached only from positions that already compared incompatible, so two same-type denoted-bearing parameters swapped still load and run the swap (driven: two_denoted_parameters_of_the_same_type_swapped_are_still_not_decidable). Different types swapped are now reported as an ORDER mistake (denoted_parameters_swapped_are_reported_as_an_order_mistake).
(c) CENSUS, report-only (old and new verdict both computed, every difference logged, instrumentation removed):
  * stdlib + corpus (46 project dirs, 180 files alone): 0 verdicts moved, σ changed 0 inputs. Cross-check, HEAD's CLI vs this one over the same loads: identical up to the instance ORDER of one PartialEq ambiguity message, which varies run to run on HEAD.
  * full workspace suite (7383): 2 moved, both 87246ea2's wi347 fixtures. result_ret_denoted (a deliberate mismatch) is now ALSO refused by the signature rule; its row asserts the discharge refusal, still there. result_ret_denoted_ok is now compared and accepted.
  No newly refused program is a relation types_compatible gets wrong.

TESTS, 14 rows (wi1magr 7, wi347 4, wi431 3). BACK-OUT, measured over all 6532 anthill-core tests:
  G (carrier gate restored) -> 6: wi1magr return / parameter / order / σ refusals; wi431 denoted-return and σ-message refusals.
  S (σ passes the occurrence carrier through) -> 4: one per σ reader (wi1magr σ, wi347 return leg, wi347 effects leg, wi431 σ message).
  Controls drive their programs and pass either way by design.

REVIEW /code-review (high): 8 findings, 3 fixed (effects-leg σ undriven; a control that only loaded; the instance-fact message printed the un-σ'd spec type), 1 not needed (an Opaque head stays unsubstituted and fails open by design), 4 skipped: requires_shadow_is_confusable keeps a TermId-only σ and gate (fails open to its warning, the safe side); σ can rewrite an Expr leaf inside a denoted (no producer puts a type parameter there); the order search re-applies σ per permutation (bounded, diagnostic path); sigma_subst_view shares its shape with substitute_ref_terms (different leaf rule and carrier preservation, documented).

FOUND, not this ticket: .v on a value typed Foo[T = Int64, N = 3] stays an unresolved FieldOf and the load is refused, while on Foo[T = Int64] it types as Int64 (HEAD too). Being fixed next, inline.

DOCS: kernel-language §8.7 (ground is a property of the type, not of its carrier). The WI-347 doc is back on check_override_refinement, where 9cb362a2 had displaced it.
RUST-ONLY: scaland has no member-signature or instance-binding check.
cargo-test: full workspace green via rustland/scripts/test.sh (36 binaries, 7397 passed, 0 failed).

