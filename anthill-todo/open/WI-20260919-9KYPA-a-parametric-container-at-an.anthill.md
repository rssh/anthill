## Attributes

- id: WI-20260919-9KYPA-a-parametric-container-at-an
- created: 2026-09-19T22:18:39Z

- status: Open
- status_agent: user
- status_at: 2026-09-19T22:18:39Z

- acceptance: cargo-test, scaland-sbt-test

- tags: modinst

## Description

A PARAMETRIC CONTAINER AT AN UNLAWFUL ARGUMENT IS NOT REFUSED WHERE THE TYPE IS WRITTEN — the last leg of the NonEq mirror. MEASURED (2026-09-19, at 99b962a5, one fixture per row, `operation k(s: Set[T = <key>]) -> Int64`): Set[T = Float] REFUSED; Set[T = Pt] (pt(x: Float)) REFUSED; Set[T = Holder] (holder(o: Option[T = Float])) REFUSED — that one is new, from CKD4J's mirror; Set[T = List[T = Float]] LOADS; Set[T = Option[T = Float]] LOADS. The two that load are the gap kernel-language.md §8.3 already names: 'It reads the key's own provisions, so a key whose unlawfulness is in its ARGUMENT (Map[K = List[T = Float]], Map[K = (a: Float)]) is a known remaining gap, not a guarantee.'

WHAT IS ALREADY RIGHT, so the gap is narrow and is about ONE channel. (1) RUNTIME equality: since CKD4J's mirror the partial-carrier gate walks through a parametric constructor, so eq(cons(nan, nil), cons(nan, nil)) and eq(some(nan), some(nan)) answer FALSE (they answered TRUE before). (2) The POSITIVE channel at CALL sites: List.contains over List[T = Float] elements is refused through the conditional Eq rows CKD4J derives (wi_ckd4j_conditional_eq_derivation_test::a_float_element_is_still_refused pins both List[Float] and Option[Float]). What is missing is only the NEGATIVE channel at a WRITTEN TYPE — an entity field, a parameter or return type, a const's type, a sort alias, a let annotation, a typed lambda binder, a binding inside requires/provides, and nested inside any of those (WI-644/WI-835's enumeration).

TWO PARTS, and neither alone closes it. (a) DERIVE THE CONDITIONAL NonEq: eq_derive derives provides PartialEq[S] :- PartialEq[P…] and Eq[S] :- Eq[P…] for a parametric sort (derive_conditional_eq); the mirror row provides NonEq[S] :- NonEq[P…] is not derived, so List[T = Float] is not a WITNESSED NonEq carrier and the negative check sees nothing. Note the asymmetry the existing code documents: a derived NonEq carries the witness operation nonEqRefl which no carrier backs, which is why eq_derive::run stands after check_provider_operations and marks its rows (mark_unbacked_derived_provision) — a conditional NonEq row must do the same, and must NOT collide with the PartialEq row the same carrier already has (Eq ⊥ NonEq is checked per carrier by check_eq_noneq_exclusive, and a parametric carrier would now hold a conditional Eq AND a conditional NonEq, which are not contradictory: they hold at DIFFERENT arguments. That check must learn to read the conditions before this can land, or it will refuse every conditional carrier.) (b) THE USE-SITE CHECK MUST RESOLVE A GOAL: check_use_site_requires_eq reads the key's own provisions (a witnessed NonEq row at the carrier); for List[T = Float] it must instead resolve NonEq[List[T = Float]] through the conditional row. Cost: the check runs per written type, so a resolution per key site — measure it.

OUT OF SCOPE, recorded so it is not mistaken for this: a NAMED TUPLE key (Map[K = (a: Float)]) has no sort to carry a provision at all, so neither part reaches it; that one needs the structural reading WI-644's enumeration leaves open.

ACCEPTANCE — driven, each saying at its site which change it fails without: Set[T = List[T = Float]] and Map[K = Option[T = Float]] are REFUSED where the type is written, naming the key, the parameter, the carrier and the required spec; Set[T = List[T = Int64]] and Map[K = Option[T = Int64]] still LOAD (the control that the refusal is conditional and not a blanket one for parametric keys); the five programs of wi_ckd4j_conditional_eq_derivation_test still answer, and a_float_element_is_still_refused still refuses; eq(cons(nan, nil), cons(nan, nil)) stays FALSE; check_eq_noneq_exclusive does not refuse a carrier holding a conditional Eq beside a conditional NonEq, with a test that a carrier holding an UNCONDITIONAL pair is still refused; cargo-test green.

REF: rustland/anthill-core/src/kb/eq_derive.rs (derive_conditional_eq, run's marking, the module header's remaining-gap paragraph); typing::check_use_site_requires_eq (WI-644/WI-835); check_eq_noneq_exclusive (WI-658); docs/kernel-language.md §8.3 ('a known remaining gap'); docs/proposals/058-modular-instances.md §3.10; WI-20260918-CKD4J (delivered: the conditional Eq rows, the NonEq classification mirror, the runtime gate).

