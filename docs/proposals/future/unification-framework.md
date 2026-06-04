# Future: Unification as a framework of per-sort registered algorithms

> **Stub** (2026-06-04) — to be extended. Unnumbered (see [README](README.md)).

## Idea

Unification is not one fixed algorithm but a **framework that dispatches to a
per-sort registered algorithm**, with syntactic (first-order) unification as the
default. A sort may register its own — effect rows register row unification
(Rémy; WI-307), sets register AC, intervals register CLP(R). This **condenses**
several apparent gaps in the typer into one mechanism (see
[`type-parameter-scoping.md`](../../design/type-parameter-scoping.md)
§"Relationship to the logical-rules engine"): effects stop being a parallel
algebra; value-in-type (`denoted`) equality is just the embedded value's sort's
unifier; the resolver and the typer share one dispatcher.

## Basis

The mechanism is the **reprogrammable / monadic** unification approach — each
theory is a subclass of the unification monad, so one customizable unification
implementation hosts many logic systems. Formal basis and Scala prototype:

> R.S. Shevchenko, A.Yu. Doroshenko, O.A. Yatsenko. *Embedding a family of logic
> languages with reprogrammable monadic unification in Scala* (Вбудування
> сімейства логічних мов із можливостями перепрограмування монадичної уніфікації
> в Scala). **Problems in Programming (Проблеми програмування)**, 2024, No. 1.
> DOI: [10.15407/pp2024.01.03](https://doi.org/10.15407/pp2024.01.03).

## Substrate for WI-010

Typing-as-constraints solved by per-domain solvers *is* CLP; the per-sort
unification framework is the engine WI-010 (resolver-as-type-checker) wants.
Effects (WI-307) are the existing proof-of-concept that it must exist.

## To extend

- the unifier interface a sort registers (monad subclass / `unify_S`);
- the **order** relation alongside equality — per-sort subtyping / variance /
  join-meet (proposal 035 already expresses variance as SLD rules over
  `Covariant` / `Contravariant` facts; WI-293 consumes them), so the framework
  dispatches per-sort *ordering* too, not only unification;
- theory composition (Nelson–Oppen / Baader–Schulz; disjoint-signature
  decidability);
- termination obligation; discrimination-tree indexing under non-syntactic
  theories.
