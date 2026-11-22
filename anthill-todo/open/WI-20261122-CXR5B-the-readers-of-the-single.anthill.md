## Attributes

- id: WI-20261122-CXR5B-the-readers-of-the-single
- created: 2026-11-22T10:23:52Z

- status: Open
- status_agent: user
- status_at: 2026-11-22T10:23:52Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261121-JE2MT-two-readings-of-which-sort-a

- tags: typing

## Description

THE READERS OF THE SINGLE CARRIER PARAMETER MOVE TO THE SORT CARRIER AND THE OPERATION CARRIER (stage 2 of docs/design/spec-carrier-set.md; filed with the user 2026-11-22. Stage 1 is WI-20261121-JE2MT, which delivers the owner `sort_carrier` and the derivations built on it).

The implementation computes ONE carrier parameter per spec, by five ladders (design §2, L1-L5), and about 120 sites read it (docs/design/spec-carrier-set/readers.md): dispatch, the coherence grouping, the witness classification, the default rows, the member checks, projections and refusals.

DECIDED with the user (design §6):
- 1: a call fixes its OPERATION CARRIER, the type-vars its signature mentions (`Self` mentions them all). Parameters are fixed by the arguments, the result by the type expected at the call, any type-var by a bracket or a `requires`, and a provider's provisions by a bracket naming it. What the call leaves unfixed is read off the provisions at what it fixes. It is refused when it fixes nothing and names no provider, or when those provisions disagree. One provider and several are held alike, so §8.7's refusal of one provider writing two provisions goes. The kernel-language.md §5.4 wording is approved, with its amendment.
- 3: a provision binds each type-var an operation takes a value of.
- 4: the SORT CARRIER is all the type-vars, for every spec; `Self` is the spec at all of them.
- 5: anthill.reflect.typing.provision_carrier's ?c is the SUBSTITUTED SORT. self_provides, default_provider, the loader's default index and one_default move with it.
- 6: a binding whose type-var appears only in operations' results does not make a provision the provider's own.

MEASURED today (design §3; docs/design/spec-carrier-set/run.sh reruns each):
- b3/b4: the carrier and the default row move with the order two type-vars are declared.
- b5-b8: two witnesses that differ in a type-var no argument fixes are a first match by declaration order.
- d5 and e3/e5: one provider writing two provisions is refused at load.
- d7: naming the witness in a bracket is refused.
- d11: a call naming its provider is refused, although it should answer 1.
- d12: a call naming its provider on a spec with no type-vars loads clean and fails at run ("operation has no body").
- e4: a provider whose values `joinTwo` receives is filed as a witness.
- e5: a `joinTwo` bound by name has its receiver refused where the same member passes.
- c1: a Monad witness at another sort is refused; its cause is to be named.

TO DO:
- the readers, by question (W, O, S, V, P, M, K, X: design §4);
- the two indexes keyed by the single parameter: ProvidesIndex's witness carriers, and the eq-dispatch index's witness filing (WI-20261121-DBR8V's (b) follows from it);
- the default index's key under a compound ?c, on the per-call path;
- kernel-language.md §5.1, §5.2 (the `Self` passage's wording is still to be drafted for the user), §5.4 (approved), §8.3, §8.7;
- a note in 058 §3.6.

ACCEPTANCE: design §7's stage 2 rows, each driven with its back-out; families green; full workspace green via rustland/scripts/test.sh; scaland testFull.

## Changes

### 2026-11-22T11:03:31Z — feedback — claude

Two decisions this ticket restates changed with the user on 2026-11-22, after a fourth review of docs/design/spec-carrier-set.md. They supersede the description where it differs. DECISION 5, corrected: provision_carrier's ?c is the type of the values the provision is for. For a spec with a dictionary that is the spec at all its type-vars (`Set provides Eq[T = Self]` is at `Eq[T = Set]`). For a self-representing spec it is the PROVIDER at its own type-vars (`List provides Stream[T = T, E = {}]` is at `List[T = T]`), and the spec's type-vars are read off it. With the spec's substituted sort there instead, rule (2) of default_provider would write six overlapping 'default Stream' rows, and one_default (check_one_default, kb/defaults.rs:798) would refuse the standard library (probes g1-g4). DECISION 6, decided again (it was option (b)): every binding counts. A provider provides a spec for itself when its sort is the head of the carrier or the head of one of the carrier's bindings. One verdict moves: f4, two sorts each owning a provision of Coll[C = Foo, Elem = Num], is refused at load until one is marked `default provides`; it runs today. f1's Num gains a harmless inferred default row. f2's Foo for Dflt and the nine stdlib NonEq self-provisions keep their own provisions. Stage 2's rows for both are in the design's §7.

