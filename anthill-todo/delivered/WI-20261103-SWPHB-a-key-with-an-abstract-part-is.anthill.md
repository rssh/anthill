## Attributes

- id: WI-20261103-SWPHB-a-key-with-an-abstract-part-is
- created: 2026-11-03T05:08:30Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-04T07:49:51Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A KEY WITH AN ABSTRACT PART IS SKIPPED WHOLE, so an unlawful part beside it loads: `operation k[F](s: Set[T = (a: F, b: Float)]) -> Int64 = 1` loads, as do `Set[T = Pair[A = F, B = Float]]` and `sort H { sort F = ?  entity h(s: Set[T = (a: F, b: Float)]) }` (measured 2026-11-03), where `Set[T = (a: Int64, b: Float)]` is refused. Since WI-20261102-7AB56 a neutral projection is abstract the same way: `k(x: Leaf[E = Float], y: Leaf, s: Set[T = (a: x.E, b: y.E)])` loads (found by its /code-review; before it every projection key was refused). MECHANISM: `check_use_site_requires_eq` (typing/coherence.rs) skips a binding `type_is_ground` answers false for, and `read_projection_key` answers a key that keeps a neutral as abstract; `eq_holds_at` is asked of a ground key only. WHAT: judge the concrete part of a partly abstract key, with `Eq` assumed at each abstract leaf (a type parameter, a variable, a neutral projection) as the requirement of the code that binds it. The resolver's assumption channel (`available_requires`) covers a goal coarsely — `Eq[T = ?F]` covers `Eq[Float]` — so it is not that assumption as it stands. ACCEPTANCE: the four keys above refused, naming the unlawful part; `Set[T = (a: F, b: Int64)]`, `Set[T = Pair[A = F, B = Int64]]` and `Set[T = (a: x.E, b: y.E)]` over an open `E` load; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-04T07:49:42Z — feedback — claude

Delivered. A key with an abstract part is judged at its other parts: each abstract part (a type parameter, a type variable, a projection nothing fixes) is a rigid with Eq assumed at it, the best case for the part, and the key is resolved under sigma (KeyAtRigidParts in typing/coherence.rs), so an assumption covers only its own part. What the declarations the key is written in require is assumed too: the frame of its operation (its sort's chain under the provision block it is in, its own requires) and each parameter's declaration. The ticket's four keys are refused, a tuple naming its component (Set[T = (a: F, b: Float)]: its component anthill.prelude.Float does not); (a: F, b: Int64), Pair[A = F, B = Int64] and (a: x.E, b: y.E) over an open E load and run. A refused key prints its parameters by name. A type parameter beside a projection no longer exempts the key: (a: F, b: y.E) off a body binder is refused as not judged. Not covered (stated as the check's non-scope 6): a tuple nested in an application is refused, as its ground twin Set[T = List[T = (a: Int64, b: Int64)]] already was; and what a call binds F to is not checked (non-scope 3: k[F = Float]({1.5}) over k[F](s: Set[T = F]) loads, before and after). Spec: kernel-language.md, the = paragraph, wording approved by the user 2026-11-04. Rows: wi_swphb_partly_abstract_key_test (6), wi_7ab56's beside row rewritten. Full workspace 11646 passed, 0 failed; anthill-core under the node carrier 10575 passed; families green; scaland testFull 802 passed.

### 2026-11-04T08:00:40Z — feedback — claude

Follow-up, inline (user, 2026-11-04): a tuple nested in a key is read by its components, as at the top of the key and as the spec says. A nested tuple whose components provide Eq is a part of the key with Eq assumed at it (KeyAtRigidParts), so Set[T = List[T = (a: Int64, b: Int64)]], Pair[A = Int64, B = (a: Int64, b: Int64)], List[T = ()] and a tuple in a tuple load (refused before); List[T = (a: Int64, b: Float)] and List[T = (a: F, b: Float)] stay refused; a tuple no condition reaches does not decide the key. The delivery note's non-scope 6 is gone. Still open: a call requiring Eq at a type holding a tuple is refused by dispatch (WI-20261021-VF8GT's), and an inferred key (let s = {1.5}) is not checked (non-scope 3). Full workspace 11647 passed, 0 failed; families green.

