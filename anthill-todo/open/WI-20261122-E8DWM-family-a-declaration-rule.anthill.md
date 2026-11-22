## Attributes

- id: WI-20261122-E8DWM-family-a-declaration-rule
- created: 2026-11-22T20:38:20Z

- status: Open
- status_agent: user
- status_at: 2026-11-22T20:38:20Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

FAMILY a-declaration-rule REACHES ITS RULE AGAIN. The family (rustland/anthill-core/tests/families/declaration_rule.rs) was built for kernel-language.md §8.7's declaration rule — a member typed by its own sort at its own parameter, and a projection off it, behind a spec `Sp[T, K, L, J]` with `op(t: T, x: K, y: L)`. Since WI-20261003-GR5EN (a left-out parameter is the `?` written there) every program stopped at a `narrower` refusal before that rule, and since WI-20261122-CXR5B step 7 (decision 3: a provision binds each type-var an operation takes a value of) all 6,160 are also refused ProvisionNamesNoCarrier, because every provision of the template leaves `L` (and, under `spec-x = k`, `K`) out. Binding them is no repair: the member writes `y` as a projection off its own `x` (`x.J`, `x.v.T`, `List[T = x.J]`), which no provision can write as `L`. TO DO: reshape the template so the declaration rule is what decides — e.g. the spec writes `y` as the same projection off its own `x`, so `L` is not taken, and `spec-x = k` binds `K` to the member's `x` — measure again the controls of its doc (the once-only parameter replacement, the declaring sort's parameters kept out of a provision's open slots), and bless. ACCEPTANCE: most programs load or are refused by the declaration rule itself (IncompatibleMemberSignature at the rule's legs), each control fails its back-out by a named count, families green.

