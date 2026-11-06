## Attributes

- id: WI-20261106-9G5K2-a-guarded-equation-whose
- created: 2026-11-06T09:25:23Z

- status: Open
- status_agent: user
- status_at: 2026-11-06T09:25:23Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a guarded equation whose SUBJECT names nothing loads clean: `rule r: baz(?a) = 0 :- g` with nothing declaring `baz` is a law no redex can ever be written for

## Changes

### 2026-11-06T09:25:54Z — feedback — user

FOUND BESIDE WI-20260825-6RRVA (bd8eebdf), from its /code-review. MEASURED on bd8eebdf: `import anthill.prelude.{Int64}` + `rule bodied2: baz(?a) = 0 :- Int64.gt(1, 0)` with nothing declaring `baz` loads clean (as does `bar(?a) = bar(?a) :- …`, which 6RRVA exempts as the subject repeated in its replacement). A bodyless `<=>` subject INTRODUCES a scoped name (`rule my_law: foo(?a, ?b) <=> foo(?b, ?a)` resolves `foo` to `<ns>.foo`); a guarded `=` subject stays a bare unresolved intern, so nothing declares it and no operation body can write a redex for it without the typer refusing the call as an unknown functor — the law is dead. The subject node is exempt from the head name check because a head introduces its functor (WI-896), which is true of `<=>` and not, it seems, of a guarded `=`. TO DECIDE: whether a guarded equation's subject introduces (and should then resolve as the `<=>` one does) or must name a declared operation (and is refused when it names nothing). A spec question first — kernel-language §5.3.

