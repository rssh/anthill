## Attributes

- id: WI-20261112-TRGTW-a-let-annotation-does-not
- created: 2026-11-12T05:12:30Z

- status: Open
- status_agent: claude
- status_at: 2026-11-12T05:12:30Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A `let` ANNOTATION DOES NOT INSTANTIATE AN OPERATION TAKEN AS A FUNCTION VALUE. PROGRAM: `operation idp[P](x: P) -> P = x` and `operation viaLet() -> Int64 = let h: (x: Int64) -> Int64 = idp  h(4)`. MEASURED on c7ad2ef0: refused "type mismatch in h.annotation (let-binding): expected Int64 -> Int64, got ?P -> ?P". TWINS, each runs: the same arrow at an argument slot, `applyInt(idp)` over `applyInt(f: (x: Int64) -> Int64) -> Int64 = f(4)` (4); a monomorphic operation, `let h: (x: Int64) -> Int64 = inc  h(4)` over `inc(x: Int64) -> Int64 = x + 1` (5); an annotated lambda, `let h: (x: Int64) -> Int64 = lambda (x: Int64) -> idp(x)  h(4)` (4). The projection twin from WI-20261104-KBZ4F, `let h: (x: MemStore) -> Int64 = g` over `g[P](x: P) -> P.Val requires Storage[C = P]`, is refused the same way ("got ?P -> Storage[C = ?P].Val"); `applyMem(g)` at the slot answers 7. MECHANISM, not traced past the first step: at the reference (`check_bare_ref`) `callable_at_slot` answers `Refused` against the annotation (traced for KBZ4F's `g`), so the value keeps its own `?P`; the `let`'s conformance (`types_compatible` in typing/build.rs, LetAfterValue) runs on a fresh σ and refuses `?P` against `Int64` — its probe unify runs only where the ANNOTATION has variables. At an argument slot the call's own unify binds `?P` first. EXPECTED: `viaLet` 4 and KBZ4F's `let` twin 7; `let h: (x: Int64) -> String = idp` refused naming the result. ACCEPTANCE: rows driven to their values with their refused twins; back-outs measured; full gate green.

