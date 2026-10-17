## Attributes

- id: WI-20261017-T34HP-modify-framework-design-in-the
- created: 2026-10-17T07:37:17Z

- status: Open
- status_agent: user
- status_at: 2026-10-17T07:37:17Z

- acceptance: cargo-test

## Description

MODIFY FRAMEWORK — DESIGN, IN THE PROPOSALS FIRST: what identifies a resource at run time, and what a Modify handler is. No code. Decided with the user, then written into the proposals: revise proposal 037 (a Draft that 027, 036 and 047 cite as the canonical framework) and bring into agreement with it, or mark superseded, what disagrees — 027 §"Modify[T]" and its handler model, 027.1's handler contract (it still dispatches "on `Modify[T]`"), 036 §"Single-instance-per-functor limitation", 047 (Modify as State; §10's WI-200 and "State vs direct store access" questions) and 050.1 (§2's construction and fresh-result rules, §6's spec text). A change to kernel-language.md §5.6 or §5.7 is agreed with the user before it is written. Then docs/design/037-implementation.md, the realization: the four write paths today (`Cell.*` builtins straight to the arena, `ModifyRuntime.*` through the global handler, the Store mirror, the KB) and what each becomes.

Settles, in this order: (1) what identifies a resource at run time — the contradiction below; (2) what a handler is — the store behind references (037), the owner of state for a scope (047, WI-200's direction (c)), or nothing beyond mutation of the argument (every compiled target) — and the single door the user directed on 2026-10-16 (WI-20260908-9WVT7, note F10: every Modify through `ModifyRuntime`, `Cell.set` included, so time travel can intercept it); (3) allocation, and the run-time counterpart of the typer's masking; (4) installation and scope, which decides the shape of WI-078 (h); (5) whether a raise rolls back state — spec §5.7's `StateT Env (ExceptT Err …)` says yes at `Error.reify`, the runtime keeps the write (measured in WI-20260926-7D48J), 047 leaves its ranks undecided. Branch stays with WI-070.

THE WI-200 CONTRADICTION. Over `sort Box { provides Modifiable[T = Self]; entity box(id: Int64) }` and the pure `mk(n) = box(id: n)` (`eval_test::m5_modify_a_resource_with_fields_is_refused`), is `let a = mk(1); let b = mk(1)` one resource or two? Spec §5.6: two — two places are two resources. 050.1 §2 and §8: two and unconnected — each call's result is fresh, and a construction adds no region of its own. WI-200's fix as recorded on 2026-10-16: one — the handler receives only the value, so keeping `box(id: 1)` and `box(id: 2)` apart means keying by it. Then `operation demo() -> Unit = (let a = mk(1); put(a, 10))` loads pure (a let-bound local's write is dropped, the path WI-20261016-HE2J6 measured) and changes what `fetch(mk(1))` reads, and no row could name that write. Ways out: (A) a value of a modifiable sort names a slot, as a nullary constructor does — equal values are then one resource, a write through one is never masked or fresh, and one no row can name is refused (HE2J6's rule); (B) identity is minted by an allocating operation (050.1 §6 with Cell's model) — a constructed `box(id: n)` is data, not a resource, and the stopgap becomes a load error; (C) the place is the resource, as compiled code reads `Modify[r]` (`&mut r`). WI-200 implements the chosen rule and depends on this; WI-078 (h) waits on (4) without an edge, since the rest of WI-078 does not.

