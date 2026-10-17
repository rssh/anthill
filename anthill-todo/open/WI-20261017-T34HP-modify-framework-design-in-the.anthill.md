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

## Changes

### 2026-10-17T09:06:06Z — feedback — claude

DECISION 1 (user, 2026-10-17) — WHAT IDENTIFIES A RESOURCE, AND WHAT A HANDLER IS. Reached in discussion; it supersedes the description's "Ways out" (A)/(B)/(C), which framed the question around the generic `ModifyRuntime`.

(1) IDENTITY belongs to the language, per base sort; a handler never chooses it (037 §1's "identity is a property of the handler" goes; Rule 6 stays). A base sort with an allocating operation (`new`, `effects Modify[result]`) is ALLOCATED: each call makes a fresh resource, and its values come only from `new` (a public constructor beside it is refused). One without is KEYED by its values, which name something outside (a store's root and convention, a device, a mailbox's owner): equal values are one resource, the key provides total `Eq` as `Map`'s keys do, and identity follows `Eq`, not the canonical printing the Store mirror keys by today.

(2) BASE AND SECONDARY. A base modifiable sort holds its state outside every anthill value, and only its own operations change it (today Cell, KB and the Store family; ExecutionEnvironment, the webots devices and guardians' Mailbox are declared only). A secondary sort (MutableStack) is written in anthill over the base resources it holds: it has no identity of its own (two values are one resource exactly when they hold the same base resources), it is modifiable by containment (`region::type_admits_modify`), and an `internal` constructor keeps its invariants (WI-369). Map and Substitution are persistent values, not resources.

(3) NO GENERIC `ModifyRuntime` SPEC. One with operations forces Cell's on every sort; one without says what the base `Modifiable` claim says. A base sort's runtime is its own state operations: the mutating ones, the reads and the allocation.

(4) A HANDLER IS AN IMPLEMENTATION OF A BASE MODIFIABLE SORT, one per handler. The default is today's host realization (`provides S language rust { operation_map … }`, proposal 038, held to the declarations by WI-20260922-BRT4Y), generalized from one realization per language at build time to one per installation at run time. A handler that owns the state answers the reads too; allocation (minting the identity, storing the initial value) is the implementation's.

(5) THE FRAMEWORK knows two things: which sorts are base, read from declarations at load; and dispatch — a call to a base sort's operation goes to the implementation installed for it, the single door the user directed (WI-20260908-9WVT7 note F10), so a handler sees every write. `Modifiable` stays a marker spec, with no dictionary.

(6) CONSEQUENCES FOR THE CODE. The stdlib's `ModifyRuntime` (fixed `get`/`set`) and Cell's `provides ModifyRuntime[T = Self, V = V]` go, and so does `default_modify_handler`'s functor map, which only served sorts with no operations of their own (`Box` and `counter` in the m5 fixtures, which become load refusals). WI-200's goal, two boxes kept apart by the generic handler, has no counterpart, since nothing writes a Box; its scope follows from this ticket.

CORRECTION TO THE DESCRIPTION: on 2026-10-16 the user decided only "refuse" (F1 in d4f93591); "the language admits `Modify[b]` on such a place, and a handler that keeps instances apart" was that session's gloss, restating WI-200's May acceptance.

OPEN, for the later decisions: the type system's additions (an implementation written in anthill, checked against the sort's operation signatures; possibly a name for a sort's interface); what answers an allocation when no implementation is installed (rule bodies; the run-time side of masking); how and where an implementation is installed (WI-078 (h)); whether a raise rolls back state; Branch (WI-070).

