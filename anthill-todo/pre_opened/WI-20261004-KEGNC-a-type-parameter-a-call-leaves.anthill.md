## Attributes

- id: WI-20261004-KEGNC-a-type-parameter-a-call-leaves
- created: 2026-10-04T08:10:58Z

- status: PreOpened
- status_agent: claude
- status_at: 2026-10-04T08:11:12Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261001-80ZV8-a-bare-parametric-sort-means

- tags: typing

## Description

A TYPE PARAMETER A CALL LEAVES UNFIXED IS AN INFERENCE VARIABLE OF THE BODY, SOLVED HINDLEY–MILNER STYLE — `Map.empty()` has a type BEFORE inference and one AFTER it; after inference what nothing solved becomes a rigid unknown, or an error. PROPOSED by the user 2026-10-04 (in the discussion of WI-20261001-80ZV8's decision 3); not to be started without a design pass.

THE PROGRAM.

  operation go() -> Int64 =
    let m = Map.empty()                -- nothing here says K or V
    let m2 = Map.put(m, "a", 1)        -- this does
    Map.size(m2)

  operation bad() -> Int64 =
    let v = LogVar.fresh()             -- nothing says T
    let _ = LogVar.bind(v, 1)          -- T is Int64
    takes_string(LogVar.read(v))       -- must be refused: T is Int64

TODAY (measured 2026-10-04, WI-20261001-80ZV8). A call that fixes a type parameter of its callee by none of bracket, arguments and expected type has three answers. An operation's OWN `[A]` is an error at the call (`expected a type for 'A', got unconstrained`). A parameter of the callee's SORT is left OPEN in the result (the user's "1 (a)" of 2026-10-03), which inside one expression lets the enclosing call say the rest (`put(empty(), "a", 1)`, `mplus(empty(), pure(1))`); bound to a name, the open slot was read by every use as that use liked (`let x = Box.fresh()`; `takes_int(x) + takes_str(x)` loaded), so 80ZV8's interim rule CLOSES it at the binding to the binder's own unknown (`x: Box[T = x.T]`, `closed_where_named`). A sibling call inside the sort takes the caller's instance. So `go` above is refused today at `Map.put(m, "a", 1)` (`expected m.K, got String`) until the author annotates the `let`, and `bad` is refused at `bind`.

THE PROPOSAL. The value has two types. BEFORE inference each parameter the call leaves unfixed is an INFERENCE VARIABLE of the enclosing body — `m: Map[K = ?K, V = ?V]` — monomorphic: not generalized, one type for every use. Uses unify it across the whole body, Hindley–Milner style (GLOBAL inference: a later statement solves an earlier `let`). AFTER inference each such variable is SOLVED — or, where the body never says, either TRANSFORMED INTO A RIGID VALUE (the unknown the interim rule already produces at the binding) or reported as an ERROR naming the binding to annotate. `go` loads with no annotation; `bad` is refused naming the two uses that disagree.

WHY IT IS A TICKET AND NOT A PATCH. It is ordinary unification — no new kind of constraint — but a binding must outlive the call that made it. Today each call's substitution is built at the call and dropped when the call is typed (`check_apply_iter`; `check_operation_bodies` records it: "no substitution is threaded through an operation body, so a binding made in one call cannot reach the lambda that owns the variable"). The one body-scoped variable the typer has is an un-annotated lambda binder (WI-20260904-50B2K), solved from the declaration at the return. So the work is one substitution threaded through a body: carried with the typing environment, read through wherever a bound name's type is read, merged where branches join (`if` / `match`), generalization left where it already is (a `let`-bound lambda, WI-1083's `PolyType`), and a closing pass at the end of the body. The interim rule is forward-compatible: every program it admits this admits.

TO DECIDE WITH THE USER BEFORE IMPLEMENTING. (1) For a variable the body never solves: rigid or error — and whether a parameter the sort declares COVARIANT may instead be the bottom type (`let xs = nil` then never extended). (2) Whether an operation's own `[A]` follows the same rule (today an error at the call). (3) What an unplaced SIBLING call inside the sort does (today: the caller's instance — 80ZV8's decision 3; `Self.f()` is not accepted as a receiver). (4) Whether a variable is solved only by later statements of the same body, or also through a closure that captures the value. (5) The order of reporting when two uses disagree: which one is "the" mismatch.

ACCEPTANCE. Each row runs or names its refusal, with its control. `let m = Map.empty()` followed by `put(m, "a", 1)` loads and runs with no annotation. `let v = fresh()` bound at `Int64` and read at `String` is refused naming both uses. A variable no use solves takes the decided closing. The rows of `wi_80zv8_*` that pin "annotate the let" flip, and no program that loads before the change is refused after it. Full workspace green via `rustland/scripts/test.sh`; scaland parity stated (its generator reads no inferred types today).

## Changes

### 2026-10-04T10:51:32Z — feedback — claude

MEASURED 2026-10-04 while building WI-20261001-80ZV8's interim rule (a value's open slot is closed where the value gets a name), for this ticket's scope. (1) An un-annotated lambda binder bound to an open argument is read at two instances inside the lambda: `let f = lambda (b) -> Bag.size(Bag.add(b, 1)) + Bag.size(Bag.add(b, "s"))` then `f(Bag.empty())` loads. The interim rule does not reach it — a flexible variable with a name is not an open slot. (2) The literal `[]` carries an inert `type_var` of its own (WI-20260904-50B2K left it on purpose, as the closest thing to a forall the typer has), which a name does not close: `let xs = []` is read at two element types, while `let xs = nil` is closed to `xs.T`. One value, two spellings, two verdicts — pinned by `wi_80zv8_named_open_slot_test a_named_nil_is_closed_and_a_named_literal_keeps_its_variable`. (3) The branch join already takes what the other branch SAYS for an open slot (`open_slots_said_by`, typing/subtype.rs), binding nothing; under this ticket that becomes unification of the two branches' variables, and the function goes. (4) A named function's result is deliberately not closed by the interim rule (`SlotPosition::Named`): `let mk = lambda (n: Int64) -> Bag.empty()` stays a function to an open bag. Under inference that is generalization at a let-bound lambda, which WI-1083's PolyType already owns. PUT TO THE USER with the interim rule and not decided: a slot in a COVARIANT position stays open at a name (the relaxed value restriction), which would keep `let xs = nil` any list and align it with `[]`; it is point (1) of this ticket's list to decide.

### 2026-10-04T11:48:05Z — feedback — claude

DECIDED by the user 2026-10-04, after the note above ("agree with variant 5"), and implemented under WI-20261001-80ZV8: at a name, an open slot in a COVARIANT position is the bottom type `Nothing` — `let xs = nil` and `let xs = []` are `List[T = Nothing]` — and elsewhere the name's own unknown. So point (1) of this ticket's list is answered for the covariant case: a variable the body never solves is `Nothing` where its position is covariant; for any other position it is still to decide (rigid, as the interim rule has it, or an error). The empty literal's wildcard is now read as an open slot, so note (2) above no longer holds: `nil` and `[]` named agree. Note (1), the un-annotated lambda binder, stands. NEW for this ticket's scope, measured: a SORT's parameter is bound by the first argument that names it, so over `let acc = nil`, `List.append(acc, [1])` is refused (`expected List[T = nothing], got List[T = Int64]`) where `List.append([1], acc)` loads; an operation's own `[A]` joins its arguments (WI-20260926-NEKR0). Body-wide inference would solve `acc` at `Int64` and remove the order; short of it, giving a sort's parameter the same join is a question put to the user.

