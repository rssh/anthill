## Attributes

- id: WI-20260929-PFAGY-a-two-hop-chain-to-a-type
- created: 2026-09-29T20:16:20Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-05T10:39:38Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A TWO-HOP σ CHAIN TO A TYPE HOLDING A VALUE IS READ AS UNBOUND, SO A CALL WHOSE REQUIREMENT NOTHING SUPPLIES LOADS CLEAN AND DIES AT RUN TIME WHERE ITS TYPED TWIN IS REFUSED. `sort User { sort S = ?; sort U = ?; requires Store[State = S]; operation mkS() -> Option[T = S] = none(); operation go13(o: Option[T = U], u: U, s: S) -> Int64 = Store.peek(s) }`, providers only at `Buf[T = Int64, N = 4]` and `Buf[T = String, N = Bool]`, and `run(b: Buf[T = Int64, N = 3], c: Buf[T = String, N = Bool]) = User.go13(User.mkS(), b, b)`: loads, and `anthill run` fails "DeferToRequirement: requirement param `__req_store` not bound in caller frame"; the typed twin (`N = Bool` against providers at `N = String` / `Buf[T = String, N = Bool]`) is refused at load. MEASURED before and after WI-20260929-WBHTM. MECHANISM: `mkS()` leaks `S` into `go13`'s `U`, so σ holds `S ↦ U ↦ Buf[…, N = 3]`; the callee-supply substitution reads σ one hop and keeps `S` abstract, and `sigma_class_terminal` (typing/dep_projection.rs ~587) chases only `Value::Term` bindings, so it reads `U`, bound to an occurrence-carried type, as an UNBOUND root `(U, false)`; `drop_unpinned_demand_keys` (dict.rs ~2592) then drops the key as "the call says nothing about it" and route 4 discharges the requirement with no dictionary. The one-hop shape (`S ↦ Buf[…]`) no longer reaches it since WBHTM, whose supply lowers first. FIX: in `sigma_class_terminal`, a non-`Term` binding ends the chase as CONCRETE (no σ-class), not as an unbound root; or resolve the chain before the σ-class readers. FOUND by WI-20260929-WBHTM's /code-review (V11). ACCEPTANCE: the value program refused at load as its typed twin is; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-10-05T10:39:00Z — feedback — claude

DELIVERED by WI-20260929-020TH and WI-20260929-JN09W together. REPRODUCED on the parent: the value program loaded and died "DeferToRequirement: requirement param __req_store not bound in caller frame"; the typed twin was refused naming `Store[State = User.S]`. The ticket's second FIX is what was done — the chain is resolved before the sigma-class readers: `spec_param_binding_term` reads the binding at the end of sigma's chain on every carrier (020TH), so the requirement is `Store[State = Buf[T = Int64, N = 3]]`, concrete, and `sigma_class_terminal` is no longer asked about it. Read that way the requirement PINS the carrier, and route 4's gate then keeps the unrelated `c: Buf[T = String, N = Bool]` from answering for it (JN09W). Both spellings are refused at load naming the requirement at `b`'s type: wi_jn09w_holder_gate_test `a_sort_level_requirement_through_the_chain_is_not_held_by_another_buf` (fails with either part backed out). NOT DONE: `sigma_class_terminal` still reads a binding that is not a term as an unbound variable; no program was found that still reaches it. GATE as WI-20260929-020TH's, one tree: rustland 8560 / 0 / 14, scaland 599.

