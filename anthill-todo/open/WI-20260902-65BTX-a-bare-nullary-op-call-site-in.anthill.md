## Attributes

- id: WI-20260902-65BTX-a-bare-nullary-op-call-site-in
- created: 2026-09-02T09:31:36Z

- status: Open
- status_agent: claude
- status_at: 2026-09-02T09:31:36Z

- acceptance: cargo-test

## Description

A BARE NULLARY OP CALL SITE IN AN OPERATION BODY IS NOT A REDEX, so a `[simp]` law
reaches `tau()` and not `tau` — the one half of WI-20260902-CZJ2N's step D it did not take.

MEASURED on CZJ2N's delivered tree:
  namespace zz.d
    operation tau() -> Int64
    rule tau() <=> 7 [simp]              -- and `rule tau <=> 7 [simp]`: both define now
    operation drive(n: Int64)  = tau()   -- 7
    operation drive2(n: Int64) = tau     -- residual: unify(?_, drive2(0))
  end
CZJ2N closed the HEAD side (the two head spellings are one term and one law) and left the
CALL SITE. A bare name in an operation body lowers to `Expr::VarRef`, and
`simp_rewrite::is_rewritable` (rustland/anthill-core/src/kb/simp_rewrite.rs:490) lists the
node kinds the rewriter descends into — `VarRef` is not among them — so the redex the law
matches never appears.

IT IS NOT THE SAME MECHANISM AS THE HEAD, which is why CZJ2N declined it rather than
folding it in. The head is a TERM and the canon settles it at the store. A call site is an
OCCURRENCE, and which reading it takes is TYPE-DIRECTED: §5.4 gives a bare nullary op two
candidate readings — the eta lift (an arrow-typed slot) and the zero-arg call — and only
`typing::check_bare_ref` (typing.rs:6607) has the `expected` type that separates them. It
already gives the bare name the zero-arg-call TYPE; what it does not do is ELABORATE the
occurrence into the `Apply` node `tau()` produces. CZJ2N's rule-body twin
(`Loader::nullary_op_call_or_ref`) could be written at the loader precisely because a rule
body has no arrow slots to respect.

WHY IT IS A SEPARATE TICKET rather than a line in that one: the change is in the typer and
its population is EVERY bare nullary operation reference in EVERY operation body — the
stdlib's `Additive.zero`, `Multiplicative.one`, `BoundedLattice.top`/`bottom`, `Map.empty`,
`Int64.minValue`/`maxValue`, and the `smoke.eta_nullary` / `wi698` eta fixtures that exist
to pin the OTHER reading. CZJ2N's own census found those, and none of them is a rule body.

TWO CANDIDATE FIXES, in the order WI-20260902-CZJ2N's plan preferred them:
 1. ELABORATE at `check_bare_ref`'s zero-arg-call arm — return the same `Expr::Apply`
    occurrence `tau()` builds, so `[simp]`, eval and codegen see ONE shape. This is the
    property to deliver and the one that makes the eta/call split explicit at the site that
    already decides it.
 2. Fallback if that elaboration is not local: teach `simp_rewrite::is_rewritable` and the
    firer that a `VarRef` of a nullary operation IS the redex `op()`. Cheaper, but it puts
    the rule in the rewriter instead of at the reading, so eval and codegen keep the other
    shape — `op_info::is_nullary_operation` (added by CZJ2N as the one owner of "is this
    name a call") would then have a fourth reader that the first three do not share.

ACCEPTANCE: `operation drive2(n) = tau` beside `drive(n) = tau()` under `rule tau() <=> 7
[simp]` answers 7 from BOTH, driven through eval. The eta rows must stay green and be named
as controls: `wi698_row_param_refinement_test::nullary_eta_lift_round_trips_through_eval`
(a nullary op passed by NAME into a `() -> Int64` slot must stay an `OpRef`, not become a
call) and `::nullary_returning_function_prefers_return_type_reading`. Say at the site which
rows a back-out fails. Both implementations if scaland can drive it (it has no typer, so
probably rustland only — say so rather than leaving it open). Update kernel-language.md
§5.3, whose sentence CZJ2N wrote to state exactly this boundary: "a bare `tau` call site
inside an operation body is a `var_ref` and is still not a redex, which is §5.4's
type-directed reading and a different question from the head's".

