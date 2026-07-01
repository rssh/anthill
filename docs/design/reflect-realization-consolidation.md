# Reflect realization consolidation — how far to share

## Status: Decided — **stop at shared helpers**. The interpreter and host-Rust bridge share ONE carrier-agnostic core (record readers + term reify/reflect walks) but stay two thin realizations. Do **not** drive them through a single impl object; the `Rc<RefCell>` rework that would require is high-cost, high-risk, and low-benefit now that drift is already eliminated.

## Tracks: WI-551 (part (a): shared record readers — delivered), WI-555 (shared term reify/reflect walks — delivered), WI-554 (gap (c): single impl object — **this note is its deliverable**)

## The question

`anthill.reflect.KB.*` has two realizations:

- the **interpreter** eval-time builtins — dynamically-typed `Value` cons-lists,
  registered over `&mut KnowledgeBase` (`anthill-stl/src/reflect/builtins.rs`
  for introspection; `anthill-core/src/eval/builtins.rs` for
  `execute`/`facts_of`/`unify`/term manipulation);
- the **host-Rust bridge** — `KbBridge` implementing the generated `KB` trait,
  producing statically-typed structs, over `Rc<RefCell<KnowledgeBase>>`
  (`anthill-stl/src/reflect/bridge.rs`).

They answer the same questions over the same KB facts. They had **drifted**
per-op (the WI-543 BigInt / WI-545 requires-ensures / WI-548 kb_operations
parity tax). WI-551 framed three levels of consolidation:

- **(a)** one shared **fact-walking / record-reading** core — *done* (`reader.rs`).
- **(b)** one shared **term reify/reflect walk** — *done* (WI-555, `reader.rs`
  `reify_walk` / `reflect_walk` + the `ReifyBuilder` / `ReflectReader` traits).
- **(c)** one shared **impl object** both realizations call — *this note*.

After (a) and (b), both realizations already call the exact same core; per-op
drift is structurally impossible. Gap (c) is the stronger, largely cosmetic
goal: collapse the two thin *realizations* themselves into one object.

## Decision in one paragraph

**Not worth it.** The parity risk that motivated WI-551 is already gone — (a)
and (b) share every walk, and the only per-realization code left is the
intrinsic output mapping (dynamically-typed `Value` vs static structs), which a
single impl object could not remove anyway. Achieving one impl object would cost
an invasive, hot-path-touching rework for aesthetics only, and one half of the
interpreter's reflect surface is walled off from `KbBridge` by the crate
dependency direction. So the shared-helper status quo is the correct stopping
point. Close WI-554 with this note.

## The three blockers, weighed against the status quo

### 1. KB ownership mismatch → an `Rc<RefCell>` rework on the eval hot path

`Interpreter { pub(crate) kb: KnowledgeBase }` owns the KB **by value**
(`kb_mut(&mut self) -> &mut KnowledgeBase`, `eval/mod.rs`). `KbBridge` holds
`Rc<RefCell<KnowledgeBase>>`. Driving the interpreter builtins through the
bridge requires unifying these, i.e. one of:

- **Move `Interpreter.kb` into `Rc<RefCell<KnowledgeBase>>`.** This ripples
  through `eval/mod.rs`, `eval/eval.rs`, `eval/pattern.rs`, `Frame`, and every
  builtin currently taking `&mut KnowledgeBase`. It adds a `RefCell` borrow on
  every KB access — including the evaluation hot path — with a new class of
  **runtime borrow-panic** failure mode (a builtin holding a `borrow()` while
  something re-enters `borrow_mut()`). This is exactly the re-entrancy hazard
  WI-555 *removed* from the bridge's own reify path; re-introducing it
  interpreter-wide is a regression in robustness, not an improvement.
- **Introduce a shared-core trait both call.** This already exists in the useful
  sense: the free functions in `reader.rs` take `&mut KnowledgeBase` and the
  bridge calls them via `&mut *self.kb.borrow_mut()`. There is no further shared
  object to extract without also unifying ownership (above).

Weighed against the status quo: the status quo pays *nothing* here (each side
uses its natural ownership), and the rework buys no correctness — only a single
`self` receiver in place of two entry points.

### 2. Crate-dependency wall → `KbBridge` cannot be the interpreter's impl object

The interpreter's reflect ops are **split across two crates**: introspection in
`anthill-stl/src/reflect/builtins.rs`, but `KB.execute` / `KB.facts_of` /
`unify` / `field_access` / `make_fn` / `find_fact` / … in
`anthill-core/src/eval/builtins.rs`. `KbBridge` lives in **anthill-stl**, and
the dependency runs `anthill-stl → anthill-core`, never the reverse. So the
anthill-core half of the interpreter's reflect surface **cannot** delegate to
`KbBridge` — a single impl object spanning both is architecturally impossible
without inverting the crate dependency (or hoisting `KbBridge` into
anthill-core, which drags the generated reflect types down with it). The shared
`reader.rs` helpers avoid this precisely because they are plain functions, not a
trait-impl object tied to a crate.

### 3. Output-type divergence is intrinsic

Even granting a single impl object, the interpreter must emit dynamically-typed
`Value` cons-lists and the bridge statically-typed structs — so a
per-realization mapping layer survives regardless. WI-555 already shared the
only part that *can* be shared (the structural walk); what remains is
irreducibly two-shaped.

## What "done" looks like

- Record readers: one `read_*` per op in `reader.rs`; each realization maps the
  neutral record to its output type. ✓ (WI-551a)
- Term reify/reflect: one `reify_walk` / `reflect_walk`; each realization
  supplies a builder/reader that reconciles the in-band name carrier. ✓ (WI-555)
- Impl object: **intentionally not unified** — see blockers 1–3. The two
  realizations remain thin mappers over the shared core.

If a future change *already* moves `Interpreter.kb` into `Rc<RefCell>` for an
unrelated reason (e.g. a shared-KB concurrency model), revisit gap (c) then —
the cost calculus flips only once that ownership rework is paid for elsewhere.
