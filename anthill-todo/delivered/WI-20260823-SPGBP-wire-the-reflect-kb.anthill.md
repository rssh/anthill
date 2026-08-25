## Attributes

- id: WI-20260823-SPGBP-wire-the-reflect-kb
- created: 2026-08-23T11:49:58Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-25T11:26:23Z

- acceptance: cargo-test, scaland-sbt-test

- tags: anthill-side-check

## Description

Wire the reflect KB introspection surface into the runtime — it is DECLARED, IMPLEMENTED and DEAD. `anthill-stl/src/reflect/builtins.rs`'s `register_reflect_builtins` has ZERO callers outside its own tests (grep across every crate), so in the CLI, `anthill run`, and every embedder built on `runner::register_runtime`, the whole `anthill.reflect.KB.*` surface resolves to nothing: `sorts`, `operations`, `constructors`, `fields`, `rules`, `descriptions`, `sort_template`, `reify`/`reflect`, `Substitution.apply`/`compose`/`bindings`, and the namespace-level `qualified_name`, `short_name`, `lookup_symbol`, `kind`, `scope`, `sort_as_term`, `term_as_sort`, `can_be_sort`. Only the subset `anthill-core`'s `register_standard_builtins` binds (`KB.kb`, `KB.execute`, `KB.facts_of`, `KB.stored_facts_of`, the term ops) is live. Consequence: an anthill program cannot introspect the KB it runs in, which is the floor under every anthill-side checker/linter/migration — including the guardians example's ask that the ESSENCE of a check live in anthill rather than in a Rust host fn. FIX: call `register_reflect_builtins` from `runner::register_runtime` (anthill-stl), after `register_standard_builtins`. MEASURED SAFE: the two registries' actual `register_if_present` sets are DISJOINT today — 23 stl QNs, no overlap with core's — so LAST-WINS shadowing has nothing to shadow. The one historical hazard is already handled: WI-759 removed `anthill.reflect.field_access` from this module precisely because registering it would silently replace core's live implementation with a declared-but-broken shape; its comment says the arrangement 'was harmless only because nothing but this file's own tests ever called register_reflect_builtins', which is the condition this ticket ends — so re-audit for a NEW collision as part of the change and add a disjointness assertion so the next added builtin cannot reintroduce one silently. ACCEPTANCE: an anthill program run through the ordinary CLI path calls `KB.sorts(kb(), none())` and gets a non-empty list, and `qualified_name` on a symbol answers; both fail with UnknownOperation when the wiring is backed out. A test asserts the two registries stay disjoint. Full workspace green via rustland/scripts/test.sh.


### The `kb` parameter is a sentinel, and that is the same job

Wiring the dead registry up is half of one change, not a change of its own. Every
`kb`-taking builtin `anthill-core` DOES bind ignores its `kb` argument and uses
`interp.kb` — `kb_execute`, `kb_facts_of`, `kb_stored_facts_of` all destructure it as
`_kb_arg`, and `kb_execute`'s own doc says so outright:

> The KB argument is a sentinel — `Value::Unit` or any placeholder — because the
> evaluator has no first-class KB values and always uses the interpreter's own KB.

`kb()` returns a zero-field entity. So the declared surface promises a parameter that
means nothing, and registering the rest of the surface would extend that promise rather
than keep it. Making the parameter REAL is the change; the registration comes along.

### The form, settled with the user

Keep `execute(kb: KB, query: LogicalQuery) -> Stream[Solution]` exactly as declared, and
let a scoped load produce a `KB` value:

```anthill
execute(loaded(sources), pattern_query(...))
```

Four things fall out, and each was a question that had no good answer under the
alternatives considered (a bracket operation; a separate KB; a goal passed as a name):

* **The goal stays a logical term.** `LogicalQuery` already exists (010 / 026.1) and
  `execute` already runs it. Nothing new is invented for the goal.
* **Discard is dropping the value.** No enter/pop pair to get wrong, and no way to
  forget the pop.
* **The caller's functors keep meaning what they meant.** The produced KB is a LAYER
  over the caller's, sharing its term store and symbol table — which is exactly what
  makes a goal written at the call site legal in it. A goal is an arbitrary logical
  term, and its symbols are the caller's; a separate KB with its own tables would make
  that term meaningless and force the goal to be a NAME resolved on the far side, which
  is the short-name identity matching WI-672 / WI-897 removed.
* **A lazy `Stream[Solution]` cannot outlive its scope**, because it holds the KB value
  it was made from. A bracket form would have had exactly that bug: `execute` returns a
  `StreamSource::Resolver` pumped later by `splitFirst`, so a scope popped at the
  bracket's exit would leave the stream resolving against a base that is gone.

### THE HALF THAT WILL BITE: scope the DEFINITIONS, not just the clauses

Dropping a layer must make a name the load introduced UNRESOLVABLE again, not merely
clause-less. The clause side is the visible half — `rules`, `rules_by_functor`,
`by_domain`, `rules_by_label`, the discrimination index. The half that decides
soundness is what a DECLARATION writes: `SymbolTable::define`, the entity-field
registries (`register_entity_fields`, under BOTH the resolved and bare-interned keys),
`op_records` signatures, the provider/requires indexes. Layer only the clauses and a
discarded load leaves resolvable names behind, with nothing reporting it — a partial
discard is worse than none, because the safety claim reads as total.

`imbl` is already a dependency and already backs `Substitution` (WI-569, `Clone` is O(1)
structural sharing) and the eval map arena, so the persistent-layer discipline exists;
this extends it to the definition side. The clause store is NOT persistent today
(`rules: Vec<RuleEntry>`, `HashMap` indexes), so that is real work rather than a
re-typing.

Deliver in that order — definitions first (the part that can be silently wrong), clauses
second, the `kb` parameter made real third, the dead registry along with it.

### MEASURED: snapshot, not persistent structures

The ticket left "persistent-vs-high-water-mark" open and said to measure it. Measured on
a debug build, `load_stdlib_and_stl` (the whole stdlib plus the Rust host bindings):

```
LOAD                                                       1722.6 ms
  defs 3618 · by_qualified_name 2692 · scopes 722 (locals 2675,
  imports 395, parents 609, type_params 195)
  entity_fields 502 · op_records 376 · sort_info 226 · rules 2876
  fact_dedup 2633 · terms 17305

clone(rules_by_functor + by_domain + rules_by_label + fact_dedup)  0.121 ms
clone(discrim — ALREADY Rc-COW, WI-537's Γ overlay)                0.037 ms
clone(op_records)                                                  0.273 ms
clone(entity_fields + entity_field_types)                          0.211 ms
clone(by_qualified_name + scopes)                                  2.036 ms
                                                            total ≈ 2.7 ms
```

A FULL deep clone of everything a layer must scope is **2.7 ms against a 1722 ms load —
0.16%**, in debug. So the choice is settled in the direction the ticket did not assume:
**snapshot/restore, and no conversion of the KB's maps to `imbl`.** Retyping ~50 hot-path
`HashMap`s as HAMTs would tax every load and every resolution to save 2.7 ms on an
operation invoked once per `loaded(…)` — and one whose own cost (parse + load of the
scoped sources) is orders of magnitude larger. `discrim` needs nothing at all: it is
already `Rc`-COW, and clones in 37 µs.

### The consequence: ONE KB, monotone interners, LIFO layers

Snapshot/restore means the layer is applied to the interpreter's own KB in place, so:

* **The interners are NOT snapshotted** — `TermStore`, `SymbolTable::defs`,
  `SymbolTable::intern_map`, `next_var`. That is what makes the escape hatch sound: a
  `TermId` or `Symbol` minted inside the layer and carried out by a `Solution` still
  NAMES something after the discard. What a discard removes is RESOLVABILITY (the
  name→symbol relation), which is exactly the ticket's own statement of the rule. The
  price is a leak, not a fault: the layer's terms keep their refcounts.
* **Layers unwind innermost-first, by DEFERRAL rather than refusal.** A retired outer
  layer whose inner one is still held simply waits, and that is correct rather than
  tolerated: the inner layer's snapshot was taken WITH the outer one applied, so
  unwinding in any other order would install a state that never existed.
* **One index needs more than a monotone interner: `RuleId`.** It is the only index the
  KB hands OUT (`stored_facts_of` mints a `FactRef` over it) and `rules` is scoped, so a
  plain restore shortens the vector and the next assert aliases a slot a caller still
  holds. The layer's slots are kept as TOMBSTONES — the same `retracted: true` state
  `retract` produces — so a stale reference finds a retracted row, not a live wrong one.

### Exhaustive-by-construction, so a new field cannot be silently unscoped

The snapshot is written as an exhaustive DESTRUCTURING of `&KnowledgeBase` and
`&SymbolTable`. A field added later fails to compile until its author says which half it
is in — scoped or monotone-with-a-reason. This is the structural answer to "the part that
can be silently wrong": there is no `..` rest-pattern to hide behind.

### What it does NOT buy, so the next reader does not assume it

A layer stops the candidate RETARGETING a trusted symbol: a goal in trusted code still
resolves to the symbol it always did. It does NOT stop the candidate adding a CLAUSE
under that same trusted symbol — a source writing `fact guardians.Checked(…)` lands a
row a trusted goal asking `Checked(?c, ?s)` will see. Measured on the guardians example:
two spellings that its Rust-side namespace gate lets through do exactly that. A gate
over DECLARED names is still required, and is a separate ticket.

### DELIVERED — what landed, in the ticket's own order

**1. Definitions.** `intern::SymbolScopeSnapshot` + `SymbolTable::snapshot_scoped` /
`restore_scoped`. The scope tables (`by_qualified_name`, `scopes`, `internal_syms`, the
two import-origin maps, the ambient asking-file cursor) are scoped. `defs` is restored
over its SNAPSHOT-LENGTH PREFIX only — so a kind a layer added to a base symbol is undone,
while a symbol the layer MINTED stays nameable. `intern_map` is monotone: roll it back and
the next intern of a string the layer already interned mints a SECOND symbol for one name,
and structurally identical terms stop unifying.

`extent::ExtentScopeSnapshot` splits the same way: the mount tables (`mounts`, `profiles`,
`mirror_of`, `mirror_monotonicity`) are scoped, the live `Box<dyn ExtentSource>` /
`Box<dyn Store>` slabs are monotone.

**2. Clauses.** `kb::layer::KbScopedSnapshot` + `KnowledgeBase::snapshot_scoped` /
`restore_scoped`, covering the clause store, every index, the discrimination tree, the
declaration registries, the derived typing indexes and every memo cache. THE MEMOS ARE
SCOPED DELIBERATELY: each holds an answer computed UNDER the layer's declarations, so
leaving one behind serves a layer's dispatch decision to the base after the discard — the
"resolvable name left behind" failure in a different hat.

**3. The `kb` parameter, made real.** `Value::Kb(KbHandle)`, an arena
(`eval::layer_arena`) and `KB.loaded(sources: List[String]) -> KB effects Error`.
`kb_execute` no longer destructures its first argument as `_kb_arg`: a `Value::Kb` is
RETAINED by the lazy stream (`StreamSource::Resolver { search, layer }`), which is the
whole of why the ticket wanted a VALUE. `kb()` still means the ambient KB.

**4. The dead registry.** `runner::register_runtime` now calls
`register_reflect_builtins` after the standard set, and
`the_two_builtin_registries_are_disjoint` measures the two key sets against each other so
a newly added builtin that collides fails by NAME instead of silently shadowing.

### Two consequences a reader must not be surprised by

**A layer is dynamically scoped, and layers compose in creation order.** Snapshot/restore
is IN PLACE, so while a layer is applied `kb()` and the layer value denote the same KB:
`KB.sorts(kb(), …)` between `loaded(srcs)` and `execute(…)` sees the layer's sorts. It
over-reports and can never make the base LOSE anything, but it is not the "two independent
KB values" a reader might assume. Two live layers means the second sees the first.

Making `kb()` denote the base while a layer is live needs a genuinely SEPARATE layered KB
object — which costs the interner sharing that makes a caller's goal legal in the layer at
all, the property this ticket chose the layer form to get. That is the trade, and it is
open to revisiting.

**Discard is at a sweep point, not at the drop.** Restoring needs
`&mut KnowledgeBase`, which `Drop` cannot reach, so a release only RETIRES the slot and
`Interpreter::sweep_layers` — one `Cell` read per trampoline iteration — does the work. A
HOST driving `call` directly must call it itself. A retired layer under a still-held inner
one waits, and that is correct rather than merely tolerated: the inner layer's snapshot was
taken WITH the outer one applied.

### REVIEW — what a second pass found, and why two of them mattered

`/code-review` at high effort returned 8 findings against the finished change; all 8 held
up when checked against the code. Two were soundness:

**`effects Error` was decorative.** `KB.loaded` built `EvalError::Raised` directly instead
of routing through `Interpreter::raise_error`, which is what invokes an installed handler.
A checker writing `handle execute(loaded(candidate), q) with Error raise(e) -> report(e)`
would never see its handler fire — while this ticket's own comments claimed the
diagnostics were "the answer a checker reports". That is verbatim the WI-467 / WI-610
defect ("a bespoke `EvalError` the declared `effects Error` could never catch"). Now a
declared `anthill.reflect.LoadFailed.load_failed(diagnostics: List[T = String])` payload
through `raise_error_payload`, so a handler can DESTRUCTURE it too — a bare `Value::Str`
gives a handler nothing to match on.

It lives in `anthill.reflect`, NOT beside the other `Error` payloads in
`prelude/effects.anthill`, and scaland is what asked the question: adding it to the
prelude moved `BootstrapTest`'s emitted-sibling list and its standalone-compile floor.
The emitter was right to notice. The rule the existing payloads follow is that one lives
WITH THE THING THAT RAISES IT — `DivisionByZero` with prelude arithmetic, `EmptyStream`
with prelude `Stream`, `RelationFloundered` with the prelude `Relation` face — and nothing
outside reflect can raise this one. Moving it is the rule applied, not the test appeased;
the prelude closure is then untouched and needs no expectation edited.

**The monotone-interner argument ran in ONE direction only.** The reasoning above is all
about ids ESCAPING a layer. An id can also RE-ENTER. `rules` IS rolled back, so a base row
retracted while the layer is live — head to refcount 0, slot freed to the free list,
reissued to one of the layer's own terms — is reinstated by the discard still naming that
slot. Silently a different fact, or a panic on a freed slot. `TermStore::release` is now a
NO-OP while a layer is applied: not even the refcount moves, because a slot left at zero
would be freed by the next release after the pin lifts and resurrect the same defect one
step later.

The other six: `execute` pinned the layer NAMED by its argument rather than the scope the
search actually reads (so `execute(kb(), q)` under a live layer pinned nothing at all) —
now the INNERMOST layer, which pins the whole stack since layers unwind innermost-first;
the `List[String]` read was neither carrier-agnostic nor actually strict; `const_cache
.clear()` wiped in-flight `Forcing` sentinels and so disabled const-cycle detection during
a layer operation; and a comment of mine described a test setup the test did not use.

The one-symbol registration gate was MEASURED rather than changed: 14 of the 17 symbols
`ReflectSyms::resolve` requires are declared in the same file as `SortInfo`, and the other
three are prelude names `reflect.anthill` imports and cannot load without — so the partial
stdlib that would slip past the gate cannot load in the first place. Recorded at the gate.

**And one the fix itself introduced, which the tests caught immediately.** Making the list
read strict meant RECOGNISING the `nil` terminator rather than just stopping at it — and
`nil` is a NULLARY constructor, which `functor_view_head` canonicalizes to the bare
`ViewHead::Ref` (WI-436 / WI-511). A `ViewHead::Functor`-only match therefore saw every
list as unterminated. `ViewHead::functor_sym` is the reader that spans both spellings.
`value_list_elements` never met this because it only ever `break`s on a non-`cons`.

