## Attributes

- id: WI-20260823-SPGBP-wire-the-reflect-kb
- created: 2026-08-23T11:49:58Z

- status: Open
- status_agent: claude
- status_at: 2026-08-23T11:49:58Z

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

### What it does NOT buy, so the next reader does not assume it

A layer stops the candidate RETARGETING a trusted symbol: a goal in trusted code still
resolves to the symbol it always did. It does NOT stop the candidate adding a CLAUSE
under that same trusted symbol — a source writing `fact guardians.Checked(…)` lands a
row a trusted goal asking `Checked(?c, ?s)` will see. Measured on the guardians example:
two spellings that its Rust-side namespace gate lets through do exactly that. A gate
over DECLARED names is still required, and is a separate ticket.
