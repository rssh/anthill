## Attributes

- id: WI-20260921-R10KC-decide-whether-a-requirement
- created: 2026-09-21T15:25:33Z

- status: Open
- status_agent: user
- status_at: 2026-09-21T15:25:33Z

- acceptance: cargo-test

## Description

DECIDE WHETHER A REQUIREMENT DICTIONARY MAY BE STORED IN A VALUE, so an operation reached by VALUE can read a NAMED requirement slot that no type at the site names. Today a value carries its sort and none of its type parameters: `resolve_bridge_requirements` re-resolves the chain from the argument values, the slot's goal is SEARCHED rather than read back, and because more than one provider could have answered it must REFUSE (`NamedSlotNotCarried`) rather than re-decide a question the construction site already decided. The refusal is CORRECT while it stands; what is missing is the decision, recorded.

THE TEST ALREADY EXISTS AND THIS TICKET IS ITS INVERSION: `wi456_sorted_set_collection_test.rs::a_default_body_reading_the_slot_by_value_is_refused_naming_it` (line 328). `Pick` is a spec whose DEFAULT body `twice(c, x) = keepLeast(keepLeast(c, x), x)` redispatches its own member on `c: C`, the abstract carrier; `Tagged` is a carrier with `requires O: WeakOrd[T]` whose `keepLeast` reads the slot through `WeakOrd.compare`. Two rows, and they differ only in the route: `Driver.direct` calls `Pick.keepLeast` - one hop, the typer reads `O = ByLength` off the type - and ANSWERS 1; `Driver.byValue` calls `Pick.twice` and is REFUSED naming the slot. It asserts on `NAMED requirement slot` and `cannot be recovered`.

RE-MEASURED INDEPENDENTLY 2026-09-21, ~70 lines through the CLI rather than the harness, to check the shape is the language's and not that fixture's (scratchpad `valuedict.anthill`, reconstructible from this paragraph). `MySet` is an ordered carrier whose `contains` reads the slot; `Searchable` is a spec whose default `containsAny(c, xs)` redispatches the member `contains(c, h)` on `c: C`. `anthill load` is CLEAN (4054 facts, 432 rules) and `anthill run` dies two frames below the call:

  error: cannot dispatch `anthill.prelude.WeakOrd.compare`: the requirement it reads pins no
  provider - `anthill.prelude.WeakOrd` fills a NAMED requirement slot of the carrier, and this
  operation was reached by dispatching on a VALUE, which carries its sort but none of its type
  parameters - so the provider the value's construction chose for the slot cannot be recovered
  here, and more than one could have been.

AND IT CARRIES THE CONTROL THE COMMITTED TEST DOES NOT, which is why the paragraph above is here rather than deleted as a duplicate. The committed `direct` row proves the typed call RUNS; it does not prove the comparator DECIDED, because `"a" < "zz"` under `ByLength` and under `Alphabetical` alike - one answer would be produced either way. Measured on the probe, the same typed call splits: `MySet.contains(s, "aa")` on `s = {"zz"}` answers YES under `O = ByLength` (one equivalence class under a coarse comparator) and NO under `O = Alphabetical`. Two rival `WeakOrd[String]` are in scope throughout, so no arm is explained by there being one thing to pick. THAT SPLIT IS THIS TICKET'S ACCEPTANCE SHAPE, and adding it to the committed test is the first step of the work rather than a separate cleanup.

NOT A TYPE-SAFETY QUESTION, and an earlier framing of mine that implied it was is wrong: a comparator can be a type PARAMETER and a stored witness at the same time - `std::set<T, Compare>` does exactly that, keeping two differently-ordered sets distinct TYPES while the container holds an instance. The coherence obligation (the stored dictionary agrees with the type parameter) is CONSTRUCTOR-enforced, not a soundness hole. `anthill.realization.runtime.Dictionary` is ALREADY a first-class value (`alloc_dictionary`, layout-checked against `dict_layout`), so the carrier exists; what does not exist is a decision to put one in a sort's fields.

WHAT ACTUALLY STANDS IN THE WAY is representation and reach, and a design must answer all five - each is a cost, none is an impossibility:
 - WHERE IT LIVES. `SortedSet.tip` is nullary, so an empty set has nowhere to put one; `bin` IS the set, with no root wrapper, so a per-node field duplicates it n times. A root wrapper is a change to every producer and consumer of the type.
 - EQUALITY. `eq` is extensional (WI-456) and would have to EXCLUDE the field, or two sets built through different-but-equal witnesses stop being `=`.
 - INDEXING. The discrimination tree keys on structure, so an embedded dictionary joins the indexed term and changes what matches what.
 - SMT. Terms are data there; a dictionary field has no denotation.
 - CODEGEN. Each backend must place the field (cpp / rust / smt).

SCOPE IS LANGUAGE-WIDE, NOT SortedSet's. Every sort with a NAMED requirement slot has this shape; SortedSet is only where it was measured, because its slot is the one the language spells out. A decision of NO is as good an outcome as YES - the message already names the repair (reach the operation through a typed call, or through a sort that declares the slot, which is the form WI-456's Strategy 2b made work in 746acb98).

AND THERE IS NO INSTANCE IN THE STDLIB TODAY, which is why this went unfiled through three legs of WI-456: the three specs SortedSet provides have no default body that reads an ordering. `find` / `exists` take a user predicate, `size` / `foldLeft` walk the iterator, and `collect` / `iterator` read no `O` - measured, not assumed. The shape needs a spec whose default dispatches through the carrier's own comparator, which nothing in the prelude writes. The committed test therefore supplies its own.

ACCEPTANCE: `a_default_body_reading_the_slot_by_value_is_refused_naming_it` INVERTS rather than being deleted - `Driver.byValue` RUNS and answers what the stored dictionary decides; the `direct` row is FIRST strengthened to the ByLength / Alphabetical split above, so that one answer under both orderings fails the test and a stored dictionary that decided nothing cannot pass it; the five obstacles above are each either discharged or explicitly declined at a named site; full workspace green via rustland/scripts/test.sh. A decision NOT to build it is discharged instead by recording that decision in docs/kernel-language.md beside the named-slot rule and inverting the test's doc comment rather than the test.

RELATED: WI-456, where this was measured and whose 2026-09-21 correction entry is the source of the framing above; WI-20260921-159S9, the other residue of the same measurement (an OP-SCOPED slot does not reach a cross-sort call). NOT WI-402, which is Delivered and covers `ensures Spec[C]`, the RETURN position - a dictionary flowing OUT of an operation, which is a different thing from one stored in a datum.

