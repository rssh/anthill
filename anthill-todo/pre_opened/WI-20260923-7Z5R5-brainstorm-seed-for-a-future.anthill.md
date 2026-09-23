## Attributes

- id: WI-20260923-7Z5R5-brainstorm-seed-for-a-future
- created: 2026-09-23T09:30:48Z

- status: PreOpened
- status_agent: user
- status_at: 2026-09-23T09:30:49Z

- acceptance: cargo-test, scaland-sbt-test

## Description

BRAINSTORM (seed for a future proposal): a SortedSet ordered by a comparator that depends on a
RUNTIME VALUE — "order these strings by their distance to `target`", "order records by the
column the user clicked", "order by a locale / a weight vector read at startup". Today there is
no way to write it, by construction.

WHY IT CANNOT BE WRITTEN TODAY. A named slot's provider is a SORT chosen during typing (058 §3.9:
"instances are never CHOSEN at run time"; sortedset.anthill: "a comparator chosen at RUN TIME does
not exist as a concept … every witness is a sort declared in the program text"). A sort's
`compare(a, b)` sees only its two arguments. So a comparator that needs a third value `v` has
nowhere to get `v` from:
  * the witness sort has no instance, so no field can hold `v`;
  * the dictionary is built per call from the TYPE, and a type cannot carry a runtime value
    (value-in-type exists, WI-302/366, but only for values known at typing time);
  * a concrete provider WITH constructors (`entity byDistance(target: String)`) is exactly what
    §3.5 check 3 refuses to name (WI-20260911-TX0G6 kept that rule), and its values are not the
    set's elements anyway, so nothing would pass one in.
The only workaround is to MAP the elements (store `(key(x), x)` pairs under a stock order), which
changes the element type and leaks into every consumer.

QUESTIONS TO BRAINSTORM (none decided):
  1. Where does `v` live? Candidates: in the set VALUE (a comparator field — then two sets of one
     type can disagree, and 058 §3.4's "the order is part of the type" / merge safety needs a
     new story: runtime equality of comparators? refuse `union` unless proved same?); in the TYPE
     as a value-dependent parameter (`SortedSet[T = String, O = ByDistance[target = t]]` with `t`
     a runtime value — dependent-type territory, proposal 045/value-in-type); in a CLOSURE passed
     at construction (a `(T, T) -> Int64` argument, i.e. an ordinary function value instead of a
     provider — what does `requires O: WeakOrd[T]` then mean?).
  2. Is it a different COLLECTION rather than a different selection? e.g. `SortedBy[T, K]` keyed by
     a function value, leaving `SortedSet`'s provider-in-type story untouched.
  3. Laws: a value-dependent comparator must still be a total preorder for EVERY value of `v`;
     who proves or checks that (058 §3.10's use-site discharge is per sort, not per value)?
  4. Merge safety: what does `union(a, b)` do when both are "by distance" to different targets?
     Same type, different orders — the exact thing named slots exist to prevent.
  5. Codegen: Rust/C++ backends map a witness to a static impl; a runtime comparator is a boxed
     closure / functor with state.
  6. Prior art to compare: Haskell (reflection / `Data.Reflection` for runtime instances,
     `Data.Map` with newtype keys), Scala (implicit `Ordering` values, dependent paths), OCaml
     (functor application at run time with first-class modules), Rust (`BTreeMap` needs `Ord` on
     keys; closures via wrapper types), C++ (`std::set<T, Cmp>` with a stateful `Cmp` instance —
     the order IS in the type, the state is in the value).

OUTCOME WANTED: a written brainstorm (options, trade-offs against 058 §3.4 merge safety and §3.9,
a recommended direction) that can be turned into a numbered proposal. No implementation here.

REFERENCE: stdlib/anthill/prelude/sortedset.anthill (header, "WHAT IS NOT HERE"); proposal 058
§3.4, §3.5, §3.9, §7.1; kernel-language §5.4; WI-20260911-TX0G6 (check 3 kept as the named sort's
property).

