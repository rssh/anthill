## Attributes

- id: WI-20261114-SCGKY-persistence-print-reads-a-list
- created: 2026-11-14T10:47:01Z

- status: Open
- status_agent: claude
- status_at: 2026-11-14T10:47:01Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`persistence::print` reads a list spine by its constructors' SHORT names (`TermPrinter::unwrap_spine` and `list_elements` compare `short_name(f)` with `cons` / `nil`), so a user's own `cons` / `nil` — a sort of their own, in any namespace — prints as a `[…]` literal, and the printed text read back is a prelude `List`: another value, with no error. MEASURED on 379fa18e with `anthill query`:

```anthill
namespace p.pr
  import anthill.prelude.{Int64}
  sort MyL
    entity nil
    entity cons(head: Int64, tail: MyL)
  end
  fact mine(cons(head: 1, tail: cons(head: 2, tail: nil)))
  rule first(?h) :- mine(cons(head: ?h, tail: ?))
end
```

`--mode functor mine` prints `mine([1, 2])` and an answer binds `?l = [1, 2]`; the renamed twin (`kons` / `nill`) prints `mine(kons(head: 1, tail: kons(head: 2, tail: nill)))`. The same program with the printed fact `fact mine([1, 2])` in place of the written one loads clean, and `first(?h)` answers nothing where the original answers `?h = 1`. `unwrap_spine`'s own doc says the `[…]` print exists for persisted facts (runtime-persisted work items), so a stored user-`cons` fact would reload as another value — not measured end to end through the file store.

Same class as WI-20260904-FSNZ5 (a name read by its last segment). FSNZ5 fixed the bounded quantifier's twin of this reader (`resolve::bounded_list_elements` now reads cells by qualified name, as `eval::builtins::list_cell_kind` does) and left this one, because it is not a one-line change: the printer serves two views. `short_name`'s doc says why it reads the last segment — the parse view names a functor as written, so `anthill.prelude.List.cons` and a bare `cons` are one name there — and the file store's retract compares the parse-view print of the on-disk text with the KB-view print of the fact. Reading the KB view by qualified name alone makes the two prints of one user-`cons` fact differ, and the retract a silent no-op. The fix gives both views one answer (e.g. the parse view resolves the written name through the file's imports, or a spine is folded only when both views can tell it is the prelude's). The `sym_name(f) != "tuple"` test beside it is the same reading; `sym_name` returns the verbatim name on the parse view and the local name on the KB view (`desugar_target`'s module doc, "THAT FIX IS PER NAME AND THE SPLIT IS PER VIEW").

ACCEPTANCE: a user's `cons` / `nil` prints as its constructor application on both views, and its printed fact reloads to the same value (`first(?h)` answers `?h = 1` from the reloaded text); a prelude list still prints `[…]` on both views; a persisted user-`cons` fact is retractable through the file store (the shape of `wi1099_list_literal_twin_test::a_persisted_literal_is_still_retractable`); the `tuple` test decided by the same rule or its reading stated at its site; each row says which back-out it fails under; cargo-test green via scripts/test.sh.

