# 041 — `result` in Effects Rows

## Status

Draft. Driver is WI-261 (filed). Direct dependency of [027.1](027.1-alloc-effect-and-allocator-revision.md) — the `Modify[result]` discharge story can't be written without `result` being a name resolvable in the effects row.

## Depends on

None. Touches the kernel spec's `result` reservation (§5.4) and the typer's lookup chain for effects rows.

## Related

- [027.1-alloc-effect-and-allocator-revision](027.1-alloc-effect-and-allocator-revision.md) — primary consumer.
- Kernel spec §4.5 (named-tuple types — already in the language) and §6.7 (field access — already in the language). The multi-result discharge story falls out of these existing features once `result` is widened.

## Affects

- `docs/kernel-language.md` §5.4 — broaden `result`'s reserved scope from `ensures`-only to all term positions in the operation declaration.
- `rustland/anthill-core/src/{load,kb/typing}.rs` — extend the lookup chain in `effects` rows to resolve `result`.
- Stdlib + examples adopting `Modify[result]` (opportunistic, driven by 027.1).

## Motivation

Kernel spec §5.4 reserves `result` *only* inside `ensures` clauses:

> `ensures` clauses may additionally reference `result`, which binds to the return value. […] Using `result` in `requires` is a semantic error.

Other operation-declaration positions — most importantly `effects` rows — have no way to refer to the return value. Proposal 027.1 needs exactly this in order to declare allocators as `Modify[result]`. Without `result` being a resolvable name in effects rows, 027.1's framing can't be written.

The fix is small and contained: extend `result`'s reservation from "valid in `ensures` body" to "valid in any operation-declaration term position that semantically refers to the output." That's `effects`, `ensures`, and any future positions (e.g., reflection annotations). It does *not* cross over to `requires` — preconditions still run before the result exists.

### What's already in the language (and therefore not part of 041)

A natural worry would be: "what about multi-result operations? Don't we need a way to refer to individual result fields?" The answer is that **anthill already has the surface for this**, two ways over:

- **§4.5 Named-tuple types** make `(a: Cell[Int64], b: Cell[Int64])` a valid return type today. The spec even uses this exact shape in its own example: `operation divmod(a: Int64, b: Int64) -> (quotient: Int64, remainder: Int64)`.
- **§6.7 Field access** makes `result.a` and `result.b` valid term expressions today (`term.identifier` desugars to `field_access(term, identifier)`).

Combining the two, multi-result effect attribution works without any new grammar:

```anthill
operation make_pair() -> (a: Cell[Int64], b: Cell[Int64])
  effects Modify[result.a], Modify[result.b]
  ensures ne(result.a, result.b)
```

Everything except the bare word `result` in `effects` is already grammatical and type-checks. 041 is therefore one feature, not two: **make `result` resolve in `effects` rows**. Field projection handles the rest.

## Design

### Reserved scope for `result`

`result` is reserved in **all term positions inside the operation declaration that semantically refer to the output**:

| Position | Status today | Status after 041 |
|---|---|---|
| `requires` body | error to reference `result` | unchanged (still error — precondition runs before the result exists) |
| `effects` row | undefined (no precedent) | **reserved — refers to the return value** |
| `ensures` body | reserved — refers to the return value | unchanged |
| `meta` block (term positions) | not specifically reserved | reserved if a term position semantically refers to the output |
| Operation body | parameter / `let` shadowing freely permitted | unchanged (`result` is just a name; the body's `let result = 5; result + 1` is legal) |

The reservation is **soft** in the §2.5 sense — `result` is only special at sites that admit term references to the operation's output. Body-scope `let result = ...` continues to work; `requires`-clause `result` continues to error.

### Multi-result operations — falls out of existing features

For an operation returning a named tuple, the components are accessed via field projection (§6.7) off `result`:

```anthill
operation make_pair() -> (a: Cell[Int64], b: Cell[Int64])
  effects Modify[result.a], Modify[result.b]
  ensures ne(result.a, result.b)
```

There is no new grammar rule "named-result form," no new symbol-resolution chain "named result fields as bare names." The signature already names the components (§4.5's named-tuple types do that work), and field access already projects them (§6.7). 041 only needs to make `result` a resolvable name; the dot-projection then handles per-component reference.

### Typing — one new lookup arm

In the typer pass over `effects` rows, the name-resolution chain gains one entry:

1. Parameter names (existing).
2. **`result` → the operation's return slot, with type = the declared return type** (new under 041).
3. Normal scope chain (existing).

`result.a` then resolves via §6.7's existing field-access machinery: `result` resolves to the return slot at sort `(a: Cell[Int64], b: Cell[Int64])`; the `.a` projection extracts the named field, type `Cell[Int64]`.

`ensures` already does the analogous lookup with `result`; this proposal just adds the same arm in `effects`.

### Name resolution and shadowing

The `result` reservation is soft:

- **`result` as a parameter name**: rejected at the loader. `operation foo(result: Int64) -> Int64` is a hard error — the same name can't refer to both a parameter and the output.
- **`result` inside the operation body**: not shadowed by the proposal. `let result = expr` in the body binds a body-local `result`; the declaration-position `result` is unrelated (different scope).

## Examples

### 027.1's `Cell.new` (single anonymous result)

```anthill
operation new(initial: V) -> Cell[V]
  effects Modify[result]
end
```

### Multi-result with per-component effects

```anthill
operation make_pair() -> (a: Cell[Int64], b: Cell[Int64])
  effects Modify[result.a], Modify[result.b]
  ensures ne(result.a, result.b)
  body...
```

### Partial discharge under 027.1

```anthill
operation keep_second() -> Cell[Int64]
  effects Modify[result]
  let (a, b) = make_pair()
  Cell.set(a, 42)                            -- a's Modify discharges (a doesn't escape)
  b                                          -- b escapes; Modify[result] propagates
end
```

(The body-side destructuring `let (a, b) = ...` is the existing tuple-destructuring from proposal 018; the `result.a` / `result.b` names live in the *signature*, the destructured `a` / `b` live in the *body*. They're independent.)

### Reflection — no change

Existing reflection facts that walk operation signatures already see the return type (named tuple or not) as a structured term. No new fact kind needed; consumers that want per-field info project off the existing TupleType structure.

## Migration

**Single phase.** Extend the typer's lookup chain in `effects` rows to admit `result`. Add tests:

- `effects Modify[result]` parses, resolves, and type-checks (single-return op).
- `effects Modify[result.a], Modify[result.b]` parses, resolves, and type-checks (named-tuple return).
- `effects Modify[result]` in a `requires` clause is rejected with the existing "result not allowed in requires" diagnostic.
- `operation foo(result: Int64) -> Int64` rejected by the param-name conflict check.

Roughly a typer-arm change plus tests. No grammar work, no new IR, no new symbol kind. The "Phase 0" prerequisite that 027.1 mentions is exactly this one change.

## Open questions

1. **Diagnostic wording when `result` appears in `requires`**: today's error is something like "result not allowed in requires." Worth confirming the message is clear after 041 widens the scope elsewhere — readers shouldn't be confused why `effects` admits it but `requires` doesn't. **Suggested**: include "preconditions are checked before the result exists" in the error.

2. **Param-name conflict diagnostic**: `operation foo(result: Int64)` becomes a hard error. Worth a clear message rather than a generic name-collision error. **Suggested**: "the name 'result' is reserved for the operation's return value; use a different parameter name."

3. **Future positions that take terms**: if proposals later add term-position slots in the operation declaration (e.g., a `where`-clause, an annotation expression), they should follow the same convention — `result` resolves to the output. Document the principle alongside §5.4's reservation.

## Out of scope

- The discharge analysis itself ([027.1](027.1-alloc-effect-and-allocator-revision.md)).
- Body-level pattern destructuring (already in [018](018-expressions-and-operation-implementation.md)).
- `requires`-clause access to `result` — not changing.
- Named-tuple return syntax — **already in the language** (§4.5). 041 does not add it; it relies on it.
- Field access syntax — **already in the language** (§6.7). 041 does not add it; it relies on it.
- Reflection-side handling of result-field names — no change needed (existing reflection over the return type's structure already covers it).
