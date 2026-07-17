# Proposal 056 — Variadic argument capture: collecting the unmatched named arguments into a record

**Status:** Draft (2026-07-16; outcome of the WI-714 `fix` design thread)
**Tracked by:** WI-727 (provider). WI-714 depends on it — the `fix` increment is blocked until this lands.
**Driving client:** [052-rules-as-stream-valued-operations](052-rules-as-stream-valued-operations.md) / WI-714 — the `fix` relational-algebra op `r.fix(x: 1, z: 2)` (§4). fix is the first construct whose "arguments" are a variadic set of names, not a fixed parameter list.
**Depends on:** [042-explicit-type-parameters-on-operations](042-explicit-type-parameters-on-operations.md) (the `[R]` capture-type parameter, inferred like `join`'s `L`/`R`), WI-638 (named tuples — the record the capture produces; §6.7 mode 3 already reads it, `t.x`), the `Concat` type-constructor precedent ([052](052-rules-as-stream-valued-operations.md) join / WI-726 — `Without` in §2.2 is its dual), [043.1-compile-time-macros](043.1-compile-time-macros.md) (the rule-head face rides the `[simp]` engine, §2.3).
**Related:** [045-effect-sets-and-expressions](045-effect-sets-and-expressions.md) (**row polymorphism** — the capture type is an open/row record, the record analog of an open effect row), [044-unified-name-resolution](044-unified-name-resolution.md) (named-arg → declared-parameter matching, the step §1 extends), WI-639 (the distribute-dot `.( )` — the sibling "collect members into a named tuple" surface).
**Affects:** grammar (the capture marker on a parameter / a rule-head rest-pattern), loader + typer (arg-matching collects the leftover named args into a named tuple rather than erroring; the `Without` reduction), `docs/kernel-language.md` (§4 parameters; §8.3 rule heads). Runtime: none new — the capture is an ordinary named-tuple value.

---

## 1. Problem

Call resolution matches each **named argument** against a **declared parameter** of that name ([044](044-unified-name-resolution.md)). An operation or rule whose arguments are a **variadic set of names** — not fixed by the signature — has nothing to match them against, and the leftover names are a loud "unknown named argument" error.

The concrete case is WI-714 **`fix`**. `r.fix(x: 1, z: 2)` restricts relation columns `x`, `z` to constants and drops them (052 §"`fix` is sugar"). The keys `x`/`z` are **columns of the receiver relation** — a different relation has different columns (`who`/`item`, …), so no fixed parameter list can name them:

| step (usual DotApply, `r.fix(x: 1, z: 2)`) | outcome |
|---|---|
| `r` types as `Relation[T = (x: Int64, z: Int64, …)]` | ✓ |
| method fallback resolves `fix` on `Relation` → synthesizes `fix(r, x: 1, z: 2)` | ✓ |
| Apply arg-match: `x`/`z` against `fix`'s declared params `(r: Relation)` | ✗ **unknown named argument** |

The only escape without this feature is to key the typer on the op's identity (`op_sym == Relation.fix`, then read the named args as columns by hand) — the per-op recognizer the "no op-name-keyed typer code" discipline forbids ([052](052-rules-as-stream-valued-operations.md) join → `Concat`; the litmus: *could another op reuse it by writing the same type?*). It is **not** reusable, and it duplicates the column-binding logic the **applied citation position** already performs generically (`someRule(x: 1)`, a rule reference applied with a column-named arg, is bound + narrowed in `relation_reference_type_applied`, keyed on the functor's *kind* being a rule — never a name).

The missing capability is **general**: a way to **capture variadic named arguments**. Given it, `fix` is an ordinary operation resolved through the usual path with **zero name-keying** — and any future variadic-keyed construct reuses the same mechanism.

## 2. What this adds

A **capture parameter**: one parameter that collects every named argument **not matched to a declared parameter** into a single **named-tuple (record) value**. No new value kind — the record is a named tuple (WI-638), which the body already reads by component access (`t.x`), which downstream **type constructors** already consume, and which the runtime already carries as `Value::Tuple`.

The capability has **two faces** — the same "collect leftover named args → record", surfaced where each kind of client needs it. Which face a client uses is exactly the macro-vs-typer-direct choice 052 already makes per algebra op (`where`/`join` ride a `[simp]` macro; `project`/`fix` are typer-direct):

| face | surface | binds | consumed by |
|---|---|---|---|
| **operation parameter** (§2.1) | `operation fix[R](p: Relation, ...args: R)` | `args : (x: Int64, z: Int64)` — a record **value**; `R` its **type** | the op body, or a **return-type constructor** (`Without`, §2.2) |
| **rule-head rest-pattern** (§2.3) | `rule fix(?r, ...?args) <=> …` | the record **occurrence** bound by `...?args` | a `[simp]` **macro** ([043.1](043.1-compile-time-macros.md)) |

**The "row variable" is an ordinary type parameter; `...` is the capture marker.** `[R]` is a plain explicit type parameter ([042](042-explicit-type-parameters-on-operations.md), as `join[L, R]`), **inferred from the call** — the leftover named args `(x: 1, z: 2)` bind `R = (x: Int64, z: Int64)`, exactly as `join` infers `L`/`R` from its operands. `...args` marks the *one* parameter that collects the residue. This reuses **two existing mechanisms** (explicit type params + a rest marker) instead of inventing open-record syntax; `R` is then a first-class handle the return type consumes (`Without[Drop = R]`). The only new token is `...`.

### 2.1 Operation face — capture makes it *usual* DotApply resolution

**Today** `r.fix(x: 1, z: 2)` does **not** resolve: the ordinary DotApply method fallback synthesizes `fix(r, x: 1, z: 2)`, and arg-matching rejects `x`/`z` as unknown named arguments (the §1 failure).

**056 changes exactly one step of that same ordinary path:** with a `...args: R` capture parameter, arg-matching no longer *rejects* the leftover named args — it **collects** them into `args` as a named tuple `(x: 1, z: 2)`, whose type binds `R = (x: Int64, z: Int64)` (ordinary type-param inference, as `join` binds `L`/`R`). So the call *will* resolve, through the unchanged method fallback → `fix(p, «captured»)` → ordinary Apply typing. Everything else is pre-existing: no `[simp]` rule, no macro, no op-identity recognizer; `args` reaches the runtime as an **ordinary argument** (a `Value::Tuple`) the back-end reads directly, with none of `where`/`project`'s compile-time spec-splicing. `fix` is a plain operation; the `...args` parameter is the *sole* new mechanism.

### 2.2 Type side — `Without`, the dual of `Concat`

The result type is a function of `R` — the captured record's type — expressed as a **type constructor**, never op-name-keyed Rust (the 052 join / `Concat` discipline). fix's schema is `p.T` **minus** the captured columns:

```anthill
operation fix[R](p: Relation, ...args: R) -> Relation[T = Without[T = p.T, Drop = R]]
```

`Without[T, Drop]` reduces at the **return-type normalization boundary** — the same place `Concat` and `s.T` reduce: drop from named-tuple `T` every field whose name is a field of `Drop`; the residual 1-collapses / `Unit`s as any relation schema does. The **membership + type checks live in the reduction**: a `Drop` field naming no `T` field, or one whose type mismatches its column, is a **load error** there. So the capture itself stays **unconstrained** (`R` is inferred, collecting whatever is passed); the consumer's type constructor supplies the meaning. `Without` is generic — any op that writes `Without[…]` reuses it, exactly as any op may write `Concat[…]`.

### 2.3 Rule-head face — the variadic `[simp]` head

For a client that prefers the macro route ([043.1](043.1-compile-time-macros.md), as `where`/`join` do), a rule head captures the leftover args with the same `...` marker, into a record **occurrence**:

```anthill
rule fix(?r, ...?args) <=> fix_of(?r, args)   [simp]
```

`...?args` is the variadic analog of join's fixed `(?r1, ?r2, ?cond)` head: it binds the leftover named args as one record occurrence the macro `fix_of` reads (via the reflect occurrence API — `sub_occurrences`, component names). This face is optional for `fix` (§2.1's operation route is simpler and needs no macro); it exists so the `...` capture is uniform across **both** dispatch styles 052 uses.

### 2.4 Why records don't flatten — the effect-row disanalogy

An **effect** row `{X, Y}` is set union: if `X`/`Y` are rows they **flatten** into one flat row, and a row variable splices in transparently (unordered, name-free, idempotent). An **argument** record does **not** — its fields are *named and structured*, so two records cannot auto-merge (name collisions, no set semantics) and a captured record cannot auto-splat back into a call. Two consequences, both load-bearing:

- **(a) The capture is a record, in `( )` — never effect-set `{ }`.** `{ }` signals flatten; a captured argument list is structured, so it rides the named-tuple `R`, combined only by name.
- **(b) Schema combination is an explicit, name-aware type constructor** (`Concat` / `Without`), **not** `{ }`-algebra. `join`'s signature already splits exactly along this line: `E = {r1.E, r2.E}` **flattens** (effects), while `T = Concat[A = r1.T, B = r2.T]` is an **explicit** merge (records). `fix`'s `Without[Drop = R]` is the same on the drop side.

## 3. Design decisions & open questions

| # | decision | position |
|---|---|---|
| 1 | **Marker / "row var" spelling** — RESOLVED | `fix[R](p, ...args: R)`: `[R]` is a plain explicit type param ([042](042-explicit-type-parameters-on-operations.md), inferred like `join`'s `L`/`R`), `...args` the rest marker. No new record-row syntax; the one new token is `...`. NOT effect `{ }` — records don't flatten (§2.4). |
| 2 | **Named + positional** | `...args: R` captures **both**: a positional leftover lands in `R` as `_N` (§4.5 named-tuple positional sugar), so one mechanism covers named and positional — no separate positional-variadic feature. |
| 3 | **Ordering** | a named tuple is name-keyed / order-independent (§4.5); a positional residue keeps its `_N` order. |
| 4 | **Constraint on captured fields** | **none on the capture** (`R` is inferred, unconstrained); the consumer's `Without` enforces "fields ⊆ columns, types match". |
| 5 | **At most one, trailing** | a second `...` parameter is ambiguous; trailing keeps declared-param matching unchanged (capture is the residue). |
| 6 | **Empty capture** | `r.fix()` → `R = ()` → `Without[T, ()] = T` (identity); a legitimate degenerate case, not an error. |
| 7 | **WI-726 safety** | `R` types the *args* capture, not the relation's `T` — `fix[R]` never aliases `Relation.T`, so it avoids the `join[L, R]`-on-`Relation[T = L]` aliasing bug (WI-726 / the join increment). |

**Grammar — probed conflict-free (this session).** The `...` marker is a single **fused lexer token** — the exact technique the distribute-dot `.(` uses (grammar.js: `token(seq('.', '('))`) to stay conflict-free by **diverging at the lexer** from `.` / `.(` / `A.B`. Empirically: adding `optional(field('rest', token('...')))` to the `param` rule and regenerating is **conflict-free**; `fix[R](p: Relation, ...args: R)` parses with the `rest` marker on exactly the `...args` param (`p: Relation` untouched, no `ERROR`/`MISSING` nodes); `x.field` / `rel.(name, age)` / `Ns.Sort.member` all coexist; and the **full 176-test corpus passes**. So the grammar side of §Affects is a one-line `param`-rule change, already validated.

**Prior art (WI-727 research thread).** `Without[T, Drop]` = TypeScript **`Omit<T, K>`** (project = `Pick<T, K>`); the `...args` capture = TS **object rest** `{ ...rest }` — both mainstream, both *utility/library* shapes rather than keywords, validating the type-constructor altitude. [Scala 3 named tuples](https://docs.scala-lang.org/sips/58.html) (3.7+) match anthill's `(name: T, …)` record and offer *subset* pattern matching (`case (age = x) => …`, unmentioned fields silently ignored) but have **no rest-capture and no open rows** — so it is the **internal 045 row precedent**, not Scala, that carries the capture here.

## 4. Client: WI-714 `fix` — before / after

| | today (this thread's draft) | with 056 |
|---|---|---|
| recognition | `op_sym == Relation.fix` gate in the DotApply handler | **none** — usual method dispatch resolves `fix` |
| named-arg columns | read by hand from the raw occurrences | **captured** into `...args: R` (the record `args`, its type `R`) |
| schema narrowing | inline column-drop in a fix-specific helper | the general **`Without[Drop = R]`** type constructor |
| constant type-check | a bespoke literal-vs-column check | falls out of the `Without` reduction |
| runtime | typer splices a `Term` spec → `fix_run(r, spec)` | `fix` reads the `args` **record value** directly |

`fix` collapses from a per-op typer recognizer to an **ordinary operation** — one declared with a capture parameter, one `Without` in its return type, one host builtin that reads a record and wraps `guarded` + drops the columns. Nothing in the typer is keyed on `fix`.

## 5. Out of scope

- **A *separate* positional-variadic feature** — not needed, and not built. Positional capture is **already subsumed**: a positional leftover lands in `R` as a `_N` field (§3 OQ #2, the named-tuple positional sugar §4.5), so `...args: R` covers named **and** positional through one mechanism. (This is *more* general than C-style varargs — the residue is heterogeneous and individually typed, not a homogeneous list.)
- **Row-record subtyping in general** — 056 needs only the *capture* (collect the residue) and the *reduction* (`Without`); a full record-subtyping calculus (open records as first-class param types elsewhere) is a larger, separate question.
- **`fix`'s own semantics** — restrict-then-drop, the `guarded` + project lowering — are 052 / WI-714; 056 only removes the resolution blocker.
