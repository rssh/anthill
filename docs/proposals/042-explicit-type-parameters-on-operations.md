# 042 — Explicit Type Parameters on Operations

## Status

Draft. Three concurrent drivers:

1. **WI-260 (delivered) lives with a workaround.** `stdlib/anthill/reflect/reflect.anthill:159` currently declares `operation term_as_entity(t: Term) -> Option[T = ?E]`. The intended signature (per WI-260's description) was `Option[E]` with `E` a proper type parameter of the operation; the `?E` form is what the language can express today, and the field's prose explicitly notes the asymmetry: "The return parameter `E` is the caller-side expected entity sort; this builtin doesn't type-check that the recovered entity matches `E`." That is a workaround comment, not a design choice — the typer can't bind `E` because there's no surface for declaring it.

2. **Proposal 027.1 needs typed HOFs over collections** (`map`, `for_each`, `fold`) before the `Modify[result]` discharge story can be tested end-to-end on realistic code. Today's `Collection` / `Iteration` specs in `stdlib/anthill/prelude/{collection,iteration}.anthill` declare per-sort type parameters (`Element`, `Effect`) but offer no shape for free-standing HOFs that bind a *new* type parameter at the call (`map[A, B](xs: List[A], f: (A) -> B) -> List[B]`).

3. **Proposal 035 already commits to this surface but never formalizes it.** §"Free-standing parametric operations" of 035 says:
   > Symmetry says yes: if `operation foo[A, B](...) -> ...` is valid inside a sort body, it must be valid at namespace level too.
   …with example `operation pair[A, B](a: A, b: B) -> Pair[A = A, B = B]`. But the kernel-language spec's `Operation` production (§5.4, grammar at line 1751–1758) has no `[TypeParamList]` slot, and the tree-sitter grammar does not parse the bracketed form. 035 is marked Accepted on the strength of the typed-constructor (`Map[K, V].empty()`) story; the parametric-operations clause was left informal.

This proposal fills the gap: explicit type parameters at both declaration and call sites, formalized in the kernel grammar and typer, with explicit-form ↔ implicit-`?T`-form bidirectional desugaring.

## Depends on

- [015-universal-type-variables](015-universal-type-variables.md) — the implicit `?T` form this proposal exposes as explicit.
- [020-bracket-type-parameters](020-bracket-type-parameters.md) — `[bindings]` syntax for type instantiation; reused here at call sites.
- [035-typed-constructors-on-parameterized-sorts](035-typed-constructors-on-parameterized-sorts.md) — assumes this proposal; its "free-standing parametric operations" clause is what this formalizes.

## Affects

- `docs/kernel-language.md` §5.4 — extend the `Operation` production with an optional `[OperationTypeParamList]` between `Name` and `(`. §5.2 — cross-reference the new declaration form alongside `sort T = ?`; clarify that `[T]` is the operation-level analog (named logical variable, surface for caller-side binding).
- `docs/design/operation-call-model.md` §"Operation type arguments" — describe how operation-level type arguments flow through `frame.requirements` after sort-specific entries. (Added by this proposal.)
- `tree-sitter-anthill/grammar.js` — extend the `operation_declaration` rule and add `operation_type_param`, `operation_type_arg` productions.
- `rustland/anthill-core/src/parse/{ir,convert}.rs` — surface the type-param list in `Item::Operation`'s parse IR.
- `rustland/anthill-core/src/kb/load.rs` — allocate a `VarId` for each declared type parameter and bind it in the operation's symbol scope before processing the param list, return type, and contracts.
- `rustland/anthill-core/src/kb/typing.rs` — call-site type-application: seed the unification env from `OperationTypeArgList`, then run HM inference for any remaining slots.
- `rustland/anthill-core/src/eval/{eval,value}.rs` — populate `frame.requirements` with type-argument entries (positional, in declaration order) after sort-level entries at frame push.

## Motivation

### What's expressible today

The implicit form already works for the simple case of "this op is polymorphic in one or more type parameters":

```anthill
operation identity(x: ?T) -> ?T              -- per kernel-language.md §5.2
operation length(l: List) -> Int             -- T comes from List's sort body
operation term_as_entity(t: Term) -> Option[T = ?E]   -- ?E inferred at call site
```

Two limits show up almost immediately:

**Limit 1 — no way to *declare* the type parameter the operation introduces, separate from its uses.** Reading `operation term_as_entity(t: Term) -> Option[T = ?E]`, a reader must scan all uses of `?E` to know that `E` is the operation's own type parameter, not a shared variable with some outer scope. This works for one-line signatures; it fails for multi-parameter HOFs:

```anthill
operation fold(xs: ?C, init: ?A, step: (?A, ?B) -> ?A) -> ?A
  -- Is ?C polymorphic? Is ?B Element-of-?C? Reader has to infer.
```

**Limit 2 — no way to *apply* type arguments explicitly at a call site.** When inference is ambiguous, today's only workaround is to bind the result through a typed `let`:

```anthill
-- The call is ambiguous (?E unconstrained):
term_as_entity(t)                                            -- which entity?

-- Today's workaround: pin the result via an annotated let.
let some(v): Option[WorkItem] = term_as_entity(t)            -- ?E = WorkItem (inferred)
```

Proposal 035 already commits to fixing this for sort companions (`Map[K = String, V = Int].empty()`). The same shape, applied to a free-standing operation, is what this proposal lands.

### Concrete unblockings

**`term_as_entity`** — replace the workaround declaration with a proper type parameter:

```anthill
-- Before (workaround, today):
operation term_as_entity(t: Term) -> Option[T = ?E]

-- After (this proposal):
operation term_as_entity[E](t: Term) -> Option[E]
```

Callers that supply context (typed `let`, typed parameter, function return) get inference. Callers that don't can pin the parameter explicitly: `term_as_entity[WorkItem](t)`.

**Collection HOFs** for 027.1 testing:

```anthill
-- map: existing form (cannot express the relationship between input and output element types):
operation map(c: ?, f: (?A) -> ?B) -> ?
  -- Cannot say "?C's Element is ?A" or "?C and the result share a constructor",
  -- and the result effect row has no name to bind to `f`'s row.

-- map: with explicit type params and Collection requires (this proposal):
operation map[A, B, C, E](c: C, f: (A) -> B @ E) -> C
  requires Collection[Collection = C, Element = A, Effect = E]
  requires Collection[Collection = C, Element = B, Effect = E]
  effects E
  -- Same constructor for in and out, different element types. `E` is map's
  -- effect row, inherited from f and re-exported via the Collection requires
  -- so the result type's effect row matches.
  -- The `Collection = C` binding stays named here: the parameter named
  -- `Collection` collides with the sort name `Collection`, so positional
  -- (`Collection[C, A, E]`) would parse but read awkwardly.
```

**HOFs with effect rows** (the 027.1 trigger):

```anthill
operation for_each[A, E](xs: List[A], f: (A) -> Unit @ E) -> Unit
  effects E
  -- E is bound at the call by f's effect row; propagated to for_each's row.
```

Without per-operation type-parameter declarations, `E` here would have to be either (a) a stdlib-wide named variable colliding with other uses, or (b) `?E` with the typer asked to do harder scope work than the explicit-binding case.

## Design

An operation introduces a small **environment of logical variables** — its type
parameters `[T]` — and the rest of this section is facets of that one
environment, not separate features:

- it is **inferred bidirectionally** — synthesized from the arguments, then
  checked against the expected return (§"Resolution at a call" / "Inference
  order");
- a variable is introduced **explicitly** as `[T]`, or **implicitly** by a
  sort-carried projection `X.L`, which mints one *and* adds a `requires X[L =
  Ti]` (§"Type projections");
- the bound variables **parameterize the `requires`** the operation carries —
  they set the bindings its requirement dictionaries are constructed at
  (`operation-call-model.md`).

`[T]`, type projections, and `requires` are three faces of the same environment.

### Declaration-site syntax

Extend the `Operation` production with an optional bracketed type-parameter list, immediately after the name:

```
Operation ::= DescriptionBlock*
                [Visibility] 'operation' Name [OperationTypeParamList]
                '(' [ParamList] ')' '->' Type
                ['requires' RuleBody]
                ['ensures' RuleBody]
                ['effects' '(' Effect (',' Effect)* ')']
                ['meta' ':' Meta]

OperationTypeParamList ::= '[' OperationTypeParam (',' OperationTypeParam)* ']'
OperationTypeParam     ::= Name                  -- shorthand for `Name = ?`
                         | Name '=' Type         -- with default value
```

Each entry declares a named logical variable scoped to the operation. The three shapes:

| Form | Meaning at declaration site |
|---|---|
| `Name` | Shorthand for `Name = ?` — declare the name for a fresh anonymous logical variable. |
| `Name = ?` | Explicit form of the above. |
| `Name = Type` | Declare the name with a default — used when the caller and inference both leave the slot unfilled. |

So `operation map[A, B](...)` is exactly `operation map[A = ?, B = ?](...)` with the `= ?` elided. This mirrors how `sort T = ?` works in a sort body — same `Name = ?` shape, same fresh-logical-variable allocation. The brackets are just the per-operation listing form.

**Distinct from `SortBinding`.** Although the surface shape `Name = Type` (and the punning `Name`, and `?`) is the same as `SortBinding` (kernel spec §5.1), this is **not** a `SortBinding`. A `SortBinding` is interpreted at a sort instantiation site (`Foo[T = Int]`), where the binding is one-per-instance: every reference to `Foo[T = Int]` in the same scope denotes the same instantiated sort. An `OperationTypeParam` is declared at the operation's signature, and bindings at call sites (next subsection) are **one-per-call** — two separate `foo[T = Int](...)` calls produce two independent fresh logical variables that happen to be bound to `Int`, not one shared instantiation. The shapes coincide; the semantics do not.

### Scoping

A type parameter declared in `[T1, T2, ...]` is in scope for:

- The parameter list (`Param ::= Name ':' Type` — `T` resolvable as a Type).
- The return type.
- The `requires`, `ensures`, and `effects` clauses.
- The operation body (when one exists per proposal 018).

A type parameter does **not** escape the operation declaration. Two operations may reuse the same letter without collision.

### What the kernel does today, and what's missing

At the kernel level, **every type variable is a logical variable** (`Term::Var(vid)`). All three surfaces below produce the same KB representation — a `Var(vid)` scoped to the operation, filled by inference at the call site:

```anthill
operation map(xs: List[?A], f: (?A) -> ?B) -> List[?B]   -- ?T form (§5.2)
operation map(xs: List[A],  f: (A) -> B)  -> List[B]     -- unfilled bare names (§5.2 alias)
operation map[A, B](xs: List[A], f: (A) -> B) -> List[B] -- this proposal
```

The first two are already accepted by the kernel. Both produce a per-call-site `VarId` for `A` and `B` that the typer fills from arguments and context. They differ only in surface aesthetics — there's no semantic difference between `?T` and bare-unfilled `T`.

What's missing is a way for the **caller** to set the value of a logical variable explicitly. Inference handles the easy cases; when context is ambiguous, today's only workaround is an annotated `let` (`let v: Option[WorkItem] = term_as_entity(t)`) that pins the result type and lets inference flow backward. There is no surface for "this is the value of `A`, here, now, for this call."

### What `[T]` adds: a named handle for an operation's logical variables

The bracketed declaration is a **named handle** for one of the operation's logical variables, accessible from the call site. `[T]` is shorthand for `[T = ?]` — name `T` is being declared for a fresh anonymous logical variable, exactly the same kernel operation as `sort T = ?` inside a sort body:

```anthill
-- Sort body (existing kernel feature, §5.2):
sort Foo
  sort T = ?                                       -- name a logical variable
  entity Bar(x: T)                                 -- reference by name
end
fact Foo[T = Int]                                  -- caller binds the name explicitly

-- Operation head (this proposal):
operation map[A, B](xs: List[A], f: (A) -> B) -> List[B]
-- = operation map[A = ?, B = ?](...)              -- equivalent explicit form
map[A = Int, B = String](xs, f)                    -- caller binds the names explicitly
```

A signature that uses `?A` / `?B` (or unfilled bare `A` / `B`) instead of `[A, B]` produces the same logical variables at the kernel level, but they're anonymous from the caller's perspective — no name to bind. The proposal's contribution is therefore "let the operation **expose** one or more of its logical variables under a name." It doesn't change the kernel's variable mechanism; it adds a way to address it.

**Call-site bindings as scoped type aliases.** `map[A = Int, B = String](xs, f)` reads as: for the duration of this call, alias `A = Int` and `B = String` for `map`'s named logical variables. The shape is borrowed from `Foo[T = Int]` for sorts — same brackets, same `Name = Type` punning — but the binding is per-call, not per-instance (see the next subsection).

Internally the loader allocates a `VarId` for each declaration entry (one per bare-name entry; the explicit `Name = Type` form uses the supplied Type as a default that the call site can override) and records the name in the operation's symbol scope. Resolution of bare type names inside the operation body looks up declared parameters the same way sort-body resolution does for `sort T = ?` declarations. A signature can mix `[A]` and `?B` (different letters): `A` has a caller-visible name, `B` doesn't — both are logical variables, only one is addressable from outside.

### Call-site syntax (explicit type application)

The call site uses an `OperationTypeArgList` — same surface shape as a sort instantiation's `[bindings]` but semantically a **per-call** binding, not a per-instance one. Both positional and named forms are accepted, matching the convention already established for sort instantiation (kernel spec §5.1 lines 481–503):

```
PrimaryTerm ::= ...
              | Name OperationTypeArgList '(' [ArgList] ')'   -- typed call

OperationTypeArgList ::= '[' OperationTypeArg (',' OperationTypeArg)* ']'
OperationTypeArg     ::= Type              -- positional: binds the next unfilled type parameter in declaration order
                       | Name '=' Type     -- named:      binds the parameter with this name
```

Positional and named entries may be mixed in one call, with positional first — same rule as `SortBinding` for sort instantiations (`Bifunctor[String, B = Int]`, kernel spec line 498).

Each entry binds one of the operation's declared type parameters for the duration of this single call. Two calls `foo[T = Int](a)` and `foo[T = Int](b)` are two independent binding events — the typer allocates fresh `Var(vid)`s for each call and unifies them with `Int` separately. Contrast with `Foo[T = Int]` written twice in the same scope: those denote the same instantiated sort.

Examples:

```anthill
-- All four forms valid; choose by call-site need.
term_as_entity(t)                                  -- inference (no bindings)
term_as_entity[WorkItem](t)                        -- positional (single param — natural)
term_as_entity[E = WorkItem](t)                    -- named (when you want it explicit)

-- HOF calls — positional when the param order is canonical:
map[Int, String, List[Int], {}](xs, int_to_string)        -- all positional
map[A = Int, B = String](xs, int_to_string)               -- only A and B, rest inferred (named)
map[Int, String](xs, int_to_string)                       -- A and B positional, C and E inferred
map(xs, int_to_string)                                     -- all inferred
```

The positional form mirrors `Map[String, Int]` (kernel spec line 491) — same convention, same disambiguation. Reach for the named form when (a) you want to skip a leading parameter and bind only a later one, or (b) the call is part of the stdlib's public surface and you want robustness under reordering / new-parameter additions. Otherwise positional reads cleaner.

This is the same grammar already accepted in proposal 035 for sort companions — the resolver already sees `Map[K = String, V = Int]` as an instantiation term in receiver position. Extending the parser to accept it before a `(` argument list (instead of before `.empty()`) is a one-line addition.

**Disambiguation.** `Name[...]` followed by `(` is a typed call. `Name[...]` followed by `.` is a sort-companion call (proposal 035). `Name[...]` followed by neither is an instantiation term (proposal 020). The three uses share the same lexical prefix and disambiguate on the following token — no new ambiguity introduced.

### Typer: resolution at a call

When the typer sees `op[bindings](args)`:

1. **Explicit `bindings` first** — substitute the parameters the caller pinned via `op[T = …]`; the rest go through inference.
2. **Inference for the remaining parameters is *bidirectional*** — the three sources are consulted in a **fixed order**, not as one symmetric constraint set (detailed in the next section, "Inference order"):
   - **arguments** synthesize the parameters (bottom-up, including across a provider boundary);
   - the **expected return** then fills only *still-free* parameters (top-down — assignment LHS, function return, argument position) — never overriding an arg-bound one;
   - **`requires`** constraints are discharged as goals that may pin any still-free parameter.
3. **No source pins an unbound parameter** — type error naming it; the caller supplies it via `op[T = …](args)`.

`op(args)` (no explicit bindings) is just case (1) with an empty bindings list — every parameter goes through inference. The shape parallels 035's `Map.empty()` resolution; the generalizations are that an operation has its own bindings table, and that the three sources are **ordered** (arguments before expected) — which 035's symmetric account left unstated.

### Inference order: arguments before expected (bidirectional)

Step 2's three constraint sources are not symmetric — their **order is fixed**, and the rule is **bidirectional** (synthesize up from arguments, then check against the expected):

1. **Synthesize from the arguments first.** Bind each parameter from the argument types (bottom-up) — *including across a provider boundary*: a `List[Int]` argument supplied where a `Stream[T = A]` parameter is declared binds `A := Int` through `List`-provides-`Stream` (the carrier's provider fact threads the binding; `Stream[T = A]` viewed against `List[Int]`-as-a-`Stream`).
2. **The expected return type fills only *still-free* parameters** — never overrides one the arguments already bound. `empty() : List[A]` (no arguments) still takes `A` from the expected; `id_list[A](xs: List[A]) -> List[A]` on a `List[Int]` does **not** let an expected `List[String]` re-bind `A`.
3. **Check** the synthesized result against the expected (the conformance check at the call's use site — operation return, typed `let`, argument position).

This ordering is a **soundness requirement**, not an optimization. Reversed — expected seeding parameters *before* arguments — a wrong declared return is silently accepted: `id_list(List[Int])` assigned to `List[String]` would pin `A := String` from the expected, the contradicting argument `List[Int]` would be ignored, and the unsound result would survive. Arguments-first pins `A := Int`; the expected `List[String]` then cannot re-bind the now-pinned `A`, and the result `List[Int]` is correctly rejected.

The kernel today does the reverse — `rustland/anthill-core/src/kb/typing.rs` (`check_apply_iter`) seeds parameters from the expected return *before* argument unification, with the correct order patched in only as a special case for self-receiver spec operations (WI-367). Making **arguments-before-expected** the general rule generalizes that fix, and is the load-bearing piece for sound `[T]` inference. See [`docs/design/type-parameter-scoping.md`](../design/type-parameter-scoping.md) for the surrounding rule set (projection `s.T` / `s.Sort`, expansion, no implicit sort-parameter sharing).

### Type projections (`s.T`, `s.Sort`, `X.L`) — and why the sort-carried form is an `[T]`

A **type projection** reads a type member off a path. There are two forms with two distinct meanings — and one of them *is* an operation type parameter, which is why it belongs here.

**Expression-carried `s.T` / `s.Sort`** — `s` is a *value* (a parameter or local). `s.T` is the named type member `T` of `s`'s static type; `s.Sort` is `s`'s whole parameterized sort (`= Stream[s.T, s.E]`). It elaborates to a fresh `Ti` plus the **constraint** `Ti = typeof(s).T`, discharged the moment `s` is synthesized (bidirectional, §"Inference order"). `Ti` is *determined* by `s` — it is **not** a free operation type parameter; this is a synthesis-time constraint, not an `[T]`. Used to thread a producer's element fluently: `iterator(l: List) -> Stream[T = l.T]`. (Surface + elimination: WI-376.)

**Sort-carried `X.L`** — `X` is a *sort* (a type), `L` one of its parameters. This **is sugar for an operation type parameter plus a requirement**:

```
f(..., p: X.L, ...)   ≡   f[Ti](..., p: Ti, ...)  requires X[L = Ti]
```

`X.L` mints a *fresh, free* `Ti` (the operation becomes polymorphic in it — an anonymous `[Ti]`) and synthesizes `requires X[L = Ti]` (the caller must supply an `X` whose `L` is that `Ti`). Many members extend trivially:

```
... X.L1 ... X.L2 ...   ≡   [Ti1, Ti2]  requires X[L1 = Ti1, L2 = Ti2]
```

This is the F-ω / Scala `X#L` abstract-type-member encoding: an abstract type member becomes a fresh variable bounded by a requirement. The synthesized `Ti` flows like any operation type parameter (inferred per §"Inference order", threaded through `frame.requirements`), and the generated requirement materializes exactly as any other (`construct_requirement`; `operation-call-model.md`). So **sort-carried projection adds no new machinery** — it desugars onto the operation-type-parameter + requirement channels this proposal and operation-call-model already define. (The grammar parses both — a dotted name in type position, same CST as a qualified ref; the loader classifies by `SymbolKind`: value head → expression-carried, sort + member → sort-carried. Elimination: WI-376.)

### Worked example: `term_as_entity`

```anthill
operation term_as_entity[E](t: Term) -> Option[E]
```

Three call patterns:

```anthill
-- (1) Expected-type context — E = WorkItem inferred from let LHS.
let opt: Option[WorkItem] = term_as_entity(t)
match opt
  some(value: ?w) -> handle(?w)               -- ?w: WorkItem
  none -> handle_missing()

-- (2) Immediate-use context — E = WorkItem inferred from the next arg.
match term_as_entity(t)
  some(value: ?w {< WorkItem >} ?) -> handle(?w)   -- explicit annotation pins E
  none -> handle_missing()
-- Note: the description block here doesn't drive inference (description blocks are
-- metadata, not types). Inference for case (2) flows from the match arm pattern's
-- expected type.

-- (3) Explicit application — no context required.
let opt = term_as_entity[WorkItem](t)
```

### Worked example: collection `map`

```anthill
operation map[A, B, C, E](xs: C, f: (A) -> B @ E) -> C
  requires Collection[Collection = C, Element = A, Effect = E]
  requires Collection[Collection = C, Element = B, Effect = E]
  effects E
```

Two `requires` mention `C` with the same constructor but different `Element` bindings — this is the "container-with-different-elements" shape that today's `Collection` spec can express only awkwardly. With explicit `[A, B, C, E]`, the relationship is in the head, not buried in the body. `E` makes the effect inheritance explicit: `map`'s row is exactly `f`'s row.

A call:

```anthill
let ys: List[String] = map(xs, int_to_string)
-- Inference fills: A = Int (from xs: List[Int]), B = String (from int_to_string's
-- return), C = List (from xs's constructor), E = {} (from int_to_string's row); 
-- requires both hold.

-- Effectful f propagates:
let ys: List[String] = map(xs, lambda x -> Cell.set(c, x); int_to_string(x))
-- E = Modify[c] inferred from f's body; map's row becomes Modify[c].
```

For HOFs that *change* the constructor (`to_set`, `to_map_by`, …), the explicit form is the natural shape:

```anthill
operation to_set[A](xs: List[A]) -> Set[A]
  -- A is the only type parameter; the constructor change is reflected in param
  -- and return types.
```

### Worked example: effect-polymorphic HOF (for 027.1)

```anthill
operation for_each[A, E](xs: List[A], f: (A) -> Unit @ E) -> Unit
  effects E
```

Effect-row polymorphism via a type parameter `E` was already half-supported (kernel spec §5.5 mentions `sort E = ?` for sort-level effect polymorphism). Promoting `E` to an operation-level explicit parameter makes the relationship explicit: the operation's row is exactly `f`'s row. A call:

```anthill
for_each(xs, lambda x -> Cell.set(c, Cell.get(c) + x))
-- f's row is Modify[c]; for_each's row inherits Modify[c]. E = Modify[c] inferred.
```

This is the missing piece for 027.1's allocator-discharge analysis on realistic HOF call sites — without operation-level `[E]`, the typer has no name to bind the inferred row to.

### Non-overlap with `requires` quantification

A sort's `requires` clause introduces a different kind of binding: "this sort's type parameter `T` must satisfy `Eq[T]`". That's a quantification over the sort's *declared* parameters, not an introduction of new ones. Operation-level `[T1, T2, ...]` is the *introduction* site. The two compose:

```anthill
sort Map
  sort K = ?
  sort V = ?
  requires Eq[T = K]                  -- K-quantified (from sort's declared K)

  operation merge_with[F](m1: Map, m2: Map, combine: (V, V) -> V) -> Map
    -- F is an operation-level parameter (not used here, illustrative).
    -- K, V come from the enclosing sort's declared parameters.
end
```

`K` and `V` are still resolved through the sort's scope; `F` is resolved through `merge_with`'s own bindings table. Same lookup mechanism, two bind sites.

**Where they touch.** A sort-carried projection `X.L` (§"Type projections") is the one form that does both: it is an operation-level *introduction* (`[Ti]`) that *also* emits a `requires X[L = Ti]`. That isn't the sort-`requires` case — it's the introduction site generating its own requirement, not a quantification over already-declared sort parameters — but it is where introduction and requirement coincide in a single piece of syntax.

## Grammar Changes (tree-sitter)

```js
// Before:
operation_declaration: $ => seq(
  optional($.visibility),
  'operation',
  field('name', $.name),
  '(',
  optional($.param_list),
  ')',
  '->',
  field('return_type', $._type),
  optional($.requires_clause),
  optional($.ensures_clause),
  optional($.effects_clause),
  optional($.meta_clause),
),

// After:
operation_declaration: $ => seq(
  optional($.visibility),
  'operation',
  field('name', $.name),
  optional($.type_param_list),
  '(',
  optional($.param_list),
  ')',
  '->',
  field('return_type', $._type),
  optional($.requires_clause),
  optional($.ensures_clause),
  optional($.effects_clause),
  optional($.meta_clause),
),

operation_type_param_list: $ => seq(
  '[',
  commaSep1($.operation_type_param),
  ']',
),

operation_type_param: $ => choice(
  $.name,                                          // shorthand for `Name = ?`
  seq($.name, '=', $._type),                       // with default value
),
```

The surface tokens (`[`, `Name`, `=`, `Type`, `,`, `]`) coincide with those used by `sort_binding`, but the production is distinct because the semantic role differs (declaration of operation-local logical variables vs binding of sort parameters at instantiation). Sharing one CST node would invite confused lookups in the typer.

For call sites:

```js
operation_type_arg_list: $ => seq(
  '[',
  commaSep1($.operation_type_arg),
  ']',
),

operation_type_arg: $ => choice(
  $._type,                                         // positional
  seq($.name, '=', $._type),                       // named
),
```

Positional and named entries may be mixed in one list, with positional first — enforced by the typer, not the grammar.

For call sites, the existing `instantiation_term` already parses `Name[bindings]`. The change is allowing it before `(args)`:

```js
// New rule (or extension of existing call):
typed_call: $ => prec.left(2, seq(
  field('callee', $.instantiation_term),
  '(',
  optional($.arg_list),
  ')',
)),
```

Precedence ensures `Map[String, Int].empty()` (proposal 035) and `term_as_entity[WorkItem](t)` (this proposal) both parse, with the trailing token (`.` vs `(`) selecting the production.

## Converter / Loader Changes

`parse/ir.rs::Item::Operation`: add `type_params: Vec<TypeParam>` (where `TypeParam` mirrors `SortBinding` for symmetry with proposal 035).

`parse/convert.rs::convert_operation`: walk the optional `type_param_list` child and populate `type_params`. Reuses the existing `convert_sort_binding`.

`kb/load.rs::load_operation`:
1. Allocate a fresh `VarId` for each entry in `type_params`. Bind the name in the operation's local symbol scope.
2. Process `params`, `return_type`, `requires`, `ensures`, `effects` — references to declared type-param names resolve to the bound vars (same machinery as `sort T = ?` inside a sort body).
3. Implicit `?T` mentions whose name matches a declared parameter resolve to the *same* var (round-trip with the desugared form).

Call-site loading: when `convert_term` sees a `Name '[' bindings ']' '(' args ')'`, build an `Apply` term where the callee carries the type bindings as side-information consumed by the typer (parallel to how 035 handles `Map[K=String, V=Int].empty()`).

## Typer Changes

The typer already handles per-call type-parameter inference for implicit `?T` (the current `term_as_entity` works because of this). The new piece is consuming the explicit-bindings table:

- At a call site `op[bindings](args)`, seed the unification environment with the explicit bindings before running argument type-checking.
- Diagnose conflicts between explicit bindings and inferred ones (`op[T = Int](x)` where `x: String` and `op`'s param is `T` should error with both the explicit binding and the conflicting argument type cited).
- Report unresolved parameters at call sites with no explicit binding and no inference path, naming each unresolved parameter — the diagnostic should suggest the explicit form (`use op[T = ...]`).

## Migration

### Stdlib migration

A small, opportunistic update to make the explicit form available where it's clearest:

| File | Change |
|---|---|
| `stdlib/anthill/reflect/reflect.anthill:159` | `term_as_entity(t) -> Option[T = ?E]` → `term_as_entity[E](t) -> Option[E]`. |
| `stdlib/anthill/prelude/list.anthill` (and other collections) | Add explicit `[A, B]` / `[A]` to HOFs as they're added (most HOFs are not in the stdlib yet — green-field for this proposal). |
| `stdlib/anthill/prelude/{collection,iteration}.anthill` | Sort-level type params (`Element`, `Effect`) stay where they are. No change to existing sigs. |

Implicit-form signatures already in stdlib (e.g. `operation identity(x: ?T) -> ?T` if added) continue to work — they're equivalent to `operation identity[T](x: T) -> T`. Migration is opt-in per signature.

### Tests

- A fixture that calls `term_as_entity[WorkItem](t)` and verifies the result type pins to `WorkItem`.
- A fixture exercising `map[A, B, C, E]` over a List, verifying type-param inference fills A from the input, B from the function, C from the constructor, and E from the function's effect row (pure → `{}`; effectful → matching row).
- A negative fixture: `term_as_entity(t)` with no context — must produce a clear "unresolved type parameter" diagnostic.
- **Frame-inspection fixture** (covers `docs/design/operation-call-model.md` §"Operation type arguments"): a synthesized `operation foo[T](x: T) -> T` with body `x`. After pushing the frame for a call `foo[Int](42)`, inspect `frame.requirements` and assert:
  - Any sort-level entries (Self + sub-requires) precede the type-argument entries.
  - An entry keyed `T` exists with the type-value for `Int`.
  - A second call `foo[String]("hi")` in the same scope produces a fresh frame whose `T` entry holds `String` — the two calls do not share their `T` binding (per-call, contra sort instantiation).
  - The inferred form `foo(42)` produces a frame with the same `T = Int` content as the explicit form.

## Non-goals

- **Higher-rank polymorphism.** `operation g[F](f: F[A] -> F[B], ...) -> ...` — `F` as a type-constructor variable. Same boundary 035 already drew: HM stays rank-1.
- **Bounded type parameters at declaration site.** `operation sort[T: Ordered](xs: List[T]) -> List[T]` (Scala-style `T: Ordered`) would be a separate proposal. Today and after this proposal: bounds are expressed via `requires` on the operation.
- **First-class operations.** Treating an operation as a value, passing `term_as_entity` itself as an argument — separate concern (proposal 018 + a type-class shape for operations).
- **Type-parameter erasure rules.** Operation type arguments are carried in the call frame at the IR/eval layer (see `docs/design/operation-call-model.md` §"Operation type arguments"), the same way sort-level requirements are. Backends decide whether to elide them: Rust-side codegen monomorphizes and erases (same answer 035 gave for `Map[K, V]`); the interpreter and any backend that needs runtime type-driven dispatch keeps them. The frame layout is uniform; this proposal doesn't fix the erasure rule per backend.

## Out-of-scope follow-ups

- **Inference-quality diagnostics.** Once explicit and implicit forms compose with HOFs and `requires` chains, ambiguity reports may need polish (which parameter is unconstrained, where does it appear, what context could pin it). Tooling work, not blocking.
- **Sort-companion ↔ free-standing-op unification at the call site.** `Map[K, V].empty()` and `empty[K, V]()` are different surfaces today (one is sort-companion dispatch, the other is namespace call). They could share more machinery — orthogonal.
- **Operation-level variance annotations.** Variance lives at the sort level (035 §Variance). No analogue is needed at the operation level for the cases this proposal addresses.
- **The inference engine itself.** This proposal's bidirectional inference is hand-rolled in `check_apply_iter` (WI-379). Its principled home is typing-as-constraints solved over a **per-sort unification framework** (CLP) — `future/unification-framework.md`, the substrate WI-010 wants. Long-horizon; orthogonal to landing `[T]`.

## Acceptance

- `operation foo[A, B](x: A, y: B) -> Pair[A = A, B = B]` parses, loads, and type-checks. A unit test in `wi_tests.rs` exercises this directly.
- `term_as_entity[E](t: Term) -> Option[T = E]` replaces the `?E` workaround in `reflect.anthill`; existing WI-260 tests pass without modification (they already work at the call-site level — only the declaration prose tightens).
- A collection-`map` fixture with explicit `[A, B, C]` passes type-checking and exercises both inferred and explicit call forms.
- `cargo test` green across the workspace.
- `simplify` clean on the changed Rust files.

## Open questions

**OQ1.** *(closed — section above resolves this.)* Both positional and named call-site bindings are admitted; mixing positional-first then named is allowed per the same rule as `SortBinding` for sort instantiations. The recommended style is positional by default; named when skipping a leading parameter or when the call is part of a public surface where reordering robustness matters. No grammar-level restriction beyond positional-first ordering.

**OQ2.** *(closed — the section above resolves this.)* The two surfaces (`[T]` declaration with bare references vs. `?T` logical variables) are independent kernel features. An operation's author picks one. Mixing same-letter cases (`operation foo[T](x: ?T)`) is grammatically admissible but means two distinct vars (declared `T` and logical `?T`) — almost certainly an author mistake; a linter should flag it.

**OQ3.** *Defaults — useful or noise?* `operation foo[T = Int](x: T) -> T` means "T defaults to Int if neither the caller nor inference fills the slot." This falls out of the unified shape (the `Name = Type` form of `SortBinding` already means this for sort instantiations); it costs nothing to allow grammatically. Open question is only whether any stdlib operation should use it for the first landing. The use case is thin — most call sites either have enough context or want explicit. Recommend: allow grammatically, no stdlib adoption in the first landing, revisit if a concrete driver appears.

**OQ4.** *(specified elsewhere — cross-reference, not open here.)* Two pieces this proposal leans on are detailed outside it: **cross-sort parameter inference** (binding `[T]` from a `List[Int]` argument used where a `Stream[T]` is expected, via provider admissibility) — **WI-379**; and **projection cross-dependency strictness** (resolution order, cycle / missing-member / abstract-receiver loud errors) — **WI-376** and [`docs/design/type-parameter-scoping.md`](../design/type-parameter-scoping.md).
