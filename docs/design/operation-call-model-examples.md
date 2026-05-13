# Operation-call model: worked examples

## Status: Concrete walk-through of example translations under the chosen IR (revised model — see `operation-call-model.md` §"Revision note")

## Companion to: `operation-call-model.md` (decision), `operation-call-model-brainstorm.md` (exploration)

This doc takes representative examples from the brainstorm and shows how each translates from source to elaborated IR — the `_within` apply / lambda forms with a single-entry `requirements` channel and tree expansion at frame push (Model 1).

Conventions used below:

- The elaborator inserts requirement params into each op's signature with synthesized symbol names (`__req_self_<spec>`, plus one named param per the impl's `requires`-chain entry). The body reads them via ordinary `var_ref(<name>)` — same mechanism as regular value-level params.
- **`apply_within(fn, args, requirements = [<single dict expr>])`** — every call's `requirements` channel has exactly one entry under v0: the dispatching `ResolvedSortNode` (dictionary). The callee's frame is populated by expanding the dict's sub-tree at push time.
- **`requirement_at_sort(dict_expr, k)`** projects the k-th positional sub-instance out of a dictionary. Used at call sites when sourcing the dispatching dict from a wrapping dictionary's sub-tree, or inside `construct_requirement`. NOT used inside bodies in the common case (sub-instances are already bound by name at frame push).
- **`construct_requirement(impl, [sub_dicts])`** builds a dictionary value with `functor = impl` and positional sub-instances `[sub_dicts]`. Used for Pin-now sub-tree literals.
- **Defer dispatch**: `fn` is the qualified spec-op symbol; the interpreter reads `requirements[0]`'s `sort` at runtime and looks up `sort_ops_table[sort][op_short]` for the impl op (sort symbols carry their ops table; the lookup is direct, not name-resolution).
- **Pin-now / Direct**: `fn` is an impl-op qualified symbol; same single-entry channel shape, just no runtime dispatch.
- **"Self bound"** = a body that calls a same-sort spec op (e.g., `Eq.neq` calling `eq`). The dispatching dictionary serves both as the body's Self and as the dispatching target for the inner spec-op call.
- IR is rendered in a slightly informal sugared form for readability; actual `Term::Fn { functor: apply_within, named_args: [...] }` shapes are larger but mechanical.
- Each example shows: source, the per-op requirements-tree derived by body walk, the elaborated body, and the call-site translations from a hypothetical caller.

**Self-recursion handling**:

- **Impl-side self-recursion** (an impl's body calling its own op recursively) → emit a **direct call by impl op name**: `apply_within(fn = EqList.eq, args, requirements = [var_ref(__req_self_eqlist)])`. The recursive frame's Self is forwarded; no cycle.
- **Spec default body needing the dispatching impl** (e.g., `Eq.neq`'s default calling `eq`) → body emits `apply_within(fn = Eq.eq, ..., requirements = [var_ref(__req_self_eq)])`, dispatching through its own Self dictionary.

Dictionary values are arena-allocated with refcount and never form cycles.

## Example 1 — Basic case (B with `requires A`, two A impls)

### Source

```anthill
sort A
  sort T = ?
  operation foo(x: T) -> String   -- spec op (no body)
end

sort B
  sort T = ?
  requires A
  operation bar(x: T) -> String =
    String.concat("B", foo(x))
end

sort C1
  sort T = ?
  fact A[T = T]
  operation foo(x: T) -> String = "c1"
end

sort C2
  fact A[T = String]
  operation foo(x: String) -> String = String.concat("c2", x)
end
```

### Per-op requirements-tree

For each op-of-B body, the elaborator computes a single `RequiresNode` tree rooted at B's spec sort, with sub-nodes for B's declared `requires`:

```
B-tree = RequiresNode(B, [
  RequiresNode(A, [])
])
```

`B.bar`'s inserted requirement params: `__req_self_b` (the B-dict), `__req_a` (B's A sub-instance).

### Elaborated body of `B.bar`

```
params:       [x]
requirements: [__req_self_b : B, __req_a : A]
body: apply_within(
  fn = String.concat,
  args = [
    string_lit("B"),
    apply_within(fn = A.foo, args = [x], requirements = [var_ref(__req_a)])
  ],
  requirements = []     -- String.concat has no requires
)
```

The body reads `__req_a` via ordinary `var_ref`. No projection — the binding is already on the frame, expanded from `__req_self_b.sub_requires[0]` at frame push.

### Call-site translations

A caller D that satisfies B at T=String and resolves A[T=String] via C2:

```anthill
sort D
  fact B[T = String]
  fact A[T = String]    -- via C2
  operation use_bar(s: String) -> String = bar(s)
end
```

`D.use_bar`'s body call `bar(s)`. The dispatching dictionary is statically resolved (Pin-now) — a B-impl dictionary with C2 bundled inside:

```
apply_within(
  fn = B.bar,
  args = [s],
  requirements = [construct_requirement(BImpl_String, [
    construct_requirement(C2, [])    -- the A sub-instance, here C2
  ])]
)
```

A different D2 that uses C1 (any T):

```anthill
sort D2
  fact B[T = Int]      -- via C1 with T = Int
end
```

```
apply_within(
  fn = B.bar,
  args = [42],
  requirements = [construct_requirement(BImpl_Int, [
    construct_requirement(C1, [])
  ])]
)
```

When the interpreter enters `B.bar`'s frame:
- `__req_self_b` is bound to the BImpl_* dict
- `__req_a` is bound to the C2 (or C1) dict — sourced from `__req_self_b.sub_requires[0]`
- Body's `apply_within(fn = A.foo, …, requirements = [var_ref(__req_a)])` dispatches via the A-dict's functor → resolves to C2.foo or C1.foo

### Notes

- `B.bar`'s body has ONE call to a spec op (`foo`), and B has ONE `requires` (A). The frame has TWO requirement bindings (`__req_self_b` + `__req_a`).
- The `apply_within` channel at the call site has ONE entry — the dispatching B-dict.
- Different callers fill that one entry with different dicts (BImpl_String, BImpl_Int) carrying different sub-impls (C1, C2).
- The body itself never changes; only the caller's dispatching dict varies.

## Example 2 — Default method override (Eq with derived `neq`)

### Source

```anthill
sort Eq
  sort T = ?
  operation eq(a: T, b: T) -> Bool                       -- spec op (no body)
  operation neq(a: T, b: T) -> Bool = not(eq(a, b))      -- default body
end

sort IntEq
  fact Eq[T = Int]
  operation eq(a: Int, b: Int) -> Bool = ...
end
```

### Per-op requirements-tree

Eq has no `requires` of its own. Eq.neq's body calls `eq` (a same-sort spec op):

```
Eq-tree = RequiresNode(Eq, [])     -- Eq has no requires
```

`Eq.neq`'s inserted requirement params: just `__req_self_eq` (the dispatching Eq dict, also serves the body's `eq` call).

### Elaborated body of `Eq.neq`

```
params:       [a, b]
requirements: [__req_self_eq : Eq]
body: apply_within(
  fn = not,
  args = [apply_within(fn = Eq.eq, args = [a, b], requirements = [var_ref(__req_self_eq)])],
  requirements = []
)
```

The same `__req_self_eq` serves as both Self and as the dispatching dict for the inner `Eq.eq` call (Self-bound pattern).

### Call-site translation

Caller calling `neq(x, y)` for `x, y : Int` (IntEq satisfies Eq[T=Int]):

```
apply_within(
  fn = Eq.neq,        -- spec-op (Defer), dispatched to inherited default body
  args = [x, y],
  requirements = [construct_requirement(IntEq, [])]   -- Pin-now IntEq dict
)
```

Inside `Eq.neq`'s body, `var_ref(__req_self_eq)` evaluates to the IntEq dict. The inner `apply_within(fn = Eq.eq, …, requirements = [var_ref(__req_self_eq)])` resolves at runtime: `<IntEq dict>.functor = IntEq` → `IntEq.eq`.

### Notes

- Self-bound: a single requirement param serves two roles — Self for the body, and dispatching dict for the inner same-spec call.
- Common pattern in stdlib: `Eq`, `Ordered`, `Numeric` all have default ops calling primitive ones of the same spec.

## Example 3 — Diamond dependency

### Source

```anthill
sort A
  sort T = ?
  operation foo(x: T) -> String
end

sort B
  sort T = ?
  requires A
  operation use_a_in_b(x: T) -> String = foo(x)
end

sort C
  sort T = ?
  requires A
  operation use_a_in_c(x: T) -> String = String.concat("c-", foo(x))
end

sort D
  fact B[T = Int]
  fact C[T = Int]
  fact A[T = Int]      -- D supplies ONE consistent A; coherence-checked
  operation main(x: Int) -> String =
    String.concat(use_a_in_b(x), use_a_in_c(x))
end
```

### Per-op requirements-trees

- `B.use_a_in_b`: tree `RequiresNode(B, [RequiresNode(A, [])])`. Params: `__req_self_b`, `__req_a`.
- `C.use_a_in_c`: tree `RequiresNode(C, [RequiresNode(A, [])])`. Params: `__req_self_c`, `__req_a`.
- `D.main`: tree `RequiresNode(D, [])` (D's body uses no spec ops). Params: `__req_self_d` only.

### Coherence resolution at D's load time

D claims `fact B[T = Int]` and `fact C[T = Int]`. Both require A. D's `fact A[T = Int]` resolves to some impl (call it IntA). The same IntA is used inside both the B-impl and C-impl that D supplies — coherence at the diamond's join point.

### Elaborated body of `D.main`

```
params:       [x]
requirements: [__req_self_d : D]
body: apply_within(
  fn = String.concat,
  args = [
    apply_within(
      fn = B.use_a_in_b,
      args = [x],
      requirements = [construct_requirement(BImpl_Int, [
        construct_requirement(IntA, [])
      ])]
    ),
    apply_within(
      fn = C.use_a_in_c,
      args = [x],
      requirements = [construct_requirement(CImpl_Int, [
        construct_requirement(IntA, [])
      ])]
    )
  ],
  requirements = []
)
```

Both nested calls construct fresh dictionaries (Pin-now), each bundling the same IntA. After hash-consing, the inner `construct_requirement(IntA, [])` resolves to a single canonical IntA value — used twice.

### Notes

- Coherence is enforced at D's load: ambiguous A would reject; missing A would reject.
- At runtime, both inner calls receive a dict whose A sub-instance is the same IntA.
- The IntA value is constructed once and refcount-shared between BImpl_Int's and CImpl_Int's sub-trees.

## Example 4 — Cross-bound (B requires both Eq and Ordered)

### Source

```anthill
sort B
  sort T = ?
  requires Eq[T = T]
  requires Ordered[T = T]
  operation sort_pair(a: T, b: T) -> Pair[A = T, B = T] =
    if eq(a, b) then pair(a, b)
    else if lt(a, b) then pair(a, b)
    else pair(b, a)
end
```

### Per-op requirements-tree

B's requires-chain: [Eq, Ordered] (declaration order). Tree:

```
B-tree = RequiresNode(B, [
  RequiresNode(Eq, []),
  RequiresNode(Ordered, [])
])
```

`B.sort_pair`'s inserted requirement params: `__req_self_b`, `__req_eq`, `__req_ord`.

### Elaborated body of `B.sort_pair`

```
params:       [a, b]
requirements: [__req_self_b : B, __req_eq : Eq, __req_ord : Ordered]
body: if_expr(
  cond = apply_within(fn = Eq.eq, args = [a, b], requirements = [var_ref(__req_eq)]),
  then = apply_within(fn = pair, args = [a, b], requirements = []),
  else = if_expr(
    cond = apply_within(fn = Ordered.lt, args = [a, b], requirements = [var_ref(__req_ord)]),
    then = apply_within(fn = pair, args = [a, b], requirements = []),
    else = apply_within(fn = pair, args = [b, a], requirements = [])
  )
)
```

Two distinct named bindings: `__req_eq` for the Eq dictionary, `__req_ord` for the Ordered dictionary. Both populated from `__req_self_b`'s sub-tree at frame push.

### Call-site translation

Caller D with `fact B[T = Int]` resolving Eq[Int] (IntEq), Ordered[Int] (IntOrdered):

```
apply_within(
  fn = B.sort_pair,
  args = [x, y],
  requirements = [construct_requirement(BImpl_Int, [
    construct_requirement(IntEq, []),
    construct_requirement(IntOrdered, [])
  ])]
)
```

At frame push, the runtime expands the B-dict:
- `__req_self_b` = BImpl_Int dict
- `__req_eq` = IntEq dict (from sub_requires[0])
- `__req_ord` = IntOrdered dict (from sub_requires[1])

### Notes

- Multi-bound: the requires-chain has length 2 → 3 named bindings on the frame (Self + 2 sub-instances).
- The body's `var_ref(__req_eq)` and `var_ref(__req_ord)` are direct local lookups — no projection.
- The `apply_within` channel always has one entry (the dispatching B-dict). The 2-vs-3 question (sub-instance count) is hidden inside the dictionary tree.

## Example 5 — Monad transformer chain (instance chains + lambda requirement capture)

### Source

```anthill
sort Monad
  sort M = ?
  operation pure(x: ?A) -> M[T = ?A]                          -- spec op
  operation bind(m: M[T = ?A], f: ?A -> M[T = ?B]) -> M[T = ?B]   -- spec op

  operation mapM(f: ?A -> M[T = ?B], xs: List[T = ?A]) -> M[T = List[T = ?B]] =
    match xs
      case nil() -> pure(nil())
      case cons(x, rest) ->
        bind(f(x), \y ->
          bind(mapM(f, rest), \ys ->
            pure(cons(y, ys))))
end

fact Monad[M = Option]                                              -- concrete instance

fact Monad[M = StateT[S = ?S, M = ?M]] :- Monad[M = ?M]            -- conditional chain
```

### Per-op requirements-tree (Monad.mapM)

Monad has no `requires` of its own. mapM's body uses same-sort spec ops (pure, bind, mapM):

```
Monad-tree = RequiresNode(Monad, [])
```

`Monad.mapM`'s inserted requirement param: `__req_self_monad` (Self-bound).

### Elaborated body of `Monad.mapM`

```
params:       [f, xs]
requirements: [__req_self_monad : Monad]
body: match_expr(
  scrutinee = xs,
  arms = [
    arm(pattern = nil_pat,
        body = apply_within(
          fn = Monad.pure,
          args = [nil()],
          requirements = [var_ref(__req_self_monad)]
        )),
    arm(pattern = cons_pat(x, rest),
        body = apply_within(
          fn = Monad.bind,
          args = [
            apply_within(fn = f, args = [x], requirements = []),
            lambda_within(
              params = [y],
              body = apply_within(
                fn = Monad.bind,
                args = [
                  apply_within(
                    fn = Monad.mapM,             -- recursive call
                    args = [f, rest],
                    requirements = [var_ref(__req_self_monad)]
                  ),
                  lambda_within(
                    params = [ys],
                    body = apply_within(
                      fn = Monad.pure,
                      args = [cons(y, ys)],
                      requirements = [var_ref(__req_self_monad)]
                    ),
                    requirements = [var_ref(__req_self_monad)]
                  )
                ],
                requirements = [var_ref(__req_self_monad)]
              ),
              requirements = [var_ref(__req_self_monad)]
            )
          ],
          requirements = [var_ref(__req_self_monad)]
        ))
  ]
)
```

Three things this example showcases:

1. **Same-requirement multi-call**: five same-spec calls all read `var_ref(__req_self_monad)`. Hash-consing deduplicates the var_ref TermIds; no separate hoist pass needed.
2. **Recursive call passes Self forward**: `mapM(f, rest)` recursively calls itself; the recursive frame's `__req_self_monad` is bound to the same dictionary.
3. **Lambda requirement capture**: each `\y -> …` and `\ys -> …` captures `__req_self_monad` via `lambda_within(..., requirements = [var_ref(__req_self_monad)])`. The expression evaluates to the dict at construction time; stored in `closure.requirements`. When the lambda is invoked (via `bind`), the new frame's `__req_self_monad` is populated from the closure's snapshot.

### Conditional instance: StateT chain

```anthill
fact Monad[M = StateT[S = ?S, M = ?M]] :- Monad[M = ?M]

operation pure(x) = ...    -- StateT's pure body
operation bind(m, f) = ... -- StateT's bind body, uses inner M's bind/pure
```

`StateTMonad.bind`'s body uses inner M's bind. So StateTMonad has its own `requires`: `[Monad[M = ?M]]`. Its requirements-tree:

```
StateTMonad-tree = RequiresNode(StateTMonad, [
  RequiresNode(Monad, [])    -- the inner monad
])
```

Inserted requirement params: `__req_self_statet`, `__req_inner_monad`.

`StateTMonad.bind`'s body uses `var_ref(__req_inner_monad)` to dispatch inner M's `bind`/`pure`.

### Resolution chain at use site

Some caller has a value of type `StateT[Int, Option, X]` and calls `bind` on it.

- SLD synthesis: want `Monad[StateT[Int, Option]]`. Match conditional `Monad[StateT[?S, ?M]] :- Monad[?M]` with `?S = Int, ?M = Option`. Subgoal: `Monad[Option]`. Find: `fact Monad[M = Option]` → OptionMonad.
- Pin-now construction:
  ```
  construct_requirement(StateTMonad, [
    construct_requirement(OptionMonad, [])
  ])
  ```
  StateTMonad wraps OptionMonad as its one bundled sub-instance.
- At the caller's `bind` call site:
  ```
  apply_within(
    fn = Monad.bind,
    args = [m, f],
    requirements = [construct_requirement(StateTMonad, [
      construct_requirement(OptionMonad, [])
    ])]
  )
  ```
- When StateTMonad's `bind` body is entered, the frame has:
  - `__req_self_statet` = the StateTMonad dict
  - `__req_inner_monad` = the OptionMonad dict (from StateTMonad.sub_requires[0])

Inside, calls to inner M's bind look like `apply_within(fn = Monad.bind, …, requirements = [var_ref(__req_inner_monad)])` — dispatching through OptionMonad.

### Notes

- The monad-transformer pattern works because each level's dictionary bundles exactly its direct sub-requires; deeper resolutions live in deeper frames.
- `lambda_within(..., requirements = [var_ref(__req_self_monad)])` is essential: monadic continuations would lose their Monad scope without capture.
- The recursive `mapM(f, rest)` call forwards `var_ref(__req_self_monad)` — same dictionary, same frame requirements at the recursive level.

## Example 6 — Phantom-only type-param

### Source

```anthill
sort Tagged
  sort Tag = ?       -- never used in op bodies
  sort T = ?
  entity tagged(v: T)
  operation unwrap(x: Tagged) -> T = match x case tagged(v) -> v
end

sort UserId
  fact Tagged[Tag = User, T = Int]
end

sort PostId
  fact Tagged[Tag = Post, T = Int]
end
```

### Per-op requirements-tree

`Tagged.unwrap` doesn't call any spec ops. Tagged has no `requires`. Tree:

```
Tagged-tree = RequiresNode(Tagged, [])
```

Inserted requirement param: `__req_self_tagged` (could also be omitted if the body doesn't use Self — see Notes).

### Elaborated body

```
params:       [x]
requirements: [__req_self_tagged : Tagged]    -- present by convention; body doesn't use it
body: match_expr(
  scrutinee = x,
  arms = [arm(pattern = tagged_pat(v), body = var_ref(v))]
)
```

### Notes

- Phantom params (Tag here) don't appear in the requirements-tree because they don't drive any spec-op dispatch.
- If `Tagged.unwrap`'s body genuinely doesn't reference Self, the elaborator could elide `__req_self_tagged` and pass `requirements = []`. Implementations that always include Self for uniformity are also valid.
- Both UserId.unwrap and PostId.unwrap could share the same `unwrap` body (they DO, since it's inherited from Tagged).

## Example 7 — Conditional default (`Eq[List[T]] :- Eq[T]`)

### Source

```anthill
sort EqList
  fact Eq[T = List[T = ?A]] :- Eq[T = ?A]

  operation eq(xs: List[T = ?A], ys: List[T = ?A]) -> Bool =
    match (xs, ys)
      case (nil(), nil()) -> true
      case (cons(x, rest_x), cons(y, rest_y)) ->
        and(eq(x, y), eq(rest_x, rest_y))   -- inner eq: Eq[T = ?A]; outer recursion: Eq[T = List[?A]]
      case _ -> false
end
```

### Per-op requirements-tree

EqList's `requires` chain: `[Eq[T = ?A]]` (from the conditional clause's subgoal). Tree:

```
EqList-tree = RequiresNode(EqList, [
  RequiresNode(Eq, [])    -- the inner element's Eq
])
```

Inserted requirement params for `EqList.eq`: `__req_self_eqlist`, `__req_inner_eq`.

The body has TWO eq calls:
1. `eq(x, y)` on `?A` — dispatches through `__req_inner_eq`.
2. `eq(rest_x, rest_y)` on `List[?A]` — self-recursion, direct call to `EqList.eq`, forwarding `__req_self_eqlist`.

### Elaborated body

```
params:       [xs, ys]
requirements: [__req_self_eqlist : Eq[List], __req_inner_eq : Eq]
body: match_expr(
  ...
  arms with cons-cons branch:
    apply_within(
      fn = and,
      args = [
        -- inner element call: Defer dispatch via the element's Eq
        apply_within(fn = Eq.eq, args = [x, y], requirements = [var_ref(__req_inner_eq)]),
        -- self-recursion: Direct call by impl name, forward Self
        apply_within(fn = EqList.eq, args = [rest_x, rest_y], requirements = [var_ref(__req_self_eqlist)])
      ],
      requirements = []
    )
  ...
)
```

### Call-site translation

Caller calling `eq(xs, ys)` for `xs, ys : List[T = Int]`:

- SLD synthesis: want `Eq[T = List[T = Int]]`. Match conditional with `?A = Int`. Subgoal: `Eq[T = Int]` → IntEq.
- Pin-now construction at the call site:
  ```
  apply_within(
    fn = Eq.eq,                                          -- Defer through the spec
    args = [xs, ys],
    requirements = [construct_requirement(EqList, [
      construct_requirement(IntEq, [])
    ])]
  )
  ```

At frame push for `EqList.eq`:
- `__req_self_eqlist` = the EqList dict
- `__req_inner_eq` = the IntEq dict (from `__req_self_eqlist.sub_requires[0]`)

The body then:
- `apply_within(fn = Eq.eq, args = [x, y], requirements = [var_ref(__req_inner_eq)])` → dispatches IntEq.eq.
- `apply_within(fn = EqList.eq, args = [rest_x, rest_y], requirements = [var_ref(__req_self_eqlist)])` → recurses with the same EqList dict.

### Notes

- The body's two requirement bindings (`__req_self_eqlist`, `__req_inner_eq`) come from the dispatching dictionary's sub-tree expansion at frame push. Body uses them by name.
- The single-entry channel carries the full tree; the runtime does the expansion.
- Self-recursion forwards Self via `var_ref(__req_self_eqlist)` — no cycle in the dictionary tree.

## Example 8 — Recursive instance chain (`Eq[List[List[X]]]`)

This example extends Example 7 by one nesting level — the SAME body and the SAME impl, applied recursively at construction time.

### Setup

(Same `EqList` sort as Example 7, plus a base impl `EqX` for some sort `X`.)

Concrete query: caller has `xss, yss : List[T = List[T = X]]` and an `EqX` impl in scope; calls `eq(xss, yss)`.

### SLD synthesis chain

Caller resolving `Eq[T = List[T = List[T = X]]]`:

| Step | Goal | Match | Resolved as |
|---|---|---|---|
| 1 | `Eq[List[List[X]]]` | conditional with `?A = List[X]` → subgoal `Eq[List[X]]` | (descend) |
| 2 | `Eq[List[X]]` | conditional with `?A = X` → subgoal `Eq[X]` | (descend) |
| 3 | `Eq[X]` | base fact → `EqX` | leaf |

### Pin-now construction

```
construct_requirement(EqList, [
  construct_requirement(EqList, [
    construct_requirement(EqX, [])
  ])
])
```

This nested literal evaluates at runtime to a tree of arena handles:

```
env_X    : { functor: EqX,    sub_requires: [] }
env_LX   : { functor: EqList, sub_requires: [env_X] }
env_LLX  : { functor: EqList, sub_requires: [env_LX] }
```

No cycles: each dictionary's `sub_requires` references only earlier-constructed dicts.

### Call-site IR

```
apply_within(
  fn = Eq.eq,
  args = [xss, yss],
  requirements = [construct_requirement(EqList, [
    construct_requirement(EqList, [
      construct_requirement(EqX, [])
    ])
  ])]
)
```

### Runtime trace (one cons-cons step at the outer level)

The body of EqList.eq executes for outer `xss = cons(xs, rest_xss)`, `yss = cons(ys, rest_yss)`. Each element xs / ys is itself `List[X]`.

1. **Frame for outer call**: `__req_self_eqlist = env_LLX`, `__req_inner_eq = env_LX` (expanded from env_LLX.sub_requires).

2. **Inner-element call** `eq(xs, ys)` where `xs, ys : List[X]`:
   ```
   apply_within(
     fn = Eq.eq,
     args = [xs, ys],
     requirements = [var_ref(__req_inner_eq)]    -- env_LX
   )
   ```
   At runtime: dispatching dict = env_LX; functor = EqList → resolves EqList.eq. New frame: `__req_self_eqlist = env_LX`, `__req_inner_eq = env_X` (from env_LX.sub_requires[0]).

3. **One more level down**: this body's inner-element call `eq(x, y)` where `x, y : X`:
   ```
   apply_within(fn = Eq.eq, args = [x, y],
                requirements = [var_ref(__req_inner_eq)])     -- env_X
   ```
   At runtime: dispatching dict = env_X; functor = EqX → resolves EqX.eq. EqX.eq's body runs on Xs.

4. **Self-recursion paths** (at each level):
   - Outer-level recursion on `rest_xss, rest_yss`:
     ```
     apply_within(fn = EqList.eq, args = [rest_xss, rest_yss],
                  requirements = [var_ref(__req_self_eqlist)])    -- forward env_LLX
     ```
   - Inner-level recursion on `rest_xs, rest_ys`:
     ```
     apply_within(fn = EqList.eq, args = [rest_xs, rest_ys],
                  requirements = [var_ref(__req_self_eqlist)])    -- forward env_LX (the inner frame's Self)
     ```

The body code is identical in every frame; only the dictionary values bound to `__req_self_eqlist` / `__req_inner_eq` differ.

### Why this works without cycles

- Each `construct_requirement` builds a dictionary pointing only to **already-constructed** sub-instances. Arena handles flow upward, never inward.
- Self-recursion uses the impl-op name (`EqList.eq`), forwarding the current Self; no Self-reference inside any dictionary.

### Notes

- The chain depth equals the type's nesting depth. Each level adds one outer `construct_requirement` wrapping the inner.
- The single body of EqList.eq is reused at every level; per-frame `__req_self_eqlist` / `__req_inner_eq` differ.

## Example 9 — Same sort at two type-args (`requires Ordered[A]` and `requires Ordered[B]`)

When a sort has two `requires` clauses naming the **same sort but at different type-args**, they're treated as two distinct entries in the requires-chain.

### Source

```anthill
sort Pair
  sort A = ?
  sort B = ?
  requires Ordered[T = A]
  requires Ordered[T = B]

  entity pair(a: A, b: B)

  operation cmp(p1: Pair[A=A, B=B], p2: Pair[A=A, B=B]) -> Int =
    let ca = compare(p1.a, p2.a)         -- A-typed comparison
    in if ca != 0
       then ca
       else compare(p1.b, p2.b)          -- B-typed comparison
end
```

### Per-op requirements-tree

```
Pair-tree = RequiresNode(Pair, [
  RequiresNode(Ordered, []),    -- for A
  RequiresNode(Ordered, [])     -- for B
])
```

Inserted requirement params: `__req_self_pair`, `__req_ord_a`, `__req_ord_b`.

### Elaborated body

```
params:       [p1, p2]
requirements: [__req_self_pair : Pair, __req_ord_a : Ordered[A], __req_ord_b : Ordered[B]]
body: let_expr(
  binding = ca,
  rhs = apply_within(
    fn = Ordered.compare,
    args = [p1.a, p2.a],
    requirements = [var_ref(__req_ord_a)]
  ),
  body = if_expr(
    cond = apply_within(fn = ne, args = [ca, 0], requirements = []),
    then = ca,
    else = apply_within(
      fn = Ordered.compare,
      args = [p1.b, p2.b],
      requirements = [var_ref(__req_ord_b)]
    )
  )
)
```

Two distinct named bindings (`__req_ord_a` and `__req_ord_b`). They share a sort name (Ordered) but at different type-args.

### Call-site translation

Caller D using `Pair[A=Int, B=String]`:

```
apply_within(
  fn = Pair.cmp,
  args = [p1, p2],
  requirements = [construct_requirement(PairImpl_Int_String, [
    construct_requirement(IntOrdered, []),
    construct_requirement(StringOrdered, [])
  ])]
)
```

At frame push:
- `__req_self_pair` = the PairImpl_Int_String dict
- `__req_ord_a` = IntOrdered (from sub_requires[0])
- `__req_ord_b` = StringOrdered (from sub_requires[1])

The body then dispatches Ordered.compare twice — first through IntOrdered, then through StringOrdered.

### Notes

- Same-sort-name bounds aren't unusual — any sort parametric in multiple types (Pair, Map, BiFunctor, …) will frequently have multiple instances of the same constraint sort.
- Each named binding is independent: caller can pass impls for entirely unrelated types (Int + String).
- Compare with Example 4: that had **different sort names** (Eq + Ordered) at the same T. This example has the **same sort name** (Ordered) at different type-args. Both produce length-2 requires-chains; the difference is in the dictionary's sub-instance functors.

## Summary observations

Across all nine examples, the pattern is consistent:

- **Every `apply_within` has exactly one entry in its `requirements` channel** — the dispatching `ResolvedSortNode`. Sub-instances are bundled inside.
- **Spec-op calls** become either:
  - `apply_within(fn = ImplOp, args, requirements = [<dict>])` — Pin-now / Direct, `fn` is the resolved impl-op.
  - `apply_within(fn = SpecOp, args, requirements = [<dict>])` — Defer, `fn` is the spec-op; the interpreter resolves via the dictionary's functor at runtime.
- **Self-recursion in conditional impls** uses Direct dispatch with the impl's own qualified op name, forwarding Self via `var_ref`.
- **Multi-bound ops** have requires-trees with multiple sub-nodes; the elaborator synthesizes one named binding per sub-node, all populated from the dispatching dict's sub-tree at frame push.
- **Conditional instances** materialize as chained `construct_requirement` literals at Pin-now sites; the runtime arena holds one slot per constructed level.
- **Lambdas** capture the current Self (and any sub-instances they reference) at construction time; closures replay the captured scope on invocation.
- **Recursive calls** forward the current frame's Self via `var_ref(__req_self_<sort>)` — the recursive frame runs in the same dictionary scope.

The IR translation is mechanical given:
1. Per-op requirements-tree (computed by body walk + fixed-point for mutual recursion) and the elaborator's name synthesis per node.
2. The canonical ordering of sub-requires (**declaration order in source**).
3. SLD synthesis at each call site to resolve dictionaries from the caller's `fact …` declarations and construct them via `construct_requirement`.

The runtime is uniform: `requirements[0]` of any `apply_within` evaluates to one dictionary; the callee's frame is populated by Self + sub-tree expansion. The body reads requirement params via `var_ref(<synthesized_name>)` — same as ordinary locals. No `requirement_at_current` primitive, no fn-position requirement form. `requirement_at_sort` and `construct_requirement` appear at call sites (and inside `construct_requirement` nesting) — not inside bodies.
