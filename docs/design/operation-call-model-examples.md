# Operation-call model: worked examples

## Status: Concrete walk-through of example translations under the chosen IR

## Companion to: `operation-call-model.md` (decision), `operation-call-model-brainstorm.md` (exploration)

This doc takes representative examples from the brainstorm and shows how each translates from source to elaborated IR — the `_within` apply / lambda forms with explicit requirement slots.

Conventions used below:

- `requirement_at_current(i)` reads `frame.requirements[i]` (the i-th requirement in this body's frame).
- `requirement_at_current(i, op_short)` is the fn-position form: dispatch `op_short` through `frame.requirements[i]`.
- `requirement_at_sort(requirement_expr, k)` projects into an requirement value to read its k-th bundled requirement (used at dispatch sites to forward an requirement value's deps onward — see Example 8).
- IR is rendered in a slightly informal sugared form for readability; actual `Term::Fn { functor: apply_within, named_args: [...] }` shapes are larger but mechanical.
- Each example shows: source, the per-op requirements derived by body walk, the elaborated body, and the call-site translations from a hypothetical caller.

**Self-recursion handling**:

- **Impl-side self-recursion** (an impl's body calling its own op recursively, e.g., `EqList.eq` on the tail) → emit a **direct call by impl op name**: `apply_within(fn = EqList.eq, args = [...], requirements = [requirement_at_current(0), ...])`. No Self entry in `requirements`. No cycles in requirement values.
- **Spec default body needing the dispatching impl** (e.g., `Eq.neq`'s default calling `eq`) → caller passes the impl requirement value into the body's `frame.requirements[0]` and the body dispatches via `requirement_at_current(0, "eq")`. The impl requirement value isn't self-referential, so no cycles.

Under this discipline, requirement values are arena-allocated with refcount and never form cycles.

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

### Per-op requirements (after body walk)

| Op | requirements | Notes |
|---|---|---|
| `A.foo` | `[]` | spec op (no body) |
| `B.bar` | `[A]` | body calls foo (an A op) |
| `C1.foo` | `[]` | impl op, no spec calls |
| `C2.foo` | `[]` | impl op, no spec calls |

### Elaborated bodies

`B.bar`:

```
requirements: [A]
body: apply_within(
  fn = String.concat,
  args = [
    string_lit("B"),
    apply_within(fn = requirement_at_current(0, "foo"), args = [x], requirements = [])
  ],
  requirements = []
)
```

`requirement_at_current(0)` reads `frame.requirements[0]`, which the caller filled with the resolved A impl. Dispatch on the value's functor finds the right `foo`.

### Call-site translations

A caller D that satisfies B at T=String and resolves A[T=String] via C2:

```anthill
sort D
  fact B[T = String]
  fact A[T = String]    -- via C2
  operation use_bar(s: String) -> String = bar(s)
end
```

`D.use_bar`'s body call `bar(s)`:

```
apply_within(
  fn = B.bar,
  args = [s],
  requirements = [<C2 entity-value>]    -- typer resolves D's A[T=String] → C2
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
  requirements = [<C1 entity-value with T binding>]
)
```

The requirement value is sort-tagged (`Value::Requirement(handle)` where `arena[handle].functor = C1`); inside `B.bar`, `requirement_at_current(0, "foo")(x)` dispatches on the value's functor.

### Notes

- `B.bar`'s body has ONE call to a spec op (`foo`), so `requirements = [A]` is length 1.
- Different callers fill the same slot with different impls (C1 or C2) based on their own resolved requirement.
- The body itself never changes; only the caller's `requirements` slot varies.

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

### Per-op requirements

| Op | requirements | Notes |
|---|---|---|
| `Eq.eq` | `[]` | spec op |
| `Eq.neq` | `[Eq]` | default body uses `eq` (a same-sort spec op) — Self bound |
| `IntEq.eq` | `[]` | impl op, no calls to specs |

### Elaborated body of `Eq.neq`

```
requirements: [Eq]   -- Self bound: "this Eq instance"
body: apply_within(
  fn = not,
  args = [apply_within(fn = requirement_at_current(0, "eq"), args = [a, b], requirements = [])],
  requirements = []
)
```

The Self bound expresses "neq's body needs the Eq instance dispatching against." When IntEq inherits the default `neq`, the requirement value at index 0 is IntEq itself.

### Call-site translation

Caller calling `neq(x, y)` for `x, y : Int` (IntEq satisfies Eq[T=Int]):

```
apply_within(
  fn = Eq.neq,        -- dispatched from spec name to inherited default
  args = [x, y],
  requirements = [<IntEq entity-value>]
)
```

Inside `Eq.neq`'s body, `requirement_at_current(0, "eq")(a, b)` dispatches to `IntEq.eq` because `frame.requirements[0]`'s functor is IntEq.

### Notes

- This is the "Self-dispatch" case. `Eq.neq` doesn't have an explicit `requires` clause, but its body refers to `eq` (a same-sort spec op), which implicitly bounds Self to satisfy Eq.
- Per-op requirements is derived from body even when Self is implicit.
- Common pattern in stdlib: `Eq`, `Ordered`, `Numeric` all have default ops calling primitive ones.

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

### Per-op requirements

| Op | requirements | Notes |
|---|---|---|
| `B.use_a_in_b` | `[A]` | body calls foo |
| `C.use_a_in_c` | `[A]` | body calls foo |
| `D.main` | `[]` | calls use_a_in_b and use_a_in_c, both qualified-by-context (B/C ops) |

### Coherence resolution at D's load time

D claims `fact B[T = Int]` and `fact C[T = Int]`. Both B and C `requires A`. The typer must verify D supplies A[T=Int] consistently for both bounds. D's `fact A[T = Int]` resolves to some impl (call it IntA). The same IntA is used for both the B-bound and the C-bound — this is coherence at the diamond's join point.

### Elaborated body of `D.main`

```
requirements: []
body: apply_within(
  fn = String.concat,
  args = [
    apply_within(fn = B.use_a_in_b, args = [x], requirements = [<IntA>]),
    apply_within(fn = C.use_a_in_c, args = [x], requirements = [<IntA>])
  ],
  requirements = []
)
```

The same requirement value (IntA) is passed twice — once to B.use_a_in_b's requirements slot, once to C.use_a_in_c's requirements slot.

### Notes

- Coherence is enforced at D's load: ambiguous A would reject; missing A would reject.
- At runtime, both B.use_a_in_b and C.use_a_in_c receive the same IntA requirement, so dispatch resolves consistently.
- If a future version of D wanted to use *different* A's for B vs C (rare, controversial), the model could support it via per-bound A pinning — but v0 enforces consistency.

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

### Per-op requirements

| Op | requirements | Notes |
|---|---|---|
| `B.sort_pair` | `[Eq[T=T], Ordered[T=T]]` | body calls eq (Eq op) and lt (Ordered op) |

### Elaborated body of `B.sort_pair`

`Sort.requires(B)` is canonically ordered by **declaration order in source**: index 0 = Eq, index 1 = Ordered (Eq declared first).

```
requirements: [Eq, Ordered]
body: if_expr(
  cond = apply_within(fn = requirement_at_current(0, "eq"), args = [a, b], requirements = []),
  then = apply_within(fn = pair, args = [a, b], requirements = []),
  else = if_expr(
    cond = apply_within(fn = requirement_at_current(1, "lt"), args = [a, b], requirements = []),
    then = apply_within(fn = pair, args = [a, b], requirements = []),
    else = apply_within(fn = pair, args = [b, a], requirements = [])
  )
)
```

Two distinct requirement-slots: `requirement_at_current(0)` for Eq, `requirement_at_current(1)` for Ordered. Both carry their own resolved impls.

### Call-site translation

Caller D with `fact B[T = Int]` and resolved `fact Eq[T = Int]` (IntEq), `fact Ordered[T = Int]` (IntOrdered):

```
apply_within(
  fn = B.sort_pair,
  args = [x, y],
  requirements = [<IntEq>, <IntOrdered>]
)
```

### Notes

- Multi-bound: requirement vector grows linearly with the number of `requires` clauses.
- Position is canonical (declaration order). The body refers to requirements by position; the call site fills in positional matching the canonical order.

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

### Per-op requirements (Monad.mapM)

`Monad.mapM`'s body has five spec-op calls (pure, bind, bind, recursive mapM, pure) all using Self == "this Monad instance." Self bound: requirements = `[Monad[M = M]]`.

### Elaborated body of `Monad.mapM`

```
requirements: [Monad]    -- Self bound (length 1)
body: match_expr(
  scrutinee = xs,
  arms = [
    arm(pattern = nil_pat,
        body = apply_within(fn = requirement_at_current(0, "pure"), args = [nil()], requirements = [])),
    arm(pattern = cons_pat(x, rest),
        body = apply_within(
          fn = requirement_at_current(0, "bind"),
          args = [
            apply_within(fn = f, args = [x], requirements = []),
            lambda_within(
              params = [y],
              body = apply_within(
                fn = requirement_at_current(0, "bind"),
                args = [
                  apply_within(
                    fn = Monad.mapM,    -- recursive call
                    args = [f, rest],
                    requirements = [requirement_at_current(0)]   -- pass current requirement to recursive call
                  ),
                  lambda_within(
                    params = [ys],
                    body = apply_within(
                      fn = requirement_at_current(0, "pure"),
                      args = [cons(y, ys)],
                      requirements = []
                    ),
                    captured_requirements = [0]   -- inner lambda captures requirement from outer lambda's frame
                  )
                ],
                requirements = []
              ),
              captured_requirements = [0]   -- outer lambda captures requirement from mapM's frame
            )
          ],
          requirements = []
        ))
  ]
)
```

Three things this example showcases:

1. **Same-requirement multi-call**: five calls to spec ops in one body, all reading `requirement_at_current(0)` for the same Monad instance.
2. **Recursive call passes requirement**: `mapM(f, rest)` recursively calls itself; since recursive mapM also needs requirement_at_current(0), the call's `requirements = [requirement_at_current(0)]` propagates the current frame's Monad requirement.
3. **Lambda requirement capture**: each `\y -> ...` and `\ys -> ...` lambda captures `requirement_at_current(0)` from its enclosing scope via `captured_requirements = [0]`. When the lambda is invoked (via `bind`), the new frame's `requirements[0]` is populated from the closure's snapshot.

### Conditional instance: StateT chain

```anthill
fact Monad[M = StateT[S = ?S, M = ?M]] :- Monad[M = ?M]

operation pure(x) = ...    -- StateT's pure body
operation bind(m, f) = ... -- StateT's bind body, uses inner M's bind/pure
```

StateT's bind body looks roughly:

```
operation bind(m: StateT[S, M, A], k: A -> StateT[S, M, B]) -> StateT[S, M, B] =
  -- needs inner M's bind to compose state-passing
  \s -> bind_inner(m(s), \pair -> ...)        -- bind_inner is M's bind
```

This body uses M's bind. So StateT's bind body's requirements = [Monad[M = M]] (Self bound on the INNER M, not on StateT). The outer M is what requirement_at_current(0) refers to.

### Resolution chain at use site

Some caller has a value of type `StateT[Int, Option, X]` and calls `bind` on it.

- SLD synthesis: want Monad[StateT[Int, Option]]. Match conditional clause `Monad[StateT[?S, ?M]] :- Monad[?M]` with `?S = Int, ?M = Option`. Subgoal: Monad[Option]. Find: `fact Monad[M = Option]` → OptionMonad.
- The conditional clause's *resolved requirement value* is some StateT-Monad-instance constructed by the StateT machinery, which internally references OptionMonad.
- At the caller's `bind` call site, `requirements = [<resolved_StateT_Monad_instance>]`.
- That instance's bind body, when entered, has its `frame.requirements[0]` = the inner OptionMonad reference (passed through by the StateT-Monad-instance construction).

Each layer's body uses `requirement_at_current(0)` for its inner Monad. The chain materializes step-by-step as the call stack descends — never as one giant pre-built data structure.

### Notes

- The monad-transformer pattern works because each level's requirement slot only carries the *direct* requires; deeper resolutions live in deeper frames.
- `lambda_within(captured_requirements = [0])` is essential here: monadic continuations would lose their Monad requirement without capture.
- The recursive `mapM(f, rest)` call propagates `requirements = [requirement_at_current(0)]` — the current frame's requirement passes through to the recursive frame.

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

### Per-op requirements

`Tagged.unwrap` doesn't call any spec ops. requirements = `[]`.

### Elaborated body

```
requirements: []
body: match_expr(
  scrutinee = x,
  arms = [arm(pattern = tagged_pat(v), body = var_ref(v))]
)
```

No requirement slot needed.

### Notes

- Phantom params (Tag here) don't appear in requirement signatures because they don't drive any spec-op dispatch.
- Both UserId.unwrap and PostId.unwrap could share the same `unwrap` body (they DO, since it's inherited from Tagged).
- Plan P naturally handles this: the requirement signature is the body's actual requirement, not the type-arg cardinality.

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

### Per-op requirements

The body has TWO different `eq` calls:
1. `eq(x, y)` where `x, y : ?A`. Needs `Eq[T = ?A]` — the inner element's Eq.
2. `eq(rest_x, rest_y)` where `rest_x, rest_y : List[T = ?A]`. This is **self-recursion**: same impl, same body. Resolved by **direct call to `EqList.eq`** (form (1) — concrete symbol). No Self entry in `requirements`.

So `requirements = [Eq[?A]]` — length 1, just the inner element's Eq.

### Elaborated body

```
requirements: [Eq[?A]]    -- only the inner element; Self resolved by name
body: match_expr(
  ...
  arms with cons-cons branch:
    apply_within(
      fn = and,
      args = [
        -- inner element call: dispatch via requirement value (form (2))
        apply_within(fn = requirement_at_current(0, "eq"), args = [x, y], requirements = []),
        -- self-recursion: direct call by impl name (form (1)), forward inner Eq
        apply_within(fn = EqList.eq, args = [rest_x, rest_y], requirements = [requirement_at_current(0)])
      ],
      requirements = []
    )
  ...
)
```

### Call-site translation

Caller calling `eq(xs, ys)` for `xs, ys : List[T = Int]`. Caller's frame holds `<EqListInt>` (the constructed `Eq[List[Int]]` requirement value, which itself bundles `<IntEq>` as its `requirements[0]`).

- SLD synthesis: want `Eq[T = List[T = Int]]`. Match conditional `Eq[T = List[T = ?A]] :- Eq[T = ?A]` with `?A = Int`. Subgoal: `Eq[T = Int]` → IntEq.
- Construction at the call site:
  ```
  let inner = construct_requirement(IntEq, requirements=[])             -- IntEq requirement value
  let outer = construct_requirement(EqList, requirements=[inner])       -- EqListInt requirement value
  apply_within(
    fn = requirement_at_current(j, "eq"),                             -- j = caller's slot for outer
    args = [xs, ys],
    requirements = [requirement_at_sort(requirement_at_current(j), 0)]                     -- pass outer's bundled IntEq into body's slot 0
  )
  ```

Inside the body (`frame.requirements = [IntEq]`):
- `requirement_at_current(0, "eq")(x, y)` → dispatches IntEq.eq on individual Int elements.
- `EqList.eq(rest_x, rest_y, requirements=[requirement_at_current(0)])` → direct recursion; recursive frame's `requirements = [IntEq]`, so the inner-element call inside the recursive frame still resolves to IntEq.

### Notes

- The body's `frame.requirements` is just the inner element's Eq — no Self entry. Body length is independent of recursion depth.
- The conditional-instance requirement value (EqListInt) bundles its dependency (IntEq) at construction. The dispatch site projects with `requirement_at_sort` to feed the body's `requirements`.
- Self-recursion is form (1) — concrete impl op symbol. No requirement-lookup needed for the recursive target.

## Example 8 — Recursive instance chain (`Eq[List[List[X]]]`)

This example extends Example 7 by one nesting level — the SAME body and the SAME impl, applied recursively at construction time. Demonstrates how chained conditional instances fold into the requirement-value graph.

### Setup

(Same `EqList` sort as Example 7, conditional fact `Eq[T = List[T = ?A]] :- Eq[T = ?A]`, plus a base impl `EqX` for some sort `X`.)

Concrete query: caller has `xss, yss : List[T = List[T = X]]` and an `EqX` impl in scope; calls `eq(xss, yss)`.

### SLD synthesis chain

Caller resolving `Eq[T = List[T = List[T = X]]]`:

| Step | Goal | Match | Resolved as |
|---|---|---|---|
| 1 | `Eq[List[List[X]]]` | conditional with `?A = List[X]` → subgoal `Eq[List[X]]` | (descend) |
| 2 | `Eq[List[X]]` | conditional with `?A = X` → subgoal `Eq[X]` | (descend) |
| 3 | `Eq[X]` | base fact → `EqX` | leaf |

### Construction (bottom-up)

The call-site IR builds the chain bottom-up:

```
let env_X    = construct_requirement(EqX,    requirements=[])             -- arena handle, refcount=1
let env_LX   = construct_requirement(EqList, requirements=[env_X])        -- bundles env_X
let env_LLX  = construct_requirement(EqList, requirements=[env_LX])       -- bundles env_LX
```

After construction the arena holds three slots:

```
env_X    : { functor: EqX,    requirements: [] }                  -- refcount=2 (held by caller's local + env_LX.requirements[0])
env_LX   : { functor: EqList, requirements: [env_X-handle] }      -- refcount=2 (held by caller's local + env_LLX.requirements[0])
env_LLX  : { functor: EqList, requirements: [env_LX-handle] }     -- refcount=1 (held by caller's local)
```

No cycles: each requirement value's `requirements` references only requirement values constructed earlier in the chain.

### Call-site IR

```
apply_within(
  fn   = requirement_at_current(j, "eq"),                           -- j = caller's slot for env_LLX
  args = [xss, yss],
  requirements = [requirement_at_sort(requirement_at_current(j), 0)]                     -- env_LLX.requirements[0] = env_LX
)
```

### Runtime trace (one cons-cons step at the outer level)

The body of EqList.eq executes for outer xss = `cons(xs, rest_xss)`, yss = `cons(ys, rest_yss)`. Each element xs / ys is itself `List[X]`.

1. **Frame for outer call**: `frame.requirements = [env_LX]` (from the apply's requirements slot evaluated).

2. **Inner-element call** `eq(xs, ys)` where `xs, ys : List[X]`:
   ```
   apply_within(fn = requirement_at_current(0, "eq"), args = [xs, ys], requirements = [])
   ```
   At runtime: `frame.requirements[0] = env_LX`; functor=EqList → resolve to EqList.eq impl.

   But wait — the body's requirements is `[Eq[?A]]` (length 1), so it expects a requirement at slot 0. The inline IR above shows `requirements = []` — that's not enough. The IR transform actually emits:
   ```
   apply_within(fn = requirement_at_current(0, "eq"), args = [xs, ys],
                requirements = [requirement_at_sort(requirement_at_current(0), 0)])      -- env_LX.requirements[0] = env_X
   ```
   Inner-element call's body (entered with `frame.requirements = [env_X]`) — recursing on List[X], which contains X-typed elements.

3. **One more level down**: this body's inner-element call `eq(x, y)` where `x, y : X` becomes:
   ```
   apply_within(fn = requirement_at_current(0, "eq"), args = [x, y],
                requirements = [])                            -- EqX.eq has requirements = []
   ```
   At runtime: `frame.requirements[0] = env_X`; functor=EqX → resolve to EqX.eq. Pushes a frame with `requirements = []`. EqX.eq body runs on Xs.

4. **Self-recursion paths** (at each level):
   - Outer-level recursion on `rest_xss, rest_yss : List[List[X]]`:
     ```
     apply_within(fn = EqList.eq, args = [rest_xss, rest_yss],
                  requirements = [requirement_at_current(0)])                -- forward env_LX
     ```
     Direct call by name; new frame's `requirements = [env_LX]` — same as outer.
   - Inner-level recursion on `rest_xs, rest_ys : List[X]`:
     ```
     apply_within(fn = EqList.eq, args = [rest_xs, rest_ys],
                  requirements = [requirement_at_current(0)])                -- forward env_X
     ```
     Same body, new frame's `requirements = [env_X]`.

The body code is identical in every frame; only `frame.requirements` differs.

### Why this works without cycles

- Each construct_requirement builds a requirement value pointing only to **already-constructed** sub-requirements. The arena handles flow upward (earlier → later), never inward.
- Self-recursion uses form (1) (concrete impl name `EqList.eq`), so the recursive call doesn't need a self-handle in `requirements`.
- An requirement value's `requirements` is bounded by its impl's `requirements.len()` — for EqList that's 1 (just the inner element's Eq).

### Refcount lifecycle for this chain

Starting at the outer call's frame push (after step 1 above):

```
env_LLX:  caller-local + IR-eval-step + frame.requirements (transient) → various transient bumps then drop
env_LX:   env_LLX.requirements[0] + caller-local + (passed into outer frame.requirements)
env_X:    env_LX.requirements[0] + (passed into inner frames as needed)
```

When outer call returns, caller's local drops:
- `env_LLX` rc → 0; freed; cascades drop on its `requirements[0]` (= env_LX).
- `env_LX` rc decrements; if no other holder, also frees; cascades on its `requirements[0]` (= env_X).
- `env_X` rc decrements; if no other holder, also frees.

No cycle ⇒ refcount cascades cleanly.

### Notes

- The chain depth equals the type's nesting depth. Each level constructs one requirement value carrying one bundled handle (the next inner level).
- The single body of EqList.eq is reused at every level; per-frame `requirements` differs.
- `requirement_at_sort(requirement_at_current(j), 0)` is the projection primitive that "peels" one level of the chain at each call site.
- Compare with Example 7's call-site IR (single level): same shape, just one fewer construction.

## Example 9 — Same sort at two type-args (`requires Ordered[A]` and `requires Ordered[B]`)

When a sort has two `requires` clauses naming the **same sort but at different type-args**, they're treated as two distinct entries in `requirements`. Both share a sort name; both produce env values whose functor is some impl of `Ordered`; but the impls (and their bundled deps) typically differ.

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

### Per-op requirements

`Pair.cmp`'s body has two spec-op calls to `compare`, each with arguments of a different type — one A-typed, one B-typed. Each needs a different `Ordered` instance.

| Op | requirements | Notes |
|---|---|---|
| `Pair.cmp` | `[Ordered[T=A], Ordered[T=B]]` | two slots, one per `requires` |

### Canonical ordering

Slots follow **declaration order in source** — same single rule for every example. So `requirements[0] = Ordered[T=A]` (declared first), `requirements[1] = Ordered[T=B]`.

### Elaborated body

```
requirements: [Ordered[A], Ordered[B]]
body: let_expr(
  binding = ca,
  rhs = apply_within(
    fn = requirement_at_current(0, "compare"),    -- Ordered[A]'s compare
    args = [p1.a, p2.a],
    requirements = []                              -- compare's requirements = []
  ),
  body = if_expr(
    cond = apply_within(fn = ne, args = [ca, 0], requirements = []),
    then = ca,
    else = apply_within(
      fn = requirement_at_current(1, "compare"),   -- Ordered[B]'s compare
      args = [p1.b, p2.b],
      requirements = []
    )
  )
)
```

Two distinct slot indices: `requirement_at_current(0)` for `Ordered[A]`'s compare, `requirement_at_current(1)` for `Ordered[B]`'s compare.

### Call-site translation

Caller D using `Pair[A=Int, B=String]` and resolving Ordered[Int] (IntOrdered), Ordered[String] (StringOrdered):

```
apply_within(
  fn = Pair.cmp,
  args = [p1, p2],
  requirements = [<IntOrdered>, <StringOrdered>]
)
```

Inside the body, `requirement_at_current(0, "compare")` dispatches to `IntOrdered.compare` (because `frame.requirements[0]`'s functor is IntOrdered), and `requirement_at_current(1, "compare")` dispatches to `StringOrdered.compare`. The two slots stay separate; no aliasing despite both being `Ordered` impls.

### Notes

- Same-sort-name bounds aren't unusual — any sort parametric in multiple types (Pair, Map, BiFunctor, …) will frequently have multiple instances of the same constraint sort.
- Each slot is independent: caller can pass impls for entirely unrelated types (Int + String), or related types (e.g., both Int). Whatever was resolved.
- A is also `Ordered` (a future Pair type might use it differently); B independently is also `Ordered`. The functor in the env value tells the runtime which impl to dispatch.
- Compare with Example 4: that example had **different sort names** (`Eq` and `Ordered`) at the same `T`. This example has the **same sort name** (`Ordered`) at different type-args. Both produce length-2 `requirements`; the difference is whether the two slots' env values share a functor or not.

## Summary observations

Across all nine examples, the pattern is consistent:

- **Requirement-less ops** (impl ops with concrete bodies and no spec calls) have `requirements = []`.
- **Spec-op calls** become either `apply_within(fn = ImplOp, ..., requirements = [...])` (form (1) — pinned at typing time) or `apply_within(fn = requirement_at_current(i, op_short), ..., requirements = [...])` (form (2) — dispatched at runtime via requirement value).
- **Self-recursion in conditional impls** uses form (1) with the impl's own qualified op name. No Self entry in `requirements`. No cycles.
- **Multi-bound ops** have `requirements` of length N matching the sort's `requires` clauses in **declaration order**.
- **Conditional instances** materialize as chained requirement values constructed bottom-up; each value bundles only its non-Self deps.
- **Lambdas** capture requirements from their enclosing scope; closures carry requirement values for invocation later.
- **Recursive calls** pass the current frame's relevant requirement slots through `requirements = [...]` to the recursive frame.

The IR translation is mechanical given:
1. Per-op `requirements` (computed by body walk + fixed-point for mutual recursion).
2. The canonical ordering of requirement slots (**declaration order in source**).
3. SLD synthesis at each call site to resolve requirement values from the caller's `fact …` declarations and construct them via `construct_requirement`.

The runtime is uniform: `frame.requirements[i]` is populated at frame entry from the caller's `apply_within.requirements`; `requirement_at_current(i, op_short)` dispatches via the requirement value's functor; `requirement_at_sort(requirement_expr, k)` projects into an requirement value's bundled `requirements`. No new runtime mechanism beyond these primitives.
