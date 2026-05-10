# Operation-call model: worked examples

## Status: Concrete walk-through of example translations under the chosen IR

## Companion to: `operation-call-model.md` (decision), `operation-call-model-brainstorm.md` (exploration)

This doc takes representative examples from the brainstorm and shows how each translates from source to elaborated IR — the `_within` apply / lambda forms with explicit env slots.

Conventions used below:

- `env_at(i)` denotes a synthesized var-ref reading `frame.envs[i]`.
- IR is rendered in a slightly informal sugared form for readability; actual `Term::Fn { functor: apply_within, named_args: [...] }` shapes are larger but mechanical.
- Each example shows: source, the per-op required_envs derived by body walk, the elaborated body, and the call-site translations from a hypothetical caller.

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

### Per-op required_envs (after body walk)

| Op | required_envs | Notes |
|---|---|---|
| `A.foo` | `[]` | spec op (no body) |
| `B.bar` | `[A]` | body calls foo (an A op) |
| `C1.foo` | `[]` | impl op, no spec calls |
| `C2.foo` | `[]` | impl op, no spec calls |

### Elaborated bodies

`B.bar`:

```
required_envs: [A]
body: apply_within(
  fn = String.concat,
  args = [
    string_lit("B"),
    apply_within(fn = env_at(0).foo, args = [x], envs = [])
  ],
  envs = []
)
```

`env_at(0)` reads `frame.envs[0]`, which the caller filled with the resolved A impl. Dispatch on the value's functor finds the right `foo`.

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
  envs = [<C2 entity-value>]    -- typer resolves D's A[T=String] → C2
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
  envs = [<C1 entity-value with T binding>]
)
```

The env value is sort-tagged (`Value::Entity { functor: C1, ... }`); inside `B.bar`, `env_at(0).foo(x)` dispatches on the value's functor.

### Notes

- `B.bar`'s body has ONE call to a spec op (`foo`), so `envs = [A]` is length 1.
- Different callers fill the same slot with different impls (C1 or C2) based on their own resolved env.
- The body itself never changes; only the caller's `envs` slot varies.

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

### Per-op required_envs

| Op | required_envs | Notes |
|---|---|---|
| `Eq.eq` | `[]` | spec op |
| `Eq.neq` | `[Eq]` | default body uses `eq` (a same-sort spec op) — Self bound |
| `IntEq.eq` | `[]` | impl op, no calls to specs |

### Elaborated body of `Eq.neq`

```
required_envs: [Eq]   -- Self bound: "this Eq instance"
body: apply_within(
  fn = not,
  args = [apply_within(fn = env_at(0).eq, args = [a, b], envs = [])],
  envs = []
)
```

The Self bound expresses "neq's body needs the Eq instance dispatching against." When IntEq inherits the default `neq`, the env value at index 0 is IntEq itself.

### Call-site translation

Caller calling `neq(x, y)` for `x, y : Int` (IntEq satisfies Eq[T=Int]):

```
apply_within(
  fn = Eq.neq,        -- dispatched from spec name to inherited default
  args = [x, y],
  envs = [<IntEq entity-value>]
)
```

Inside `Eq.neq`'s body, `env_at(0).eq(a, b)` dispatches to `IntEq.eq` because `frame.envs[0]`'s functor is IntEq.

### Notes

- This is the "Self-dispatch" case. `Eq.neq` doesn't have an explicit `requires` clause, but its body refers to `eq` (a same-sort spec op), which implicitly bounds Self to satisfy Eq.
- Per-op required_envs is derived from body even when Self is implicit.
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

### Per-op required_envs

| Op | required_envs | Notes |
|---|---|---|
| `B.use_a_in_b` | `[A]` | body calls foo |
| `C.use_a_in_c` | `[A]` | body calls foo |
| `D.main` | `[]` | calls use_a_in_b and use_a_in_c, both qualified-by-context (B/C ops) |

### Coherence resolution at D's load time

D claims `fact B[T = Int]` and `fact C[T = Int]`. Both B and C `requires A`. The typer must verify D supplies A[T=Int] consistently for both bounds. D's `fact A[T = Int]` resolves to some impl (call it IntA). The same IntA is used for both the B-bound and the C-bound — this is coherence at the diamond's join point.

### Elaborated body of `D.main`

```
required_envs: []
body: apply_within(
  fn = String.concat,
  args = [
    apply_within(fn = B.use_a_in_b, args = [x], envs = [<IntA>]),
    apply_within(fn = C.use_a_in_c, args = [x], envs = [<IntA>])
  ],
  envs = []
)
```

The same env value (IntA) is passed twice — once to B.use_a_in_b's envs slot, once to C.use_a_in_c's envs slot.

### Notes

- Coherence is enforced at D's load: ambiguous A would reject; missing A would reject.
- At runtime, both B.use_a_in_b and C.use_a_in_c receive the same IntA env, so dispatch resolves consistently.
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

### Per-op required_envs

| Op | required_envs | Notes |
|---|---|---|
| `B.sort_pair` | `[Eq[T=T], Ordered[T=T]]` | body calls eq (Eq op) and lt (Ordered op) |

### Elaborated body of `B.sort_pair`

`Sort.requires(B)` is canonically ordered (alphabetical by qualified name): index 0 = Eq, index 1 = Ordered.

```
required_envs: [Eq, Ordered]
body: if_expr(
  cond = apply_within(fn = env_at(0).eq, args = [a, b], envs = []),
  then = apply_within(fn = pair, args = [a, b], envs = []),
  else = if_expr(
    cond = apply_within(fn = env_at(1).lt, args = [a, b], envs = []),
    then = apply_within(fn = pair, args = [a, b], envs = []),
    else = apply_within(fn = pair, args = [b, a], envs = [])
  )
)
```

Two distinct env-slots: `env_at(0)` for Eq, `env_at(1)` for Ordered. Both carry their own resolved impls.

### Call-site translation

Caller D with `fact B[T = Int]` and resolved `fact Eq[T = Int]` (IntEq), `fact Ordered[T = Int]` (IntOrdered):

```
apply_within(
  fn = B.sort_pair,
  args = [x, y],
  envs = [<IntEq>, <IntOrdered>]
)
```

### Notes

- Multi-bound: env vector grows linearly with the number of `requires` clauses.
- Position is canonical (alphabetical here). The body refers to envs by position; the call site fills in positional matching the canonical order.

## Example 5 — Monad transformer chain (instance chains + lambda env capture)

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

### Per-op required_envs (Monad.mapM)

`Monad.mapM`'s body has five spec-op calls (pure, bind, bind, recursive mapM, pure) all using Self == "this Monad instance." Self bound: required_envs = `[Monad[M = M]]`.

### Elaborated body of `Monad.mapM`

```
required_envs: [Monad]    -- Self bound (length 1)
body: match_expr(
  scrutinee = xs,
  arms = [
    arm(pattern = nil_pat,
        body = apply_within(fn = env_at(0).pure, args = [nil()], envs = [])),
    arm(pattern = cons_pat(x, rest),
        body = apply_within(
          fn = env_at(0).bind,
          args = [
            apply_within(fn = f, args = [x], envs = []),
            lambda_within(
              params = [y],
              body = apply_within(
                fn = env_at(0).bind,
                args = [
                  apply_within(
                    fn = Monad.mapM,    -- recursive call
                    args = [f, rest],
                    envs = [env_at(0)]   -- pass current env to recursive call
                  ),
                  lambda_within(
                    params = [ys],
                    body = apply_within(
                      fn = env_at(0).pure,
                      args = [cons(y, ys)],
                      envs = []
                    ),
                    captured_envs = [0]   -- inner lambda captures env from outer lambda's frame
                  )
                ],
                envs = []
              ),
              captured_envs = [0]   -- outer lambda captures env from mapM's frame
            )
          ],
          envs = []
        ))
  ]
)
```

Three things this example showcases:

1. **Same-env multi-call**: five calls to spec ops in one body, all reading `env_at(0)` for the same Monad instance.
2. **Recursive call passes env**: `mapM(f, rest)` recursively calls itself; since recursive mapM also needs env_at(0), the call's `envs = [env_at(0)]` propagates the current frame's Monad env.
3. **Lambda env capture**: each `\y -> ...` and `\ys -> ...` lambda captures `env_at(0)` from its enclosing scope via `captured_envs = [0]`. When the lambda is invoked (via `bind`), the new frame's `envs[0]` is populated from the closure's snapshot.

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

This body uses M's bind. So StateT's bind body's required_envs = [Monad[M = M]] (Self bound on the INNER M, not on StateT). The outer M is what env_at(0) refers to.

### Resolution chain at use site

Some caller has a value of type `StateT[Int, Option, X]` and calls `bind` on it.

- SLD synthesis: want Monad[StateT[Int, Option]]. Match conditional clause `Monad[StateT[?S, ?M]] :- Monad[?M]` with `?S = Int, ?M = Option`. Subgoal: Monad[Option]. Find: `fact Monad[M = Option]` → OptionMonad.
- The conditional clause's *resolved env value* is some StateT-Monad-instance constructed by the StateT machinery, which internally references OptionMonad.
- At the caller's `bind` call site, `envs = [<resolved_StateT_Monad_instance>]`.
- That instance's bind body, when entered, has its `frame.envs[0]` = the inner OptionMonad reference (passed through by the StateT-Monad-instance construction).

Each layer's body uses `env_at(0)` for its inner Monad. The chain materializes step-by-step as the call stack descends — never as one giant pre-built data structure.

### Notes

- The monad-transformer pattern works because each level's env slot only carries the *direct* requires; deeper resolutions live in deeper frames.
- `lambda_within(captured_envs = [0])` is essential here: monadic continuations would lose their Monad env without capture.
- The recursive `mapM(f, rest)` call propagates `envs = [env_at(0)]` — the current frame's env passes through to the recursive frame.

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

### Per-op required_envs

`Tagged.unwrap` doesn't call any spec ops. required_envs = `[]`.

### Elaborated body

```
required_envs: []
body: match_expr(
  scrutinee = x,
  arms = [arm(pattern = tagged_pat(v), body = var_ref(v))]
)
```

No env slot needed.

### Notes

- Phantom params (Tag here) don't appear in env signatures because they don't drive any spec-op dispatch.
- Both UserId.unwrap and PostId.unwrap could share the same `unwrap` body (they DO, since it's inherited from Tagged).
- Plan P naturally handles this: the env signature is the body's actual requirement, not the type-arg cardinality.

## Example 7 — Conditional default (`Eq[List[T]] :- Eq[T]`)

### Source

```anthill
fact Eq[T = List[T = ?A]] :- Eq[T = ?A]

operation eq(xs: List[T = ?A], ys: List[T = ?A]) -> Bool =
  match (xs, ys)
    case (nil(), nil()) -> true
    case (cons(x, rest_x), cons(y, rest_y)) ->
      and(eq(x, y), eq(rest_x, rest_y))   -- inner eq: Eq[T = ?A]; outer recursion: Eq[T = List[?A]]
    case _ -> false
end
```

### Per-op required_envs

The body has TWO different `eq` calls:
1. `eq(x, y)` where `x, y : ?A`. Needs `Eq[T = ?A]` — the inner element's Eq.
2. `eq(rest_x, rest_y)` where `rest_x, rest_y : List[T = ?A]`. Needs `Eq[T = List[T = ?A]]` — Self bound (THIS instance recursing).

Self bound: index 0. Inner element bound: index 1 (the conditional's subgoal).

required_envs = `[Eq[List], Eq[A]]` (canonical order).

### Elaborated body

```
required_envs: [Eq[List[?A]], Eq[?A]]   -- Self at index 0, inner element's Eq at index 1
body: match_expr(
  ...
  arms with cons-cons branch:
    apply_within(
      fn = and,
      args = [
        apply_within(fn = env_at(1).eq, args = [x, y], envs = []),         -- inner element
        apply_within(fn = env_at(0).eq, args = [rest_x, rest_y], envs = [])   -- Self recursion
      ],
      envs = []
    )
  ...
)
```

### Call-site translation

Caller calling `eq(xs, ys)` for `xs, ys : List[T = Int]`:

- SLD synthesis: want `Eq[T = List[T = Int]]`. Match conditional `Eq[T = List[T = ?A]] :- Eq[T = ?A]` with `?A = Int`. Subgoal: `Eq[T = Int]` → IntEq.
- Resolved env at call site: index 0 = the conditional-Eq-for-List instance (call it `EqListInt`); index 1 = IntEq.
- `apply_within(fn = eq, args = [xs, ys], envs = [<EqListInt>, <IntEq>])`.

Inside the body, `env_at(1).eq(x, y)` invokes IntEq.eq on individual elements; `env_at(0).eq(rest_x, rest_y)` recurses through EqListInt.

### Notes

- Conditional / chained instances naturally produce multi-element env vectors.
- The Self bound (the conditional's own head) is index 0 conventionally; subgoals fill subsequent indices.
- The recursive `eq(rest_x, rest_y)` reads `env_at(0)` — the same conditional-Eq-for-List instance — and recurses correctly.

## Summary observations

Across all seven examples, the pattern is consistent:

- **Env-less ops** (impl ops with concrete bodies) have empty `envs = []`.
- **Spec-op ops** (no body, dispatched at typing time) become `apply_within(fn = ImplOp, ..., envs = [...])` after rewriting.
- **Default-body ops with Self bound** have `required_envs = [SelfSort]`.
- **Multi-bound ops** have `required_envs` of length N matching the sort's `requires` clauses canonically ordered.
- **Conditional instances** produce env vectors that include both the Self bound and the conditional's subgoal envs.
- **Lambdas** capture envs from their enclosing scope via `captured_envs`; closures carry env values for invocation later.
- **Recursive calls** pass the current frame's env slot through, so the recursive frame inherits the same env scope.

The IR translation is mechanical given:
1. Per-op `required_envs` (computed by body walk + fixed-point for mutual recursion).
2. The canonical ordering of env slots (alphabetical by bound's qualified name, or declaration order).
3. SLD synthesis at each call site to resolve the env values from the caller's `fact …` declarations.

The runtime is unchanged: `frame.envs[i]` is regular structural state populated at frame entry, and `env_at(i).foo(args)` dispatches via existing entity-functor-based op resolution. No new runtime mechanism.
