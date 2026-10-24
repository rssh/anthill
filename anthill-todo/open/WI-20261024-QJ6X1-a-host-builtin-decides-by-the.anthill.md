## Attributes

- id: WI-20261024-QJ6X1-a-host-builtin-decides-by-the
- created: 2026-10-24T06:48:31Z

- status: Open
- status_agent: claude
- status_at: 2026-10-24T06:48:31Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A HOST BUILTIN DECIDES BY THE VALUE'S CARRIER, NOT BY THE VALUE: a tuple or an entity an operation built is refused where the same value read from a fact, or written inside the call's own expression, is accepted. Measured 2026-10-24 on 5cdccb0b; found while delivering WI-20261011-7G99A.

MAP KEYS. `Map.put(m, k, 4)` / `Map.get(m, k)` refuse `k` with 'expected Map key (Int / Bool / String / Symbol / Term), got Tuple' when `k` is `let k = (n, 2)`, a parameter `k: (Int64, Int64)` handed `(n, 2)`, or `mp(n)` with `operation mp(n: Int64) -> (Int64, Int64) = (n, 2)`; and with '..., got Entity' when it is `mkb(n)`, `operation mkb(n: Int64) -> Box = Box.bx(n)`, over `sort Box { entity bx(v: Int64) }`. The same keys work read from a fact (`rule hp((1, 2)) :- true`, `rule q(?r) :- hp(?k), ?r <=> byFactTuple(?k)` answers 4; the entity twin over `rule hb(Box.bx(1))` answers 4) and written inside one chained expression (`match m.put((n, n), 4).get((n, n))` answers 4), which hand the builtin a term or an occurrence. So whether a program runs depends on how its key was carried — WI-20260827-3ZNBC's defect, for the compound native carriers. A tuple parameter is one case of it, not the cause: an entity fails the same way.

NOT MAP-SPECIFIC. The reflect builtins with a `Term` parameter accept only some of a term's carriers too: `make_fn(name, [b])` with `b` a `let`-bound op-built entity or tuple is refused 'expected Term, got Entity' / 'got Tuple'; `replace_named_arg(t, "v", x)` takes only a hash-consed `Value::Term` for `t` (an op-built entity: 'got Entity'; an entity read from a fact through `hb(?b)`: 'got Node') and for `x` (an op-built tuple: 'got Node'); `term_as_entity[E = Box](p)` with `p` a tuple raises 'expected Term, got Tuple' where a value of another shape answers `none`.

MECHANISM, as far as read. `MapKey::try_from_value` (eval/map_arena.rs) keys an Int / Bool / Str / SymbolRef and a `Value::Term`; `MapKey::of_value_interning` adds a `Value::Node` through `occurrence_to_term`; a `Value::Entity` and a `Value::Tuple` take neither. The reflect builtins match carriers by hand (`reflect_make_fn`: a Term and the scalars; `reflect_replace_named_arg`: `Value::Term` only; `term_as_entity`: Entity / Term / Node / scalars). The total lowering exists: `node_occurrence::value_to_term`, which reflect's `expect_term` already goes through, lowers every carrier that has a term form, a tuple included since 5cdccb0b. `of_value_interning`'s doc states the rule its key must keep: the intern is paid only where the alternative was an error.

WHAT. A key, or a `Term` argument, is judged by the value: every carrier with a term form is accepted and lowers to its one term, so a native value and its occurrence or hash-consed twin address one Map slot and build one term. The opaque runtime handles (closure, stream, relation, map, cell) stay refused, loudly. Survey every host builtin with a `Term` or key parameter for a hand-written carrier match, and record the list on the ticket — not only the four above.

CONTROLS. A row per program above: each is refused today, and answers what its fact-read twin answers. The twins (the fact-read key, the chained expression) pass either way. An opaque value (a closure) stays a TypeMismatch at each builtin.

