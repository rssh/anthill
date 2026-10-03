# 069: Declaration-site defaults for operation, entity-constructor, and sort parameters

## Status: Draft (2026-10-03). The motivating verdict is that `Function[A, B]` is pure: its omitted `E` is `{}`, while `Function[A, B, ?]` is explicitly open. This proposal reopens proposal 042 OQ3 / WI-850 with that concrete driver and extends the same declaration-time mechanism to operation and entity-constructor value parameters. Type inference runs to a fixed point before defaults are chosen, then solving resumes once with the defaults installed.

## Relates to: [002](002-arrow-sorts.md) (sort parameters), [018](018-expressions-and-operation-implementation.md) (operation bodies), [042](042-explicit-type-parameters-on-operations.md) (explicit operation type parameters; OQ3), [045](045-effect-sets-and-expressions.md) (effect-row binders), kernel-language §§4.4 and 8.1 (the contradictory `Function[A, B]` readings), WI-850 (the current refusal), WI-188 (entity record update), and WI-191 (typed command arguments).

## Tracked by: WI-20261003-QV5W5 (`proposal-069`). WI-188 depends on it.

## The problem

Anthill has no declaration-site parameter default. That absence now has a concrete semantic cost,
not merely a convenience cost.

Kernel-language §4.4 says both of these things:

```anthill
(A) -> B              = Function[A, B]       -- pure
(A) -> B @ E          = Function[A, B, E]     -- effectful
```

and states that the first form has the empty effect set. But §8.1 gives every unwritten sort slot
a fresh variable:

```anthill
Function[A, B] = Function[A, B, ?E]
```

Those readings contradict one another. The library comment currently tries to bridge the gap by
saying that an unbound `Function.E` means empty, but an unbound slot is not an empty row: it is a
variable which inference may bind to a non-empty row, or which polarity may make universal or
existential. Purity must be written into the declaration rather than inferred from absence.

Two related omissions have the same shape:

1. An explicit operation type parameter cannot say what to use when arguments and expected result
   do not determine it. `operation foo[T = Int64](...)` is deliberately refused by WI-850 because
   the parsed default used to be silently discarded.
2. An operation or entity-constructor value parameter cannot supply a declaration-owned argument.
   Entity fields are currently only `Name ':' Type`; there is no constructor default. Consequently a record
   update cannot be expressed as an ordinary operation whose unchanged fields default to projections
   from the receiver; WI-188 currently proposes a bespoke residual-override lowering instead.

The common rule is: a declaration may provide a value for a slot which its use site leaves
unwritten. The four surfaces carry two different kinds of thing—terms for value parameters, types
for type parameters—but omission, dependency order, diagnostics, and reflection should agree.

## 1. Surface

### 1.1 Operation value parameters

An operation parameter may carry a default expression:

```anthill
operation clamp(x: Int64, low: Int64 = 0, high: Int64 = 100) -> Int64 = ...

clamp(12)                  -- clamp(12, 0, 100)
clamp(12, high: 20)        -- clamp(12, 0, 20)
clamp(x: 12, low: 5)       -- clamp(12, 5, 100)
```

Grammar:

```text
Param ::= Name ':' Type ['=' Expr]
```

`=` belongs to the declaration; named arguments at an ordinary call retain Anthill's existing
`name: value` spelling. A defaulted parameter need not form a suffix because named arguments can
fill a later required slot:

```anthill
operation connect(host: String = "localhost", port: Int64) -> Connection = ...
connect(port: 5432)
```

A positional argument still fills the next unfilled declaration slot. Once the written positional
arguments end, every unfilled slot must either have a default or have been filled by name. Otherwise
the existing exact-coverage error applies and names the required slot.

### 1.2 Entity-constructor parameters

An entity field may carry a constructor default:

```anthill
entity Endpoint(host: String = "localhost", port: Int64 = 80)

Endpoint()                         -- Endpoint(host: "localhost", port: 80)
Endpoint(port: 8080)               -- Endpoint(host: "localhost", port: 8080)
```

Grammar:

```text
Field ::= Name ':' Type ['=' Expr]
```

The field declaration still defines the stored shape; its default affects only construction. A
default may refer to earlier fields, under the same ordering rule as operation parameters.

Constructor defaults apply only where an entity application constructs a value. In a fact head,
rule head, match case, or other pattern position, an omitted field retains its existing pattern
meaning—it is unconstrained, not filled by a default. This distinction prevents adding a default
from silently changing which stored facts a pattern matches.

### 1.3 Explicit operation type parameters

Proposal 042's parsed-but-refused form becomes meaningful:

```anthill
operation decode[T = String](bytes: Bytes) -> T = ...
```

Grammar:

```text
OperationTypeParam ::= Name ['=' Type]
```

At a call, an operation type parameter is settled in this order:

1. an explicit call-site binding (`decode[T = Json](bytes)`);
2. inference from value arguments, requirements, receiver, and expected result;
3. its declaration default;
4. the existing unconstrained-type-parameter error.

The default is deliberately last: `identity[T = String](42)` still infers `T = Int64`; a default
fills silence and does not override evidence.

### 1.4 Sort type parameters

The enclosing-list declaration admits a default after `=`:

```anthill
sort Box[T = Int64]
  entity box(value: T)
end
```

The statement form retains `= ?` as the declaration of a parameter and adds an explicit `default`
tail, avoiding collision with an ordinary type alias:

```anthill
sort Box
  sort T = ? default Int64
  entity box(value: T)
end
```

Effect-row parameters use the same tail:

```anthill
sort Function
  sort A = ?
  sort B = ?
  effects E = ? default {}

  operation apply(f: Function[A, B, E], x: A) -> B effects E
end
```

Grammar additions:

```text
SortTypeParam     ::= Identifier [SortTypeParamList] ['=' Type]
UnspecifiedSort  ::= 'sort' Name '=' VariableTerm ['default' Type]
EffectsSortItem  ::= 'effects' Name '=' VariableTerm ['default' EffectExpr]
```

The `default` tail is admitted only when the right side declares a parameter (`?` or a named
variable). `sort T = Int64` remains a type alias, and `effects E = {Error}` remains a fixed effect
binding; neither silently changes meaning.

Higher-kinded defaults are allowed when kinds agree:

```anthill
sort Traverse[F[T] = List, A]
```

As with every declared type, a default is resolved and kind-checked at its declaration. A wrong-kind
default is a load error at the default, not a later failure at a use.

## 2. Infer first, default second, solve again

An omitted type parameter starts as an inference variable marked with its declaration default. An
explicit variable starts as an ordinary open variable and suppresses the default:

```anthill
Function[A, B]       -- Function[A, B, E = {}]
Function[A, B, ?]    -- E is a fresh open effect-row variable
Function[A, B, E]    -- E is the written surrounding parameter
Function[A, B, {IO}] -- E is explicitly {IO}
```

Defaults do not take part in primary inference. The complete algorithm at one elaboration boundary
is:

1. bind written positional and named arguments;
2. create fresh inference variables for omitted parameters, remembering which carry defaults;
3. gather the ordinary constraints from the call or type construction and solve them to a fixed
   point, without consulting defaults;
4. for each still-unbound, omitted parameter with a default, in declaration order, instantiate the
   default under the current substitution and add an equality constraint;
5. resume constraint solving to a fixed point so defaults propagate through dependent parameters
   and surrounding constraints;
6. perform conformance, kind, and unconstrained-parameter checks.

Step 5 is a second solver phase, not a second default-selection phase. A default is chosen at most
once. The solver may use `B = List[A]` to determine `A` from a constraint on `B`, but it may not
replace a value inferred in step 3, retry with another default after a contradiction, or apply a
default to an explicit `?`.

The elaboration boundary matters. An operation or constructor call gathers constraints from its
receiver, written arguments, requirements, and expected result before step 4. A type written as a
declaration contract is finalized before a later value is checked against that contract. Thus
`f: Function[A, B]` reaches step 4 with no evidence for `E` and becomes
`Function[A, B, E = {}]`; checking an effectful callback afterward cannot reopen it. Conversely,
`box(1)` may infer a defaulted element parameter from `1` before its default is considered.

This amends §8.1's expansion rule: an omitted parameter is initially fresh, as today, but a fresh
variable marked with a default must be finalized by steps 4–5 before the completed type escapes its
elaboration boundary. It does not change the polarity of an explicit hole or a non-defaulted slot.

Defaults may refer only to earlier parameters from the same declaration and to names in the
declaration's enclosing scope:

```anthill
sort Index[K, Values = List[T = K]]     -- valid
sort Bad[A = List[T = B], B]            -- refused: forward reference to B
```

Declaration order makes default installation deterministic and rejects cycles structurally. A
caller may override any default explicitly.

## 3. Operation and constructor value-default semantics

A value default is part of the operation or entity declaration and is elaborated into a full
argument list before evaluation or construction. The evaluator, constructor, and host ABI continue
to receive exactly the declared arity; there is no optional runtime slot and no new `Value` variant.

A default expression may refer to:

- earlier value parameters;
- the operation's type parameters and the enclosing sort's parameters (for an operation), or the
  entity's enclosing sort parameters (for a constructor);
- visible constants, constructors, and operations.

It may not refer to a later parameter, `result`, or a body-local binding. The dependency graph is
therefore declaration order, not a general fixed point:

```anthill
operation range(first: Int64, last: Int64 = first, step: Int64 = 1) -> Range = ...
```

Each selected default is evaluated exactly once, left to right, in the callee's parameter frame.
Its effects are effects of the operation and must fit the operation's declared effect row. Supplying
an explicit argument may avoid executing a default, but does not narrow the operation's declared
effect upper bound.

Calls in operation bodies, rule-body functional fragments, top-level queries, and constructor
expressions use the same coverage and insertion rule. A logical variable written as an argument is
an argument, not an omission. Pattern positions never insert constructor defaults.

### Function values

Defaults belong to a named operation declaration, not to arrow types. Eta-expanding an operation
therefore produces its full-arity arrow, as today, and applying the resulting function value must
supply every argument. No hidden optionality is added to `Function` or arrow equality.

This keeps defaults out of structural function subtyping and makes loss of the declaration name
explicitly the point where its call convenience is lost.

### Dispatch and conformance

A spec operation owns the callable signature, including its defaults. A carrier implementation
matches the full parameter list and types exactly as before and does not redeclare the defaults;
calls through the spec elaborate from the spec declaration before dispatch. A redeclared default
on an implementation is refused rather than compared for expression equivalence.

A non-spec operation owns its defaults directly. Reflection reports defaults from the callable
declaration, not from a selected implementation.

## 4. `Function[A, B]` resolves the §4.4 / §8.1 contradiction

`Function` declares:

```anthill
effects E = ? default {}
```

Consequently:

- `(A) -> B` and `Function[A, B]` both carry the closed empty row;
- `(A) -> B @ E` and `Function[A, B, E]` both carry the written row;
- `Function[A, B, ?]` is the explicit effect-polymorphic spelling;
- `Function[A, B] <: Function[A, B, E]` remains the ordinary effect-widening relation from the
  concrete empty row, not a special interpretation of an absent slot.

The `function.anthill` comment saying “E unbound (= empty)” is deleted. `E` is not left unbound: it
starts as a marked inference variable and is finalized to `{}` when primary inference leaves it
free. Section 8.1's fresh-variable rule gains the two solver phases from §2, while all of its
universal/existential rules continue to apply to explicit holes and non-defaulted slots.

## 5. Record update becomes an ordinary derived operation

For an entity `WorkItem`, the loader can derive the conceptual member:

```anthill
operation copy(
  self: WorkItem,
  id: String = self.id,
  description: String = self.description,
  status: Status = self.status
) -> WorkItem =
  WorkItem(id: id, description: description, status: status)
```

WI-188's surface remains:

```anthill
wi.copy(status = Claimed(agent, since))
```

The special record-update spelling lowers to the derived operation's ordinary named call
(`WorkItem.copy(wi, status: Claimed(agent, since))`). Every unspecified field is then handled by
the parameter-default mechanism. WI-188 still owns recognition of the `field = value` update
surface and derivation of `copy`, but no longer needs a separate residual override map or bespoke
constructor reconstruction semantics.

This is why WI-188 depends on this proposal's implementation rather than merely relating to it.

## 6. Diagnostics and reflection

- A declaration reports every default whose expression/type does not conform to its parameter.
- A default referencing a later parameter names both parameters and says that defaults are ordered.
- A call missing a required parameter names that parameter; it does not report only an arity count.
- An explicitly supplied value that conflicts with another inference source is still a type error;
  the default is never consulted as a fallback after a contradiction.
- `anthill.reflect` operation parameters, entity fields, and sort parameters expose their term or
  type default. A default is semantic data and may not be accepted by a parser then dropped, the
  failure WI-850 measured.
- Persistence and code generation preserve the distinction between no default, a default, and an
  explicit hole at a use site.

## 7. Implementation outline

1. Extend the tree-sitter grammar and both Rust and Scala parsed IRs for operation-value,
   entity-constructor, and sort defaults. Restore the already parsed explicit-operation-type
   default as semantic IR rather than a refusal.
2. Resolve and type-check defaults at their declarations. Record type defaults on sort parameter
   metadata and value defaults on the canonical operation signature.
3. Change type-parameter inference to mark omitted defaulted slots, solve without defaults, install
   defaults in declaration order, then resume solving before final validation. Preserve explicit
   `?` as the opt-out.
4. Change operation-call and entity-construction checking to complete missing value slots after
   type-parameter finalization. Keep the resulting runtime call/constructor at full arity, and do
   not fill omitted fields in pattern positions.
5. Thread defaults through reflection, persistence, Rust/Scala code generation, and diagnostics.
6. Declare `Function.E` as `default {}` and remove every special “unbound means empty” reading.
7. Replace WI-850's refusal tests with driven calls, and add controls proving that removing default
   application changes the result or restores the old error.

## 8. Acceptance

- `Function[A, B]` is structurally the same effect instantiation as `Function[A, B, E = {}]`, and
  rejects an effectful callback where a pure one is required.
- `Function[A, B, ?]` remains open and accepts an effect row inferred by its context.
- Arrow `(A) -> B` and `Function[A, B]` agree in the §4.4 and §8.1 tests without a special-case
  “missing E means empty” branch.
- `Box[T = Int64]` defaults an omitted `T`, while `Box[?]` remains open and `Box[String]` overrides
  the default.
- A dependent sort default (`Values = List[T = K]`) expands after `K`; a forward reference and a
  kind mismatch are loud declaration errors.
- A constraint introduced by a dependent default is propagated by the second solver phase and may
  determine an earlier still-free parameter; defaults are not selected a second time.
- `operation identity[T = String](x: Option[T] = none()) -> T` uses inference before `T`'s default,
  uses the default when no source binds `T`, and honors an explicit call-site override.
- A value default referring to an earlier parameter evaluates once and is type/effect checked.
- `Endpoint(port: 8080)` fills a defaulted `host`, while an omitted `host` in an `Endpoint` pattern
  remains unconstrained and matches stored non-default hosts too.
- Missing required parameters remain errors, including a required parameter declared after a
  defaulted one.
- Calls through function values still require full arity.
- Spec dispatch uses the spec declaration's defaults and refuses implementation-local redeclaration.
- Rust tests run through `rustland/scripts/test.sh`; `sbt testFull` and tree-sitter corpus tests pass.

## 9. Non-goals

- Default operation bodies and default providers are unrelated mechanisms.
- Defaults do not introduce partial application, variadic arguments, overloaded arities, or an
  optional-parameter bit in arrow types.
- A default is not an error-recovery fallback. It applies only to an omitted slot.
- Constructor defaults do not change pattern omission, stored entity shape, or field subtyping.
