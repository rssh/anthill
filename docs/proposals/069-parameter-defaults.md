# 069: Declaration-site defaults for operation, entity-constructor, and sort parameters, and rule columns

## Status: Draft (2026-10-03). The motivating verdict is that `Function[A, B]` is pure: its omitted `E` is `{}`, while `Function[A, B, ?]` is explicitly open. This proposal reopens proposal 042 OQ3 / WI-850 with that concrete driver and extends the same declaration-time mechanism to operation and entity-constructor value parameters, and to the columns of a declared rule (§1.5), whose undeclared default is `?`. Type inference runs to a fixed point before defaults are chosen, then solving resumes once with the defaults installed.

## Relates to: [002](002-arrow-sorts.md) (sort parameters), [018](018-expressions-and-operation-implementation.md) (operation bodies), [042](042-explicit-type-parameters-on-operations.md) (explicit operation type parameters; OQ3), [045](045-effect-sets-and-expressions.md) (effect-row binders), kernel-language §§4.4 and 8.1 (whose 2026-10-03 `Function[A, B]` verdict this proposal supersedes), WI-850 (the current refusal), WI-188 (entity record update), WI-191 (typed command arguments), [052](052-rules-as-stream-valued-operations.md) (a rule cited as a `Relation` value; WI-714's column binding), [061](061-rule-declarations.md) (rule declarations — where a rule column's default is written), [070](070-self-and-fresh-bare-sorts.md) (`Self`; a reference to the enclosing sort is read as any other, so a default applies inside a sort's own definition as outside it — §2), WI-20260821-6WVJB (one arity per predicate — enforced here only for a declaration with a default), and [070](070-self-and-fresh-bare-sorts.md) (`Self` — §2's "the self tie wins over the default" is `p: Self` in its terms).

## Tracked by: WI-20261003-QV5W5 (`proposal-069`). WI-188 depends on it.

## The problem

Anthill has no declaration-site parameter default. That absence now has a concrete semantic cost,
not merely a convenience cost.

Kernel-language §4.4 currently resolves the old arrow/`Function` ambiguity this way:

```anthill
(A) -> B              = Function[A, B, E = {}] -- pure; the arrow writes the row
(A) -> B @ E          = Function[A, B, E]      -- effectful
Function[A, B]        = Function[A, B, ?E]     -- omitted E is open
```

That is a coherent current rule, recorded as a user decision on 2026-10-03: the arrow is pure, while
the named sort with an omitted `E` is effect-polymorphic because Anthill declares no parameter
defaults. This proposal deliberately **supersedes that decision**. Its motivating verdict is that
the declaration of `Function` should own the ordinary meaning of an omitted row: `E` defaults to
`{}`, and the author who wants the open reading writes `Function[A, B, ?]`. Purity is then written in
the `Function` declaration rather than attached specially to either the arrow spelling or an
unbound variable.

Two related omissions have the same shape:

1. An explicit operation type parameter cannot say what to use when arguments and expected result
   do not determine it. `operation foo[T = Int64](...)` is deliberately refused by WI-850 because
   the parsed default used to be silently discarded.
2. An operation or entity-constructor value parameter cannot supply a declaration-owned argument.
   Entity fields are currently only `Name ':' Type`; there is no constructor default. Consequently a record
   update cannot be expressed as an ordinary operation whose unchanged fields default to projections
   from the receiver; WI-188 currently proposes a bespoke residual-override lowering instead.

The common rule is: a declaration may provide a value for a slot which its use site leaves
unwritten. The five surfaces carry two different kinds of thing—terms for value parameters and rule columns, types
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

**In a rule-body goal, the result is named `result:`.** A goal at an operation's arity + 1 is its
functional-relation view, the last positional argument being the result (WI-938); a `Bool`
operation's goal at its declared arity succeeds when the call returns `true` (WI-583). Both read the
COUNT of positional arguments, and a default makes the parameter count a range, so the count alone
no longer says which argument is the result:

```anthill
operation clamp(x: Int64, low: Int64 = 0, high: Int64 = 100) -> Int64

:- clamp(12, ?r)       -- the result with low and high defaulted?  or  x = 12, low = ?r?
:- clamp(12, 5, ?r)    -- the result with high defaulted?          or  low = 5, high = ?r?
```

So the result column takes a NAME, the reserved `result` (kernel-language §5.4 already refuses a
parameter named `result`, so the label can never mean a parameter):

- **Positional arity + 1 keeps its meaning — with every parameter written.** `clamp(12, 0, 100, ?r)`
  is the functional view exactly as today; no existing goal changes.
- **With fewer positional arguments, the goal is a call** and the omitted parameters take their
  defaults. For a `Bool` operation that is the "succeeds when `true`" reading (`contains(?xs, 3)`);
  any other operation needs its result column, written `result: ?r` — `clamp(12, result: ?r)`.
- **`result:` works at any arity**, with or without defaults: `clamp(12, 5, result: ?r)` and
  `clamp(12, 0, 100, result: ?r)` alike. It is the one spelling that combines with omission.
- **A short goal on a non-`Bool` operation without `result:` is a load error**, never a silent pick
  between the two readings: `clamp(12, ?r)` is refused with "`?r` fills `low`; write
  `result: ?r` for the call's result". (Read as a call, its value is an `Int64` in goal position,
  which is no goal.)

The same holds wherever the functional view is read — a rule body, a query, a constraint body.

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

**In a rule body, the position decides.** A rule body holds both kinds of position, and the same
text means a pattern in one and a value in the other:

```anthill
rule r1 :- Endpoint(port: 80)                         -- a goal: matches stored Endpoint facts
rule r2 :- connects(Endpoint(port: 80))               -- an argument of a rule goal: unified
rule r3(?d) :- ?d <=> describe(Endpoint(port: 80))    -- an argument of an operation call
```

- In a **logical** position — a goal, an argument of a rule goal (at any depth), or a side of `<=>`
  — the entity is matched by unification, so it is a pattern: an omitted field is a fresh variable
  (kernel-language §8.3, *Partial entity patterns*), never its default. `r1` and `r2` match stored
  `Endpoint`s whatever their host.
- As an argument of an **operation call** — which a rule body evaluates (proposal 068: an operation
  call in a rule body is its value, at any depth) — the entity is the value the operation receives,
  so it is a construction: omitted fields take their defaults. `r3` hands `describe` the
  `Endpoint("localhost", 80)` an operation body would, rather than an `Endpoint` with an unbound
  host on which the call could only wait.

The split keeps one meaning for `describe(Endpoint(port: 80))` in an operation body and in a rule
body — 068's purpose — and leaves every pattern meaning what it means today. It is the same
partition kernel-language §6.7 already draws for a dotted name between a logical position and a
value position. A position nested inside a construction inherits it (`describe(Wrap(Endpoint(port:
80)))` fills both), and one nested inside a pattern inherits that; an operation call nested inside a
pattern starts a value position again, because 068 evaluates it.

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

### 1.5 Rule columns

A rule is called as well as defined — as a goal in a rule body, in a query, and as a `Relation`
value cited in an operation body (proposal 052) — so its columns are parameters too. A column may
carry a default, and **only the predicate's declaration may write it** (proposal 061's body-less
`rule` head):

```anthill
rule within(?x, ?limit = 10)                  -- the declaration: `limit` defaults to 10
rule within(?x, ?limit) :- lt(?x, ?limit)     -- a clause: writes no default
rule within(?x, ?limit) :- special(?x, ?limit)

rule small(?x) :- within(x: ?x)               -- within(?x, 10)
rule any(?x)   :- within(x: ?x, limit: ?)     -- explicit `?`: every limit
```

Grammar, in a rule **declaration** head only:

```text
DeclColumn ::= Variable [':' Type] ['=' Expr]
```

The optional type is proposal 061's declared column type. When present it is the relation-schema
type for that column and every clause must conform to it; otherwise the schema type is synthesized
from the clauses as below. A default is not a type declaration and contributes no type information.

**Omission means the declared default, else `?`.** At a call, an omitted column takes its declared
default; a column with no default is a fresh variable, which is what an omitted column already
means at a citation today (`pair_eq(5)` is a `Relation` over its remaining column; WI-714). An
explicit `?` always means "free" and suppresses the default — the same opt-out `Function[A, B, ?]`
is for a sort parameter (§1.4):

| Call | No default declared | `?limit = 10` declared |
|---|---|---|
| `within(x: 5)` | `limit` free | `limit = 10` |
| `within(x: 5, limit: ?)` | `limit` free | `limit` free |
| `within(x: 5, limit: 3)` | `limit = 3` | `limit = 3` |

The default is inserted as though the caller had written it. If `limit` is an input of the rule's
clauses, the 10 is supplied; if it is an output, the 10 is checked — `within(x: 5)` succeeds only
where the rule answers `limit = 10`. Either reading is the clauses' own; the default adds nothing
but the argument.

**Only the declaration writes a default.** A predicate may have many clauses, and its default must
have one home. A default written on a clause head or a `fact` head is a load error naming the
declaration. If the predicate has no declaration, the clause cannot carry one — declare the
predicate (061) to give it a default.

The spelling `?v = e` inside a rule-head argument is today an ordinary term argument, the equation
`eq(?v, e)`. In a declaration that reading has no use — a declaration's columns are variables — so
the declaration reclaims it. In a **clause** head the same spelling is refused, with the message
pointing at the declaration, rather than left to mean an equation term: otherwise a default written
on the wrong head would load silently as something else. An equation term remains writable in a
clause head as `eq(?v, e)`. (The census of `?v = e` arguments in existing clause heads is part of
implementing this; each one found is rewritten to `eq(…)` or is a misplaced default.)

**A declaration with a default fixes the predicate's arity.** Once a declaration carries a default,
it states what every column means, and a clause at another arity has no meaning relative to it.
So every clause of that predicate — a `rule … :- …` clause or a `fact` — must have exactly the
declared columns, and one that does not is a load error naming the declaration and its arity:

```anthill
rule within(?x, ?limit = 10)          -- declaration with a default: `within` has two columns

rule within(?x, ?limit) :- lt(?x, ?limit)     -- fine
fact within(3, 5)                             -- fine
fact within(3)                        -- LOAD ERROR: `within` is declared with 2 columns
rule within(?x) :- small(?x)          -- LOAD ERROR: the same
```

A clause head is therefore never *filled* from the default either: a short clause is refused,
not read as `within(3, 10)`. A clause head defines answers rather than asking for them, so filling it
would turn the author's clause into a narrower one nobody wrote; refusing it says so at the clause.
This is §1.2's rule for entity patterns read from the other side — an entity's patterns are not
filled because their author did not write the default; a rule's clause heads are not filled because
they are its definition.

The check applies only to declarations that carry at least one default, and that scope is
deliberate. No declaration carries a default today, so no program that loads now is refused. A
declaration WITHOUT a default still states its arity and enforces nothing (061); extending the check
to every declaration is WI-20260821-6WVJB's decision (one arity per predicate, which itself waits on
the operation-side WI-20260821-ZW940), and this rule is the case of it that defaults force.

**Omission at a call, positional and named.** Because a defaulted predicate has exactly its
declared arity, a short goal cannot be a call of some other-arity clause, so it is read as an
omission: positional arguments bind columns from the left and named ones by name, at a goal, a
query and a citation alike, and every column left unwritten takes its default or `?`:

```anthill
within(5)              -- within(5, 10)
within(x: 5)           -- within(5, 10)
within(5, ?)           -- every limit
```

The functional-relation view (an operation's arity + 1 goal, WI-938) cannot compete for such a
goal: 061 refuses a rule declaration whose name another construct, an operation included, already
declares. A predicate declared WITHOUT a default keeps today's meaning for a short positional goal
— a call at that arity — until 6WVJB; at a citation its omitted columns are free, as now (WI-714).

**Adding a default changes existing calls.** For an operation, an omitted argument was an error
before its parameter had a default, so adding one only makes programs load. For a rule, an omitted
column already means `?`, so declaring `?limit = 10` on an existing predicate changes every call
that omits `limit` from "every limit" to "limit 10". That is the trade-off §4 makes for
`Function.E = {}`, and it is made deliberately: the default is the author's statement of what an
unwritten column means. A caller who wants every value writes `?`.

A rule-column default follows the ordering and scoping rules of §3: it may refer to earlier columns
of the same declaration and to visible constants, constructors and operations; a forward reference
is refused. An operation call in a default is evaluated as an operation call in a rule body is
(proposal 068). The predicate has one column type: the type written on the declaration, when present,
or otherwise the relation-schema type synthesized as the join (lub) of that head column's type
across all clauses (proposal 052, *The schema `T`*; kernel-language §8.6, *What types a rule's
variables*). Schema determination completes before the declaration default is checked, and the
default must conform to that one type. Individual clause-local types do not separately admit or
reject it.

A default contributes no type information. If neither a declared column type nor the clauses
determine one, the declaration is a load error at the default: write the column type explicitly
(`rule within(?x: Int64, ?limit: Int64 = 10)`) or add a clause that types it. This includes a
defaulted declaration with no clauses and no written column type. A default outside a determined
schema is likewise a load error at the default, naming the column and its schema type.

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
receiver, written arguments, requirements, and expected result before step 4. A type application is
finalized before a later value is checked against it, wherever that type application is written.
Thus `Function[A, B]` reaches step 4 with no evidence for `E` and becomes
`Function[A, B, E = {}]`; checking an effectful callback afterward cannot reopen it. The same
expansion is made in a parameter, return, alias, field, or logical type position, so a transparent
alias cannot change whether a default applies. Conversely, `box(1)` may infer a defaulted element
parameter from `1` before its default is considered.

This amends §8.1's expansion rule: an omitted parameter is initially fresh, as today, but a fresh
variable marked with a default must be finalized by steps 4–5 before the completed type escapes its
elaboration boundary. It does not change the polarity of an explicit hole or a non-defaulted slot.

It also narrows WI-1056's rule that the four ways of leaving a parameter unwritten — a bare
reference, a partial application, an explicit `?`, and an operation type parameter — "all mean the
same thing". That rule now holds for a **non-defaulted** slot only. For a defaulted slot the
spellings split deliberately: a bare reference and a partial application omit the slot and take its
default, while an explicit `?` writes a hole and suppresses the default. So `Function` ≡
`Function[A = ?, B = ?, E = {}]` and `Function[A, B]` ≡ `Function[A, B, {}]`, but
`Function[A, B, ?]` keeps the open row. §8.1's sentence is restated as: *the four spellings agree
on a slot whose parameter declares no default; on a defaulted slot, omission takes the default and
`?` is the explicit opt-out.* (Inside the sort's own definition the restatement holds unchanged —
below.)

**A type default is context-free.** Once ordinary inference leaves a slot omitted and unbound, its
declaration default is installed wherever the type application occurs: in a parameter, return,
alias, field, construction, annotation, or logical position. Polarity continues to decide the
quantifier of a **non-defaulted** omitted slot and of an explicit `?`; it does not decide whether a
declared default exists. This preserves transparent aliases: `sort F = Function[A, B]` and a direct
`Function[A, B]` denote the same pure type in every position.

An author who wants the position's ordinary open-variable reading writes `?`. Thus a rule under
`sort Box[T = Int64]` that omits `T` matches `Box[Int64]`; one that must range over every element type
writes `Box[?]`. This does not change §1.2's rule for **entity fields**: omitting a constructor field
in a pattern still makes that field unconstrained. A sort type argument and an entity value field
are distinct slots with distinct declarations.

Under

```anthill
sort AsymmetricPair[T1, T2 = T1]
  entity apair(first: T1, second: T2)
end
```

| Written | `T1` | `T2` |
|---|---|---|
| `AsymmetricPair[Int64]` | `Int64` | `Int64` |
| `AsymmetricPair[Int64, String]` | `Int64` | `String` (written) |
| `p: AsymmetricPair` (parameter) | ∀, the skolem `p.T1` | `p.T1` — `p.T2` reduces to `p.T1` |
| `-> AsymmetricPair` (return) | ∃, a fresh `ρ` per use | that same `ρ` |
| `AsymmetricPair[?]` | an explicit hole | tied to that hole |
| `AsymmetricPair[?, ?]` | a hole | an independent hole |

So a body declared `-> AsymmetricPair` must return a pair whose component types agree; the return's
non-defaulted `T1` is existential, and the default ties `T2` to it. A body returning
`apair(1, "s")` is refused. A parameter `p: AsymmetricPair` likewise accepts `apair(1, 2)` and
refuses `apair(1, "s")`. In every position, a chain of defaults ends at a root that carries the
position's ordinary quantifier, because forward references are refused: a written slot, an explicit
`?`, a non-defaulted omitted slot, an enclosing parameter, or a closed type. `Function[A, B]` is
therefore pure in a parameter and in a return; `Function[A, B, ?]` explicitly restores the
position's open-row reading.

**Within a sort's own definition a reference to the sort is read as everywhere.** There is no self
tie for a default to yield to: proposal [070](070-self-and-fresh-bare-sorts.md) removes it. A bare
or partial reference to the sort inside its own body is the sort with each left-out slot read by the
rules above — its declared default where the parameter declares one, a fresh `?` where it does not
(070 §1.3) — and THIS instance is written `Self` (070 §1.2). A type default is context-free, and the
inside of the declaring sort is not a context of its own.

```anthill
sort AsymmetricPair[T1, T2 = T1]
  entity apair(first: T1, second: T2)
  operation second_of(p: Self) -> T2 = …               -- this instance: p: AsymmetricPair[T1 = T1, T2 = T2]
  operation is_symmetric(p: AsymmetricPair) -> Bool = … -- any SYMMETRIC pair, as outside: T2 defaults to p's T1
  operation second_of2(p: AsymmetricPair) -> T2 = …     -- refused at the definition (070 §1.4)
end
```

A default therefore cannot change what a member is about, because a member about this instance says
so. And a forgotten `Self` does not quietly load as the defaulted type: `second_of2` uses the sort's
parameter `T2` beside a `p` that is not its carrier — `p` is some symmetric pair, and no parameter is
`Self` — which 070 §1.4 refuses, naming `Self` as the repair. That rule asks what the author WROTE:
`p`'s `T2` is left out, whether or not a default then fills it. Likewise inside `sort Function`,
`Function[A, B]` is a pure function, its omitted `E` being `{}` as anywhere, and this function's own
row is `Self`, or `E = E` written out.

*History.* This paragraph first said the opposite — "the self tie wins over the default": a bare self
reference kept WI-1082's rewrite to this instance's parameters and took no default, since taking it
"would change what a member is about". That was written in pre-`Self` terms and described the code
before 070; the user's reading of it (2026-10-03) was that `p` there IS `Self`, and 070 now writes
it. For one day (2026-10-04) 070 refused the bare spelling inside the sort outright, and this section
said so; the refusal was withdrawn the same day ("it should be the same as `Cell[V = ?]`") in favour
of the carrier rule, which is what guards `second_of2` above.

*For the implementation (WI-20261003-QV5W5).* 070 §1.4's carrier check
(`check_sort_parameter_carriers`) must go on reading a slot the author left out as LEFT OUT. It reads
the stored signature, where such a slot is simply absent today; once a default is installed into it,
a slot holding the default is neither the carrier nor open — `second_of2` would load — so the check
has to be given what the author wrote. (Until 070's stage (e), 2026-10-04, the loader wrote an
anonymous `?` into each slot a reference to the ENCLOSING sort left out, and this note carried a
second obligation: that fill had to leave a DEFAULTED slot out, an explicit `?` being this proposal's
opt-out. Stage (e) deleted the fill, and with it the obligation.)

The polarity rules continue to govern explicit `?`, named variables and non-defaulted slots.
`f: Function[A, B, ?]` is universal in its open row, while `-> Function[A, B, ?]` is existential in
it. Both differ from `Function[A, B]`, whose omitted `E` takes `{}` in either position. WI-1082's “a
member may not pin its own sort's parameter to a constant and still elide it in the return” needs no
rule of its own after 070: a return that writes this instance (`Self`, or `E = E`) is refused at a
body that pins the parameter; one that leaves a non-defaulted slot out is an existential, opened at
each call, and proves nothing to a consumer; and a defaulted slot left out is its default, in the
declaring sort as anywhere.

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
For an operation parameter, its effects are effects of the operation and must fit the operation's
declared effect row. Supplying an explicit argument may avoid executing a default, but does not
narrow the operation's declared effect upper bound.

An entity-constructor default must be **pure**. Entity constructors have no effect contract in which
to declare a default's effects, and construction must not acquire an effect merely because a field
was omitted. A constructor default whose inferred effect row is non-empty is a load error at that
default. Introducing effectful constructors and propagating their rows at each construction site
would be a separate language change.

Calls in operation bodies, rule-body functional fragments, top-level queries, and constructor
expressions use the same coverage and insertion rule. A logical variable written as an argument is
an argument, not an omission. Pattern positions never insert constructor defaults; in a rule body,
an entity application is a pattern in a logical position and a construction as an argument of an
operation call (§1.2, *In a rule body, the position decides*).

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

## 4. `Function[A, B]` supersedes §4.4's open-row verdict

`Function` declares:

```anthill
effects E = ? default {}
```

Consequently:

- the arrow syntax `(A) -> B` WRITES the empty row: it is `Function[A, B, {}]`, not an omission,
  so it is pure in every position, a return included;
- `Function[A, B]` takes the default `{}` in every position, so parameters, annotations, bounds,
  returns and transparent aliases agree that it is pure;
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
- A rule-column default mismatch names the column's declared or synthesized relation-schema type,
  not an arbitrary clause that contributed to it.
- A defaulted rule column with no declared or clause-synthesized type is refused at the default and
  suggests a typed declaration column; the default itself is not used to invent its schema type.
- An effectful entity-constructor default is refused at the default and names its inferred effects;
  constructors have no effect contract to admit them.
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
   metadata and value defaults on the canonical operation signature. Refuse an entity-constructor
   default whose inferred effect row is non-empty.
3. Change type-parameter inference to mark omitted defaulted slots, solve without defaults, install
   defaults in declaration order, then resume solving before final validation. Preserve explicit
   `?` as the opt-out.
4. Change operation-call and entity-construction checking to complete missing value slots after
   type-parameter finalization. Keep the resulting runtime call/constructor at full arity, and do
   not fill omitted fields in pattern positions.
5. Thread defaults through reflection, persistence, Rust/Scala code generation, and diagnostics.
6. Declare `Function.E` as `default {}` and remove every special “unbound means empty” reading.
   Restate kernel-language §8.1's WI-1056 sentence ("the four ways of leaving a parameter unwritten
   … all mean the same thing") as holding for non-defaulted slots only (§2), and add to §8.1's
   polarity section (WI-1063) that a declaration default is installed context-free, while polarity
   continues to govern explicit holes and non-defaulted slots; state that transparent aliases do
   not change whether a default applies, and that inside the declaring sort a reference to it is
   read as anywhere (proposal 070 §1.3) — the default applies there too, and this instance is
   `Self`. Restate §4.4 with the superseded 2026-10-03 verdict and the new explicit opt-out.
6a. Admit `?v = e` in a rule declaration head as a column default (amending 061's list of what a
   declaration may not carry); refuse it in clause and `fact` heads after a census of existing
   `?v = e` head arguments; refuse a clause or `fact` whose arity differs from a defaulted
   declaration; compose with 061's typed declaration columns, using a written type as authoritative
   and otherwise synthesizing the relation schema across all clauses before checking each column
   default against its one schema type; refuse a defaulted column for which neither route determines
   a type; insert defaults at goal omissions (positional and named), queries and citations
   (`resolve_relation_arg_columns` and the goal path share one owner), never in heads.
7. Replace WI-850's refusal tests with driven calls, and add controls proving that removing default
   application changes the result or restores the old error.

## 8. Acceptance

- `Function[A, B]` is structurally the same effect instantiation as `Function[A, B, E = {}]`, and
  rejects an effectful callback where a pure one is required.
- `Function[A, B, ?]` remains open and accepts an effect row inferred by its context.
- Arrow `(A) -> B` and `Function[A, B]` agree in parameters, returns, aliases and logical positions
  without a special-case “missing E means empty” branch; both `-> (A) -> B` and
  `-> Function[A, B]` are pure.
- `Box[T = Int64]` defaults an omitted `T`, while `Box[?]` remains open and `Box[String]` overrides
  the default.
- A dependent sort default (`Values = List[T = K]`) expands after `K`; a forward reference and a
  kind mismatch are loud declaration errors.
- Under `sort AsymmetricPair[T1, T2 = T1]`: a bare parameter `p: AsymmetricPair` accepts
  `apair(1, 2)` and refuses `apair(1, "s")`, with `p.T2` reducing to `p.T1`; a bare return
  `-> AsymmetricPair` opens `T1` existentially and defaults `T2` to that same witness, so a body
  returning `apair(1, "s")` is refused. INSIDE THE SORT the same holds (§2, "read as everywhere"): a
  member taking `p: Self` accepts an asymmetric instance and returns its `T2`; a member taking a bare
  `p: AsymmetricPair` is the symmetric pair it is outside, and refuses `apair(1, "s")`; and
  `second_of2(p: AsymmetricPair) -> T2` is refused at its definition for want of a carrier (proposal
  070 §1.4). Control: with the loader's `?` still written into a defaulted slot of the enclosing
  sort's own reference, the bare in-sort member accepts the asymmetric instance.
- `f: Function[A, B]` is not universal in `E` (an effectful argument is refused), and
  `f: Function[A, B, ?]` restores ∀. `-> Function[A, B]` is pure (a body returning an effectful
  function is refused), while `-> Function[A, B, ?]` restores the existential open row.
- Under `sort Box[T = Int64]`, an omitted `T` in a logical position matches only `Box[Int64]`; an
  explicit `Box[?]` ranges over every element type.
- A constraint introduced by a dependent default is propagated by the second solver phase and may
  determine an earlier still-free parameter; defaults are not selected a second time.
- `operation identity[T = String](x: Option[T] = none()) -> T` uses inference before `T`'s default,
  uses the default when no source binds `T`, and honors an explicit call-site override.
- A value default referring to an earlier parameter evaluates once and is type/effect checked. An
  operation default's effects fit its operation's declared row; an entity-constructor default with
  a non-empty inferred effect row is refused.
- `Endpoint(port: 8080)` fills a defaulted `host`, while an omitted `host` in an `Endpoint` pattern
  remains unconstrained and matches stored non-default hosts too.
- In a rule body, `Endpoint(port: 80)` as a goal or an argument of a rule goal matches stored
  `Endpoint`s with any host, while the same text as an argument of an operation call constructs
  `Endpoint("localhost", 80)` — the value the call receives in an operation body too.
- Missing required parameters remain errors, including a required parameter declared after a
  defaulted one.
- In a rule-body goal on `clamp(x, low = 0, high = 100) -> Int64`: `clamp(12, result: ?r)` binds
  `?r = 12` with both defaults; `clamp(12, 0, 100, ?r)` is the functional view as today; and
  `clamp(12, ?r)` is a load error naming `result:`. A `Bool` operation's short goal succeeds when
  the call with defaults returns `true`.
- Calls through function values still require full arity.
- Spec dispatch uses the spec declaration's defaults and refuses implementation-local redeclaration.
- A declared rule column's default fills an omission — positional or named — at a goal, a query and
  a citation, and is checked against the clauses' answers when the column is an output; an explicit
  `?` still ranges over every value; a column with no default stays free.
- A rule-column default is checked once against its declared schema type, or against the synthesized
  relation-schema LUB after all clauses have contributed when no type is declared. Clause-local
  types do not independently accept or reject it, a default outside the schema is a load error
  naming that type, and a defaulted column for which neither route determines a type is refused
  rather than inferred from the default.
- A default written on a clause head or a `fact` head is refused naming the declaration; `?v = e` in
  a clause head is refused rather than read as an equation term.
- Against a declaration with a default, a clause or `fact` at another arity is a load error naming
  the declaration; a declaration without one still enforces no arity.
- Rust tests run through `rustland/scripts/test.sh`; `sbt testFull` and tree-sitter corpus tests pass.

## 9. Non-goals

- Default operation bodies and default providers are unrelated mechanisms.
- Defaults do not introduce partial application, variadic arguments, overloaded arities, or an
  optional-parameter bit in arrow types.
- A default is not an error-recovery fallback. It applies only to an omitted slot.
- Constructor defaults do not change pattern omission, stored entity shape, or field subtyping.
- A rule column's default is never written per clause, and never fills a clause head (rule clause or `fact`).
- This proposal does not decide one arity per predicate in general (WI-20260821-6WVJB); it enforces
  arity only for a declaration that carries a default.
