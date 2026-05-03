# Scala Forward Mapping

This document defines how anthill kernel constructs map to Scala 3 code — the **forward direction**: from specification to skeleton. The inverse direction (linking existing Scala code back to specs) is handled by `Implementation` facts (kernel spec §8.5, §8.7) and (in the future) by `scala-anthill-gen` per [proposal 034](proposals/034-scala-mapping-split.md).

This is the Scala counterpart to [`docs/rust-forward-mapping.md`](rust-forward-mapping.md). Mapping decisions deviate from the Rust mapping only where Scala idioms differ; structurally, the two documents are parallel.

## 1. Overview

An anthill namespace declares an **algebra**: abstract sorts, operations with contracts, and laws. The forward mapping generates Scala **skeletons** — traits, case classes, enums, and method signatures — from these declarations. The generated code is compilable but incomplete: operation bodies are `???` (Scala's `todo!()` analog), to be filled in by a developer or agent.

The mapping is deterministic: given the same anthill source, the same Scala code is produced. The generated code serves as a starting point; once an implementation exists, an `Implementation` fact (§8) links the code back to the spec for verification.

**Codegen correctness requirement**: The generated Scala code must be directly implementable — filling in `???` bodies with real logic, without changing method signatures, types, or package structure. If a generated signature cannot be implemented as-is, the fix belongs in the codegen rules or the anthill spec, not in post-hoc edits.

**Target language version**: Scala 3.3+ (LTS). The `enum` keyword, top-level definitions, intersection / union types, and context functions are part of the baseline.

## 2. Mapping Rules

### Summary Table

| Anthill construct | Scala construct |
|---|---|
| `namespace N` | `package n` (top-level) or `object N` (nested) |
| Sort with operations (no constructors) `sort S { operation ... }` | `trait S` |
| Sort with constructors `sort S { entity C₁(...), entity C₂(...) }` | `enum S { case C1(...); case C2(...) }` |
| Standalone `entity E(fields)` | `case class E(...)` |
| `operation op(a: S, ...) -> R` (first arg is enclosing sort) | `def op(...): R` on the trait |
| `operation op(a: S, ...) -> ...S...` (return contains S) | `def op(...): Self`-typed (when `Self` makes sense) |
| `operation op(x: A, y: B) -> R` (no self-arg) | top-level `def` in a `{Namespace}Ops` object |
| `effects (Modify X)` | `def op(...): X` returning the updated state (immutable) — see §3 for alternatives |
| No effects | plain `def op(...): R` |
| `effects (Error)` or `effects (Error E)` | `Either[E, R]` return (default profile) |
| `effects (Requires Cap)` | `(using Cap)` context parameter |
| `sort T` (abstract sub-sort = type parameter) | `[T]` type parameter |
| `requires Eq[T]` | upper bound or `using Eq[T]` |
| `fact SortName` (inside sort body) | `extends SortName` |
| `fact SortName` (in entity's namespace) | `given SortName.Of[Entity] = …` |
| `List[T = X]` | `List[X]` (Scala `scala.collection.immutable.List`) |
| `Option[T = X]` | `Option[X]` |
| `rule` (law) | ScalaCheck property in `Test` source set |
| `Quoted("scala", source)` | verbatim Scala code inserted as-is |
| `constraint` (denial) | `assert(...)` or test-time check |
| `import N.{A, B}` | `import n.{A, B}` |

### 2.1 Namespace → Package or Object

A top-level `namespace` becomes a Scala `package`; nested namespaces become nested `object`s (Scala packages can't be nested inline). Names are kept as-written; hyphens become underscores.

```
namespace banking                →  package banking { ... }
namespace anthill.prelude        →  package anthill.prelude { ... }
namespace banking.transfers      →  package banking { object transfers { ... } }
```

Exports: `export`-prefixed items keep their default Scala visibility (public). `internal` items get `private[packageName]`.

### 2.2 Sort with Operations (No Constructors) → Trait

A sort whose body contains operations but no entity constructors maps to a Scala trait. Operations become abstract methods. Abstract sub-sorts (no body, just `sort T = ?`) become type parameters.

```
sort Store {                                trait Store {
  operation persist(             →            def persist(...): FactId
    store: Store, ...) -> FactId            }
  ...
}

sort Eq {                                   trait Eq[T] {
  sort T                         →            def eq(a: T, b: T): Boolean
  operation eq(a: T,                          def neq(a: T, b: T): Boolean
    b: T) -> Bool                           }
  operation neq(a: T,
    b: T) -> Bool
}
```

**Self-substitution.** Inside trait method signatures, the enclosing sort's *type parameter* maps to the trait's type parameter — Scala's `Self` is less idiomatic than Rust's, so we **don't** substitute a `Self` token in most places. Where Rust would say `fn foo(self) -> Self`, Scala says `def foo(self: T): T` (when `T` is the trait's parameter) or uses an F-bounded pattern when generic recursion is needed.

```
sort Stream {                               trait Stream[T, E] {
  sort T                         →            def splitFirst(s: Stream[T, E]): Option[(T, Stream[T, E])]
  sort E                                      def tail(s: Stream[T, E]): Stream[T, E]
  operation split_first(                      def isEmpty(s: Stream[T, E]): Boolean
    s: Stream) -> Option{...}               }
  operation tail(s: Stream)
    -> Stream
  operation isEmpty(s: Stream)
    -> Bool
}
```

(F-bounded `trait Stream[Self <: Stream[Self, T, E], T, E]` is reserved for sorts that genuinely need self-typing — flagged by a future codegen knob.)

### 2.3 Sort with Constructors → Enum

A sort with entity constructors maps to a Scala 3 `enum`. Each constructor becomes a `case`:

```
sort WorkStatus {                           enum WorkStatus {
  entity Draft                   →            case Draft
  entity Open                                 case Open
  entity Claimed(agent: String,               case Claimed(agent: String, since: String)
    since: String)                            case Verified(at: String)
  entity Verified(at: String)               }
}
```

Nullary constructors become parameterless `case`s; constructors with fields become parameterized.

When the enum sort also has operations, those become methods on the enum's companion object:

```
sort LogicalStream {                        enum LogicalStream[T] {
  sort T                                      case Empty
  entity Empty                   →          }
  operation pure(x: T)                      object LogicalStream {
    -> LogicalStream                          def pure[T](x: T): LogicalStream[T] = ???
  operation mplus(                            def mplus[T](a: LogicalStream[T],
    a: LogicalStream,                                      b: LogicalStream[T]): LogicalStream[T] = ???
    b: LogicalStream)                       }
    -> LogicalStream
}
```

### 2.4 Standalone Entity → Case Class

A standalone `entity` (sugar for a single-constructor sort) maps to a `case class`:

```
entity Account(                             case class Account(
  id: AccountId,                 →            id: AccountId,
  balance: Money                              balance: Money
)                                           )
```

### 2.5 Operation → Method or Function

Operations map to either trait methods or top-level methods, depending on the self-arg heuristic (§4):

```
-- Method:
operation balance(a: Account) -> Money
→  def balance(a: Account): Money = a.balance

-- Top-level:
operation route(fact: Term) -> Store
→  def route(fact: Term): Store = ???       // in <package>Ops
```

### 2.6 Type Parameters → Generics

An abstract `sort T` declared inside a sort body maps to a Scala generic:

```
sort List {                                 enum List[T] {
  sort T                         →            case Nil
  entity nil                                  case Cons(head: T, tail: List[T])
  entity cons(head: T,                      }
    tail: List)
}
```

### 2.7 Requires → Trait Bounds or Context Parameters

A `requires` declaration can be either a type-class supertrait or a `using` context parameter, depending on the call shape:

```
sort Ordered {                              trait Ordered[T] extends Eq[T] {
  sort T                         →            def gt(a: T, b: T): Boolean
  requires Eq[T]                              ...
  operation gt(a: T,                        }
    b: T) -> Bool
}
```

When the requires binds a specific type, it becomes a `using` context parameter at use sites:

```
sort PolynomOps {
  requires Ring[T = Coeff]       →          def add[Coeff](a: Polynom[Coeff],
  operation add(a: Polynom,                              b: Polynom[Coeff])
    b: Polynom) -> Polynom                              (using Ring[Coeff]): Polynom[Coeff] = ???
}
```

### 2.8 Effects → Method Shape

The default `scala_std` profile (per `stdlib/anthill/realization/scala_std.anthill`) maps:

| Anthill effect | Scala shape |
|---|---|
| (none) | plain `def op(args): R` |
| `Modify X` | `def op(s: X, args): X` returning the updated state (immutable) |
| `Error` or `Error(E)` | `def op(args): Either[E, R]` |
| `Requires Cap` | `def op(args)(using Cap): R` |
| `Console` | `def op(args): R` (default — `scala_cats_effect` profile would wrap in `IO[R]`) |
| Multiple effects | composed: `(s: S, args)(using Cap): Either[E, (S, R)]` |

The `scala_cats_effect` and `scala_zio` profiles re-map `Modify` / `Error` / `Console` into their respective effect monads. These are alternative profiles, not the default.

### 2.9 Rules (Laws) → ScalaCheck Properties

Rules generate ScalaCheck property stubs in the `Test` source set:

```
sort Monoid {                               // Test source:
  rule add_assoc(?a, ?b, ?c)     →          property("add_assoc[Monoid]") {
    : add(add(?a, ?b), ?c)                    forAll { (a: T, b: T, c: T) =>
    = add(?a, add(?b, ?c))                      add(add(a, b), c) == add(a, add(b, c))
}                                             }
                                            }
```

### 2.10 Quoted → Verbatim Insertion

A `Quoted("scala", "...")` term in a sort/operation body is inserted verbatim into the generated Scala source:

```
operation hash(s: String) -> Int =
  Quoted("scala", "s.hashCode")
→  def hash(s: String): Int = s.hashCode
```

### 2.11 Constraint → Assert / Test

A `constraint` (denial) maps to a `assert(...)` at the relevant scope, or a test-time check in the `Test` source set:

```
constraint balance_nonneg
  : balance(?a) >= 0
→  // In test source:
   property("balance_nonneg") { … assert(balance(a) >= 0) … }
```

### 2.12 Import → Import

```
import banking.{Account, Money}
→  import banking.{Account, Money}
```

## 3. Effect-system profile choices

The `scala_std` profile is intentionally *purely-functional but non-monadic*: `Modify` returns updated state, `Error` returns `Either`, no `IO`/`ZIO` machinery. This keeps the bootstrap-codegen path simple and the generated code dependency-free.

Two alternative profiles are reserved for future work:

- `scala_cats_effect` — `Modify X` becomes `cats.effect.Ref[IO, X]`, `Error E` becomes `IO` with `MonadError`, `Console` becomes `cats.effect.std.Console[IO]`.
- `scala_zio` — analogous with `ZIO[R, E, A]`.

These profiles are selected via `LanguageMapping(language: "scala", profile: some("cats-effect"))` etc. The default profile (no `profile:` field specified) is `scala_std`.

## 4. Self-arg heuristic

Same heuristic as Rust (`docs/rust-forward-mapping.md` §4): if an operation's first argument has the type of the enclosing sort, the operation maps to a method on that sort's trait/enum (Scala doesn't have an explicit `self` token like Rust's `&self` — the first parameter is the natural receiver).

## 5. Naming conventions

- Anthill identifiers stay as-written. Snake_case stays snake_case (Scala-idiomatic camelCase conversion is *not* automatic — that's a project decision and would belong in a `NamespaceMapping` fact, not in baseline codegen).
- Operator-named operations (e.g. `+` mapped from `add`) stay as method names, not symbolic operators (Scala 3 allows symbolic methods but they're not free; explicit naming is more grep-friendly).

## 6. Cross-references

- [029-rust-mapping-split.md](proposals/029-rust-mapping-split.md) — the architectural split this document mirrors.
- [034-scala-mapping-split.md](proposals/034-scala-mapping-split.md) — the Scala-specific split based on this mapping.
- `stdlib/anthill/realization/scala_std.anthill` — the `LanguageMapping` facts that codegen reads from the KB.
- `docs/rust-forward-mapping.md` — the Rust counterpart; structurally parallel.
