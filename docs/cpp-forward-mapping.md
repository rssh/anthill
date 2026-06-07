# C++ Forward Mapping (Draft)

This document defines how anthill kernel constructs map to C++ — the **forward direction**: from specification to skeleton. Backward direction (linking existing C++ to specs) is not covered: for existing C++ APIs, hand-author `stdlib/anthill/<vendor>/` sorts plus `Implementation` / `NamespaceMapping` facts.

Status: **Draft**. Profile: `cpp17-stl` (the only one for now). C++17 is the safe baseline because webots's own utilities build with `-std=c++17` and its public headers use only modest pre-C++17 idioms — C++20 cannot be assumed for webots-side consumers. Unreal Engine and embedded-no-STL profiles are explicit non-goals here; they slot in later as additional profiles when concrete consumers force them.

## 1. Overview

A namespace declares an algebra: abstract sorts, operations with contracts, laws. The forward mapping generates C++ skeletons — `concept`s, classes, `struct`s, function signatures — from these declarations. Operation bodies are `// TODO:` placeholders.

The mapping is deterministic: same anthill source → same C++ output.

**Codegen correctness requirement**: generated code must be directly implementable — filling in `// TODO:` bodies with real logic without changing signatures, types, or namespace structure. If a signature cannot be implemented as-is, fix the codegen rules or the spec, not the generated output.

## 2. Profile: `cpp17-stl`

| Aspect | Choice |
|---|---|
| C++ standard | C++17 minimum |
| Containers | STL (`std::vector`, `std::optional`, `std::variant`, `std::string`) |
| Error effect | `tl::expected<T, E>` (header-only, C++11+; switch to `std::expected` once C++23 is the baseline) |
| Polymorphism for sorts with ops | traits-class template (`template<typename T...> struct SortName { static fns; };`) — disambiguates by sort name |
| Polymorphism for sorts with constructors | `std::variant` of constructor structs |
| `requires` enforcement | `static_assert` with `anthill::detail::is_satisfied_v<...>` at the top of each method body; specializations carry an `anthill_satisfied` marker |
| Memory | value semantics; `std::unique_ptr` / `std::shared_ptr` only where the spec demands erasure |
| Smart-pointer policy | none by default (anthill values are values) |
| Compiler | clang or gcc; MSVC supported but not the primary target |

C++20 `concept` is deliberately not used: webots's user-controller toolchain does not guarantee C++20. C++17 enforcement is achieved via the detection-idiom + `static_assert` pattern documented in §3.11 — `requires` clauses are real compile-time constraints, not just comments. Upgrading to `concept`-based mapping is a future profile (`cpp20-stl`) that improves diagnostics and lets users write concept-constrained generics on top of the same traits classes.

UE and no-STL profiles will define their own mappings for containers, strings, and macro decoration. They are not covered here.

## 3. Mapping rules

### Summary

| Anthill | C++ (cpp17-stl profile) |
|---|---|
| `namespace N` | `namespace n {}` (lowercase, dots → nested) |
| Sort with abstract sub-sort + ops | `template<typename T...> struct SortName { static-method per op; };` (traits-class idiom) |
| Sort with no abstract sub-sort, ops only | non-template `struct SortName { static-method per op; };` |
| Sort with constructors | `struct C1 { ... }; struct C2 { ... }; using S = std::variant<C1, C2>;` |
| Sort with constructors AND operations | both: `using S = std::variant<...>;` plus a traits-class `struct SortNameOps { ... };` over `S` |
| Standalone entity | `struct E { ... };` |
| `operation op(a: T, ...) -> R` inside `sort S[T]` | static method on `S<T>`: `static R op(const T& a, ...);` |
| `operation op(a: S, ...) -> ...S...` | by-value return on the static method |
| `effects (Modify X)` | non-const reference param (`X&`) on the static method |
| No effects | pure return; method body free of side effects |
| `effects (Error)` / `effects (Error E)` | static method returns `tl::expected<R, Error>` or `tl::expected<R, E>` |
| `effects (Requires Cap)` | extra template parameter on the traits-class or capability struct passed at call |
| `sort T` (abstract sub-sort) | template parameter on the traits-class |
| `requires Eq[T]` | `static_assert(is_satisfied_v<Eq<T>>, "...")` at top of each method body; calls go through `Eq<T>::eq(...)` |
| `fact SortName[bindings]` (entity-side) | template specialization `template<> struct SortName<EntityType> { using anthill_satisfied = std::true_type; ... };` |
| `List[T = X]` | `std::vector<X>` |
| `Option[T = X]` | `std::optional<X>` |
| `String` | `std::string` |
| `Int64` | `int64_t` |
| `Float` | `double` |
| `Bool` | `bool` |
| `import N.{A, B}` | full qualification by default; optional `using N::A;` |
| `rule` (law) | Catch2 test stub (`TEST_CASE("...") { /* TODO */ }`) |
| `Quoted("cpp", source)` | inserted verbatim |
| `constraint` (denial) | `assert(...)` or test-time check |

### 3.1 Namespace → namespace

```
namespace anthill.prelude    →   namespace anthill::prelude { ... }
namespace banking            →   namespace banking { ... }
```

Names are lowercased; dots become C++17 nested-namespace syntax. `export`-prefixed items have no extra decoration (everything in a namespace is accessible by qualified name); `internal` items go inside an unnamed `namespace { ... }` block.

### 3.2 Sort with operations → traits-class template

A sort with operations maps to a **traits-class template** — `template<typename T...> struct SortName { static-method per operation; };`. The sort name itself disambiguates operations across sorts, so two anthill sorts with an `eq` operation produce two distinct C++ types and never collide.

```anthill
sort Eq
  sort T
  operation eq(a: T, b: T) -> Bool
  operation neq(a: T, b: T) -> Bool
end
```

becomes

```cpp
namespace anthill::prelude {

// Sort: Eq[T]
//   Specialize this template for a type T to claim T satisfies Eq.
template <typename T>
struct Eq {
    static bool eq(const T& a, const T& b);   // TODO
    static bool neq(const T& a, const T& b);  // TODO
};

} // namespace anthill::prelude
```

Calls always go through the trait class:

```cpp
bool same = anthill::prelude::Eq<int64_t>::eq(x, y);
```

User satisfaction is full or partial specialization. **Every specialization must declare an `anthill_satisfied` marker** so detection traits can tell it apart from the unspecialized primary template:

```cpp
template <>
struct anthill::prelude::Eq<int64_t> {
    using anthill_satisfied = std::true_type;
    static bool eq(int64_t a, int64_t b)  { return a == b; }
    static bool neq(int64_t a, int64_t b) { return a != b; }
};

// Partial specialization works (function templates couldn't allow this):
template <typename T>
struct anthill::prelude::Eq<std::vector<T>> {
    using anthill_satisfied = std::true_type;
    static bool eq(const std::vector<T>& a, const std::vector<T>& b);
    static bool neq(const std::vector<T>& a, const std::vector<T>& b);
};
```

The marker is mechanical; codegen always emits it. `requires`-driven `static_assert`s elsewhere in the codebase use it to detect satisfaction (see §3.11).

**Sorts with no abstract sub-sort** (e.g. `sort Console` with operations but no `sort T`) become non-template structs:

```cpp
struct Console {
    static void print(const std::string& s);
};
```

**Sorts with constructors AND operations** get both: a `std::variant` for the data plus a traits-class struct for the operations. Convention: the traits class is named `SortNameOps` to keep the data type name (`SortName`) free for the variant alias.

The traits-class idiom is the established C++ pattern — `std::numeric_limits<T>`, `std::iterator_traits<T>`, `std::hash<T>`, `std::char_traits<T>` all use it. Combined with the `anthill_satisfied` marker and `static_assert` enforcement (§3.11), it gives `concept`-equivalent compile-time checking without requiring C++20.

### 3.3 Sort with constructors → `std::variant`

```anthill
sort Shape
  entity Circle(radius: Float)
  entity Square(side: Float)
end
```

becomes

```cpp
namespace geom {

struct Circle { double radius; };
struct Square { double side;   };

using Shape = std::variant<Circle, Square>;

} // namespace geom
```

Operations on `Shape` are written via `std::visit` or pattern-matching helpers. Constructor names become struct names; field names become member names. Unit constructors (no fields) become empty structs.

### 3.4 Standalone entity → `struct`

```anthill
entity Account(owner: String, balance: Int64)
```

becomes

```cpp
struct Account {
    std::string owner;
    int64_t balance;
};
```

Field order in the struct matches anthill's canonical ordering (sorted by field name). Equality / comparison operators are not generated automatically — they are derived only when the corresponding `fact Eq[T = Account]` is asserted, in which case `bool operator==(const Account&) const = default;` is emitted.

### 3.5 Operations

All operations of a sort live as static methods on its traits-class struct. There is no member-function call style and no free-function call style — the disambiguation problem from §3.2 is the reason. Three syntactic shapes:

- **Operation in a sort with abstract sub-sort `T`** → static method on `SortName<T>`:
  ```cpp
  // operation eq(a: T, b: T) -> Bool   in anthill.prelude.Eq
  template <typename T>
  struct Eq {
      static bool eq(const T& a, const T& b);
  };
  // call:  Eq<int64_t>::eq(x, y)
  ```
- **Operation that returns `Self`-flavored result** → by-value return; copy elision / RVO handle ownership:
  ```cpp
  template <typename T>
  struct Numeric {
      static T add(const T& a, const T& b);
  };
  // call:  Numeric<int64_t>::add(x, y)
  ```
- **Operation in a sort with no abstract sub-sort** → static method on a plain struct:
  ```cpp
  // operation max(a: Int64, b: Int64) -> Int64   in anthill.prelude.Int64
  struct Int64 {
      static int64_t max(int64_t a, int64_t b);
  };
  // call:  Int64::max(x, y)
  ```

### 3.6 Effects

| Anthill effect | C++ encoding |
|---|---|
| (none) | `R foo(const Args&...) const` (or free fn returning `R` directly) |
| `Modify X` | `X` parameter passed as `X&` (non-const), function not `const`-qualified |
| `Error` / `Error E` | return `tl::expected<R, Error>` or `tl::expected<R, E>` |
| `Modify X, Error` | both: `X&` param + `tl::expected<R, Error>` return |
| `Requires Cap` | template parameter constrained by `Cap` concept |
| Multiple `Modify` | each modifies its own parameter |

Exceptions are not used for `Error` effect — the spec is explicit that errors are values, and `tl::expected` keeps them in the type. C++ exceptions remain available for genuinely exceptional conditions (allocation failure, etc.) but are outside the mapping.

### 3.7 Type parameters

`sort T` inside a sort body (an abstract sub-sort) becomes a template parameter on the traits-class struct. Multi-parameter sorts get multi-parameter struct templates:

```anthill
sort Container
  sort T
  sort Self
  operation insert(s: Self, x: T) -> Self
  operation contains(s: Self, x: T) -> Bool
end
```

becomes

```cpp
// Sort: Container[Self, T]
template <typename Self, typename T>
struct Container {
    static Self insert(Self s, const T& x);          // TODO
    static bool contains(const Self& s, const T& x); // TODO
};
// call:  Container<MyVec, int64_t>::insert(v, 42)
```

Named arguments in anthill (sorted by field name canonically) carry through to C++ parameter names directly.

### 3.8 Spec satisfaction

Anthill `fact Eq[T = Int64]` declares `Int64` satisfies `Eq`. In C++ this is a full template specialization of the trait class with the `anthill_satisfied` marker:

```cpp
namespace anthill::prelude {

template <>
struct Eq<int64_t> {
    using anthill_satisfied = std::true_type;
    static bool eq(int64_t a, int64_t b)  { return a == b; }
    static bool neq(int64_t a, int64_t b) { return a != b; }
};

}
```

For user-defined entities, the same shape: when `fact Eq[T = Account]` is asserted in the entity's namespace, an explicit specialization is emitted there with the marker. Partial specialization works for parameterized satisfactions (`fact Eq[T = List[T = ?U]]` becomes `template<typename U> struct Eq<std::vector<U>> { using anthill_satisfied = std::true_type; ... };`).

Codegen always emits the marker; users hand-writing additional specializations (e.g. for native C++ types they own) must include it as well, or the `static_assert` at the use site will reject the type even though the trait methods exist.

### 3.11 `requires` and substitutions

A `requires` clause becomes a compile-time check that the required trait class is specialized for the substituted type arguments.

**Sort-level `requires`:**

```anthill
sort Sorted
  sort T
  requires Ordered[T]

  operation sort(xs: List[T = T]) -> List[T = T]
end
```

becomes

```cpp
namespace anthill::prelude {

// Sort: Sorted[T]
//   Requires: Ordered<T>
template <typename T>
struct Sorted {
    static std::vector<T> sort(std::vector<T> xs) {
        static_assert(::anthill::detail::is_satisfied_v<Ordered<T>>,
                      "Sorted<T> requires Ordered<T> to be specialized "
                      "(declare 'fact Ordered[T = ...]' in anthill).");
        // TODO
    }
};

}
```

Inside the body, calls go through `Ordered<T>::compare(a, b)`. The substitution from `requires Ordered[T]` (`Ordered`'s `T` ↦ enclosing `T`) is just template argument plumbing.

**Substitutions** map directly to template arguments at the call site:
- `requires Eq[T]` → `Eq<T>::eq(...)` and a `static_assert` on `is_satisfied_v<Eq<T>>`.
- `requires Eq[T = Pair[A = T, B = S]]` → `Eq<std::pair<T, S>>::eq(...)` and a `static_assert` on `is_satisfied_v<Eq<std::pair<T, S>>>`.
- `requires Ordered[T = K], Eq[T = K]` (multi-requires) → one `static_assert` per requires, both substituting `K` for the trait's type parameter.

**Operation-level `requires`** (vs. sort-level) just means the `static_assert` is emitted inside that one method's body, not in every method.

**Detection helper.** Codegen emits this trait once into a generated header (`anthill_runtime.hpp` or per the namespace mapping):

```cpp
namespace anthill::detail {

template <typename Tr, typename = std::void_t<>>
struct is_satisfied : std::false_type {};

template <typename Tr>
struct is_satisfied<Tr, std::void_t<typename Tr::anthill_satisfied>>
    : std::true_type {};

template <typename Tr>
inline constexpr bool is_satisfied_v = is_satisfied<Tr>::value;

}
```

Three pieces — the marker on every specialization, the detection trait in the runtime header, and the `static_assert` at the top of each method body. Together they enforce `requires` at compile time without `concept`.

**Substitution at rule sites.** When an anthill `rule` body references an operation from a required sort (e.g. `Ordered.lte(?a, ?b)` inside a `rule` of `Sorted[T]`), codegen emits `Ordered<T>::lte(a, b)` — the substitution from the `requires` carries through.

### 3.9 Imports

Default: emit fully qualified names everywhere (`anthill::prelude::eq(...)`). Optional codegen flag `--use-declarations` emits `using anthill::prelude::eq;` at the top of the importing namespace. `using namespace` is never emitted.

### 3.10 Quoted blocks and constraints

`Quoted("cpp", source)` inserts `source` verbatim at the corresponding position. `constraint` becomes either an `assert(...)` at the relevant operation entry/exit or a Catch2 test, depending on whether the constraint references runtime values or static facts.

## 4. Implementation facts

`Implementation` facts (kernel spec §8.5) link existing or generated C++ to anthill specs. For forward codegen, an `Implementation{T = MyAnthillSort, target = "cpp17-stl", profile = cpp17_stl}` fact tells the mapper to emit the skeleton in a specific module path, picked from the associated `NamespaceMapping`.

`CarrierBinding` facts pick concrete C++ types for abstract sorts: `CarrierBinding{sort = Money, carrier = "::cents::Cents"}` makes the codegen emit `cents::Cents` instead of generating a fresh struct.

**Generated runtime header.** Each codegen run emits one shared header (`anthill_runtime.hpp`, or one per top-level namespace) containing the `anthill::detail::is_satisfied` detection trait used by `requires` enforcement (§3.11). All other generated headers `#include` it.

## 5. Webots and blefusku consumers

These two drive the cpp20-stl profile:

- **webots**: `stdlib/anthill/webots/` (to be authored) declares anthill sorts for `Robot`, `Camera`, `Gps`, etc., with `NamespaceMapping` facts pointing at `webots::Robot`, `webots::Camera`, `webots::GPS`. anthill specs that import these compile into C++ controllers calling the webots API directly. Webots's user-controller toolchain is the reason the profile baseline is C++17, not C++20.
- **blefusku**: actor specs satisfy a stdlib `anthill.actor.ActorBehavior` sort. The C++ emitter generates handler methods against protoc-produced types; `NamespaceMapping` facts align anthill names with `blefusku_proto::*` names. The proto envelope is emitted separately by `anthill-proto-gen`.

## 6. Out of scope (explicitly)

- **`cpp20-stl` profile.** Adds auto-generated `concept` aliases on top of the existing traits classes (`template<typename T> concept OrderedC = is_satisfied_v<Ordered<T>>;`), `requires` clauses on dependent methods (replacing in-body `static_assert`s with structural constraints), `std::optional` chaining utilities, designated initializers in entity construction. Same call-site code, better diagnostics, and lets users write `template<OrderedC T>` in their own generics. Slotted in when a consumer can guarantee C++20.
- **Unreal Engine profile.** UE has its own conventions (`UCLASS`, `UFUNCTION`, `UPROPERTY`, `FString`, `TArray`, `TSharedPtr`). Adding UE means a new profile (`ue5`) with its own type table and macro decoration. Drafted only when UE work begins.
- **Embedded no-STL profile.** Fixed-size arrays, no heap, possibly `etl::*`. New profile, same story.
- **Backward direction (C++ → anthill).** No automated extractor. Hand-author bindings as needed. A libclang-based tool may be considered later if hand-authoring proves to be a real bottleneck.
- **Smart-pointer-heavy ownership models.** Out of scope for this draft. Specs that genuinely need heap-allocated polymorphism will get `std::unique_ptr<Concept>` mappings later, not now.

## 7. Unsupported features in `cpp17-stl` (codegen refuses)

The profile uses **value semantics + RAII only**. There is no host-side hash-cons / term arena, and no heap-allocated closure store. Inputs that would require either are rejected at codegen time with a clear `CppCodegenError` message, rather than emitting code that fails to compile downstream.

### 7.1 Runtime use of `anthill.reflect.*` and `anthill.persistence.*`

Sorts under these namespaces (`TermRepr`, `SortInfo`, `OperationInfo`, `KB`, `Store`, `FileStore`, `SqlStore`, …) model live anthill terms as runtime values. They presuppose a hash-consed term store on the host — exactly the infrastructure `anthill-core`'s `TermStore` provides on the Rust side. The `cpp17-stl` profile ships nothing equivalent.

Codegen refuses any operation signature or type position that resolves to such a sort with:

> `profile cpp17-stl does not support runtime <reflection|persistence> (sort '<qn>') — these require term-store infrastructure not provided in C++; either add an explicit CarrierBinding mapping the sort to a host type, or omit the operation from the C++ surface`

**Workarounds:**
- Add an `Implementation` + `CarrierBinding` fact mapping the sort to a host type the consumer already maintains (the binding is honored before the refusal check).
- Move the operation to a Rust-only or query-time surface and don't expose it via the C++ profile.
- A future `cpp-meta` profile (or `cpp20-stl` with a stub term-store runtime) is the proper home for these features; not in scope for `cpp17-stl`.

### 7.2 Self-referential anonymous lambdas

Anthill expression bodies allow `let f = lambda(?x) -> body`. The current cpp17-stl emission is `[=](auto x) { return body; }` inside an IIFE — a generic by-value lambda. The lambda has **no name in scope for itself**, so a body that calls `f` would compile to invalid C++.

There is no clean RAII-only fix:
- A Y-combinator (`[](auto&& self, auto x){ ... self(self, x-1); }`) bloats every call site and changes the closure's call signature.
- `std::function<R(Args)>` heap-allocates a refcounted control block — that is reference-counting GC for the closure, contradicting the profile's "RAII only" contract.

Codegen detects this case (the lambda body references the let-binder name) and refuses with:

> `recursive anonymous lambda not supported in cpp17-stl profile (binder '<name>' referenced inside its own lambda body) — lift the body to a named operation, which lowers to a regular C++ function and recurses cleanly by name`

**Workaround:** lift the body to a named `operation`. Named operations lower to ordinary C++ functions and recurse by name with no closure machinery — the bytes-on-disk equivalent of a `let rec` group, but without paying for a heap closure or a verbose fixpoint encoding.

### 7.3 What is *not* refused

- **Recursion via named operations** is fully supported — the emitted C++ function is a regular `static` member (or free function) that calls itself by name. RAII-clean.
- **Non-self-referential lambdas** (`let g = lambda(?x) -> add(x, 1); g(n)`) lower normally; the detector keys on the binder name appearing inside the lambda body.
- **Cycles in entity field types** — codegen still emits headers (currently in alphabetical order; explicit forward declarations remain a known gap, see "Known gaps").

## 8. Open questions

- **Marker name (`anthill_satisfied`).** Picked for clarity over brevity; could be a shorter `_a_sat` or an attribute-based marker. Defaults to the verbose form for now.
- **Per-method `static_assert` vs. one wrapping `static_assert` block.** Current choice: emit one `static_assert` per `requires` at the top of each method body, even when the same `requires` repeats across methods of the same sort. Slightly redundant, but makes each method's contract self-documenting and avoids relying on members in the struct body that some compilers handle inconsistently. Could be optimized to a single `static_assert` block in the struct's primary template if redundancy becomes a real concern.
- **`std::expected` vs `tl::expected`.** `std::expected` is C++23. `tl::expected` is a header-only shim that works at C++11. Pick `tl::expected` until C++23 baseline is realistic across consumers (UE5, webots, blefusku).
- **`std::string` vs `std::string_view` for non-owning parameters.** Default to `const std::string&` for now (simpler, owns its buffer). Switch to `std::string_view` once a profile / annotation can request non-owning passing.
- **Header-only vs split header/source.** Templated code is necessarily header-only. Non-templated free functions and entity definitions could go in `.cpp`. Default: emit a single header per anthill namespace; revisit when build-time becomes a concern.
- **Naming of free helper functions for `std::variant` matching.** `std::visit` is verbose; emit per-sort `match` helpers or rely on `std::visit`? Default to `std::visit` for now; helpers are sugar.
