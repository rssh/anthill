# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is Anthill

A kernel language and knowledge base system for formal specification and reasoning. Four core constructs: `namespace`, `sort`, `rule`, `operation`. We can use logical variables in types as in logical terms (types unify — substitution, occurs-check); sort relations are facts. SLD resolution with discrimination tree indexing.

> **Representation note (not "types are terms").** The old "types are terms" mantra was too abstract and invited a false conclusion — that types must be hash-consed `TermId`s. They need not be. Hash-consing is a storage *optimization* (O(1) structural equality, dedup, shared-subterm memory) that pays off for **persistent, heavily-shared structure** — asserted facts, rule heads, nominal sort identities. It is **not implied by type-hood**, and notably **not required by being indexed/searched**: the discrimination tree keys on purely structural `DiscrimKey`s, never on `TermId` identity, so a non-hash-consed carrier (a `Value::Node`/`Entity`, a transient query pattern) indexes and matches identically. It is specifically **inappropriate for binders** (arrow / dependent types), whose scope and alpha-equivalence don't fit a global dedup store. The genuinely load-bearing claim is only that types carry logical variables and unify.

Specification: `docs/kernel-language.md` — canonical language spec (should be kept in sync with implementation).

Design proposals: `docs/proposals/` (numbered 001–024+) — language extensions and design decisions.

## Project Layout

```
rustland/               Rust implementation (primary, most complete)
scaland/                Scala 3 implementation (parallel port, uses fastparse)
tree-sitter-anthill/    Tree-sitter grammar (grammar.js + Rust/Node bindings, used by rustland)
stdlib/anthill/         Standard library .anthill files (prelude, reflect, realization, persistence)
examples/github-todo/   Example project: work-item tracking with domain, rules, tools
anthill-todo/           Work-item .anthill files for this project's own task tracking
docs/                   Kernel language spec, stage0 design docs, proposals
```

## Implementations

### Rust (`rustland/`)

Primary implementation. Cargo workspace with crates: `anthill-core` (parser, KB, resolution, codegen), `anthill-cli`, `anthill-stl`, `anthill-todo`. Uses tree-sitter for parsing.

See `rustland/CLAUDE.md` for Rust-specific build commands, architecture, and conventions.

### Scala (`scaland/`)

Parallel implementation in Scala 3 (sbt build, fastparse). Mirrors the Rust architecture: `term`, `intern`, `parse`, `load`, `kb`, `resolve`, `subst`, `discrim`, `span`.

```bash
cd scaland
sbt test
sbt compile
```

### Tree-sitter Grammar (`tree-sitter-anthill/`)

```bash
cd tree-sitter-anthill
npx tree-sitter generate   # regenerate parser from grammar.js
npx tree-sitter test       # run grammar corpus tests
```

## Example and Skill

- `examples/github-todo/` — complete example: domain entities, work items, rules, tools, feedback. Used by integration tests (`github_todo_test.rs`).
- `/todo` skill (`.claude/skills/todo/SKILL.md`) — manages work items via `anthill-todo` CLI. Build: `cd rustland && cargo build -p anthill-todo`. Run from project root.

## Anthill Language Syntax

```anthill
namespace anthill.example
  import anthill.prelude.{List, Option}
  export MySort

  sort MySort
    entity Variant1(field: Int)
    entity Variant2(name: String, value: Option[T = Int])
  end

  rule derived_fact(?x, ?y)
    :- Variant1(field: ?x), Variant2(name: ?y, value: some(?x))

  fact Variant1(field: 42)

  constraint unique_name
    :- Variant2(name: ?n, value: ?), Variant2(name: ?n, value: ?)
end
```

Variables: `?name` (named, shared within scope), `?` (anonymous, each occurrence distinct).

## Architecture (shared across implementations)

### Pipeline

```
.anthill source → parse (tree-sitter or fastparse) → ParsedFile (typed IR)
  → scan_definitions (4-pass: 1 define all names, 2 requires/imports,
                      3 rule-head Goals, 4 deferred predicate imports)
  → load → KnowledgeBase
```

**Cross-file mutual recursion is supported** (WI-321): pass 1 defines every name
across every file before any pass 2 runs, so two files whose sorts reference each
other both load. This ordering is load-bearing — see the `scan_definitions`
invariant comment and `wi321_cross_file_mutual_recursion_test`.

### Key Concepts

- **Hash-consing (selective, not universal)**: persistent, heavily-shared structure (asserted facts, rule heads, sort identities) is interned in `TermStore` so structurally-identical terms share one `TermId` — but interned terms live for the KB's lifetime, so transient terms (query patterns, occurrence-derived twins) are deliberately NOT interned; they ride as `Value::Node`/`Entity` carriers and match structurally. See the Representation note at the top of this file.
- **Symbol table**: string interning (`Symbol(u32)`), scope-aware two-phase resolution (Unresolved → Resolved)
- **De Bruijn variables**: rules stored with `DeBruijn(u32)`, opened to fresh globals during resolution
- **Discrimination tree**: structural term matching index for fast rule/fact lookup
- **SLD resolution**: depth-first search with negation-as-failure, delay/rotation for unbound vars
- **Facts are rules**: a fact is a rule with empty body; constraints are integrity guards
- **Named args**: canonicalized to a stable order so a record hash-conses and
  discrim-matches regardless of source order — by DECLARED field order when the
  functor has a field schema, else by interning order
  (`canonicalize_record_named_args`, `kb/resolve.rs`). **Not** alphabetical, and
  **not** universal: it returns early for an ORDERED PRODUCT (a named tuple),
  whose component order is part of its TYPE IDENTITY (WI-788) — `(a: Int64, b:
  String)` differs from `(b: String, a: Int64)` (order) and from `(Int64, String)`
  (names). IDENTITY and `<:` ARE DIFFERENT RELATIONS: subtyping is fully
  name-keyed, so BOTH width (dropped from anywhere) and PERMUTATION hold
  (WI-804, WI-803). Do not carry the order rule across from identity into `<:` —
  that mistake refused correct programs. Order still binds where position is what
  is read: an arrow's PARAMETER LIST and UNIFICATION (`TupleAlign`'s three
  disciplines, `kb/typing.rs`). Canonicalizing a tuple's components would change
  its identity, hence the exemption. See `docs/kernel-language.md` §4.5.
- **A tuple's component labels are DISTINCT** (WI-805), refused at each of the THREE
  producers that key a tuple on labels the author WROTE: the literal and the tuple
  TYPE (`check_label_unique`, `parse/convert.rs`), and a `...rest: R` VARIADIC
  CAPTURE's leftover named args (`normalize_variadic_capture`, `kb/typing.rs`) —
  whose labels are written as call arguments and only become a tuple in the typer, so
  the parse guard cannot see them. Same rule the projection `x.(a, a)` and a call's
  named args already had; DERIVED schemas (`Concat`/`Project`) guard themselves.
  Every reader takes a name's FIRST match, so a repeated label leaves a component
  reachable by neither its name nor its position, with its declared type never
  checked — `(a: 1, b: 2, a: 3)` conformed to `(b: Int64, a: Int64)` on a clean load.
  Making the readers AGREE (WI-803) does not fix this: agreeing which component to
  read leaves the unread one unread. "Literal + type" felt exhaustive and was not —
  enumerate `named_tuple_value`'s callers before believing a producer list. NOT
  applied to an arrow's PARAMETER LIST: a repeated binder name there DOES shadow (the
  body reads the LAST one), but params are applied positionally so the shadowed one's
  type is still checked at every call — nothing is silently unchecked.
- **A named-argument list may not REPEAT A LABEL** (WI-809), for ANY callee — operation,
  entity constructor, function value, `fact`, rule-body atom — checked at
  `push_fn_term` + `push_dot_method_call` (two producers; the dot-call one is easy to miss).
  Done as SYNTAX because repetition within one list needs no type info, so one rule
  covers every callee. `mk(a: 1, a: 2)` on `entity mk(a: Int64, b: Int64)` built two
  `a` fields and NO `b`, failing only at run time. Still SEMANTIC in
  `named_arg_coverage_errors`, since neither is decidable from the list alone: an
  UNKNOWN label, and one re-binding a parameter already filled POSITIONALLY
  (`f(3, acc: 10)`). `normalize_variadic_capture`'s duplicate check is kept as the
  backstop for occurrences a MACRO synthesizes without passing through the parser.
- **An entity's field names are DISTINCT too** (WI-808), refused at `convert_entity`
  through the same owner (`check_label_unique`, which takes a per-kind rationale).
  NARROWER HARM than the tuple rule, and the comment says so: an entity's duplicate
  field is still built and read POSITIONALLY (`mk(1, 2)`, `case mk(p, q)`), so its
  type IS checked — what it loses is its ACCESS PATH, since `x.f` / named args / rule
  patterns all take the FIRST match. Refused because a field name is the field's
  public interface. Field names are scoped PER ENTITY — sibling entities in one sort
  may each declare `a`, which is the ordinary variant shape.
- **A distributive projection is known by its MARK, not its shape** (WI-762).
  `convert.rs` desugars `r.(f1, f2)` to `(f1: r.f1, f2: r.f2)` — a term IDENTICAL to
  that tuple written by hand — so it MARKS the result
  (`SimpleTermStore::projections` → `Expr::Constructor::from_projection`, set once in
  `load.rs`) and the typer gates on the mark. Three inferences went with it:
  receiver IDENTITY by SOURCE SPAN, receiver TYPE by stamp, and the LOWERED receiver
  by reading `pos_args[0]` of whatever a sibling field typed into. The last two are
  now ONE producer-written record — the `DotApply` frame stores the receiver's
  lowered twin + type on the receiver occurrence (`set_lowered_receiver`), the only
  place both are in hand. DELIBERATE NARROWING: **only a written `.( )` projects.**
  `r.(f1, f2)` is `Relation[T = (f1, f2)]`; hand-written `(f1: r.f1, f2: r.f2)` is a
  tuple of two independent single-column relations — a projection is an OPERATION on
  a relation, a tuple literal IS a tuple, and per-row computation is `.map` (a
  `Stream`, not a `Relation`). Proposal 052:182 had introduced the shape-based
  reading as the stopgap "until `.( )` lands"; §6.8 is `.( )`. The mark rides as a
  FIELD of `Expr::Constructor` so every rebuild site is a compile error until it
  carries it. NOT because rebuilds drop side slots — `rebuilt_expr` carries both
  `Synthesized` provenance and `inferred_type` — but because `rebuilt_expr` is not
  the only rebuild path: `substitute_occurrence` / `term_view` / `resolve` /
  `body_specialize` call `new_expr` directly, so a beside-slot must be re-carried at
  each by hand, and missing one is SILENT.
- **Destructuring binds by LABEL** (WI-803): the typer records which component
  name each binder takes into `Pattern::Tuple.labels`, and `match_tuple_pattern`
  fetches by name via `TupleComponents::by_label` — the same reader `t.x` uses.
  Reading by SLOT is what made a permuted value bind a component the typer typed
  from a different field (WI-788). A POSITIONAL carrier has no names, so it still
  reads by slot; that is exact, not a fallback, and it is how a spread call
  (`f(3, 10)`) arrives.
- **A requirement DICTIONARY has ONE layout** (WI-857), owned by `dict_layout`
  (`kb/typing.rs`) and stated in `design/operation-call-model.md` §"Dispatch rule": a
  dictionary for spec `S` supplied by provider `P` bundles `S`'s own direct `requires`
  chain, THEN `P`'s. `P == S` is ONE list — which is also the parent-bundle dict
  (`build_concrete_dispatch_dict`), whose functor IS the frame owner. The SPEC half is
  the PREFIX so `requirement_at_sort(chain, k)` — whose `k` indexes the required
  spec's own chain — needs no offset. `expand_dispatching_dict` hands a frame exactly
  the half `impl_parent_of_op(target)` owns, and is LOUD when that is a third sort
  with a chain (`resolve_op_target` can land on an inherited same-short-name default
  or an instance-fact binding elsewhere). This channel is POSITIONAL and its rule was
  NEVER WRITTEN DOWN, so the producer walked `P`'s chain while two consumers indexed
  `S`'s; they agreed only for a chain-free witness provider — every case the suite
  covered — so a carrier-keyed `fact Ordered[T = Int64]` built an arity-0 dict and
  EVERY spec with a non-empty chain died at eval. EVERY producer must build a
  layout-valid dict, including the host-entry STAND-INS (`stand_in_requirement`):
  `cr(functor, [])` reads as "claims `functor`'s whole chain, bundles none". A
  spec-half goal that does not resolve is RECORDED (`Unavailable` → a marker functor),
  not refused and not dropped — refusing it broke 33 tests, because a spec-level
  `requires` is routinely satisfied only via the abstract fallback in
  `check_provider_requires` (`FiniteCollection requires Iterable[C = C]` holds for a
  `List` only through `List provides Stream provides Iterable`). Dispatching through
  the marker is refused at `dispatch_via_sort_ops_table` — one owner — so an unread
  slot costs nothing and a read one names its missing requirement. LOCALITY: inside
  `W`'s dictionary a sub-goal `W` itself provides takes `W`'s own provision first.
- **A sort's `requires` chain is SHARED by every provision it makes** (WI-858), so a
  provider of two floors of one spec tower must take the WEAKEST chain the floors need
  — per-provision conditions (`provides X[…] :- goals`) are 058 §3.8's proposed form,
  not a spelling that exists. `anthill.prelude.Pair` is the shipped case: it provides
  `PartialEq` and `Eq` componentwise, and takes `requires PartialEq[A], PartialEq[B]`.
  NOT `Eq` — MEASURED, an `Eq` chain makes `Pair[A = Float, B = Int64]` a LOAD ERROR
  (`Float` provides `NonEq`, and WI-835's use-site check refuses a `NonEq` carrier at a
  parameter whose sort `requires Eq`), i.e. `Pair` stops being a general PRODUCT.
  `Set`/`Map` genuinely need `Eq` on keys; a pair of anything is a pair. The cost is
  recorded, not hidden: `provides Eq[Pair]` rides the same chain and OVER-CLAIMS.
- **A HOST IMPLEMENTATION IS KEYED PER CARRIER, NEVER ON THE SPEC OP** (WI-876).
  `operation_map { compare: "ordered_compare" }` in a `provides X language rust` block
  is the clause that says which host FUNCTION realizes one of `X`'s operations — the
  operation-level peer of `carrier`, which says which host TYPE realizes a sort. It
  reaches the KB as a flat `anthill.realization.OperationMapping` fact and the runtime's
  builtin registry READS THOSE FACTS (`register_operation_mappings`), instead of the
  hardcoded spec-op names it used. WHY: a binding block had no such clause, so `Int64`'s
  host `compare` had nowhere to be keyed and went on `anthill.prelude.Ordered.compare` —
  where ONE host-scalar implementation was the backing for EVERY carrier that never
  wrote its own. MEASURED: `gt(pair(2, 1), pair(1, 9))` died *"expected Ordered scalars
  of matching type, got Entity and Entity"* on a program that LOADED CLEAN, and the
  carrier's only repair was seven per-carrier members (WI-858 withdrew `Pair`'s ordering
  rather than ship six of them; WI-877 adds it now that ONE suffices). Three parts move
  together and none works alone: the mapping (so the implementation has a per-carrier
  key), the DEFAULT BODIES on `PartialOrd.gt`/`gte`/`lt`/`lte` and `Ordered.max`/`min`
  (unshadowed at last — `ordered.anthill` stated the derivation only as LAWS, and a rule
  is not backing, WI-818), and the carriers DECLARING the ops they map (an operation
  must EXIST for a registration to attach to; body-less, the `LogicalStream.splitFirst`
  shape). "Executable" is now ONE predicate — `op_is_executable` = body │ builtin │ host
  mapping — read by both the load check (`op_backed`) and eval's carrier-override
  resolution (`carrier_override_op`, whose runnable-BODY-only gate made a host-mapped
  member read as ABSENT, so the spec default ran instead of the carrier's own host code:
  `gt(nan, 1.5)` fell into `Ordered.compare`, which `Float` does not provide).
  CONSEQUENCE, deliberate: an `Ordered` op on a carrier that provides no `Ordered` no
  longer resolves — `Ordered.max(1.5, 2.75)` was only ever answered by the spec-op
  builtin ignoring provisions, and with `total_cmp`, under which NaN ranks LARGEST. The
  derivation on `PartialOrd` carries an OP-SCOPED `requires Ordered[T]`: it must live
  with the DECLARATION (`sort_ops` has one slot per carrier+short-name, so declaring
  these on `Ordered` too would let HashMap order pick the winner), and `PartialOrd`
  itself cannot require `Ordered` — `Float` provides one and not the other.
  `PartialEq.eq` was always exempt because its builtin ALREADY dispatched to a carrier's
  own `eq` (`semantic_equal`); that asymmetry between the two builtin families was the
  defect, and the ordering family no longer needs a dispatching builtin to avoid it.
  NOT MIGRATED, and the half-migration must not read as a finished one: the SLD
  registry (`kb.register_standard_builtins`, `BuiltinTag`) ADDED carrier-keyed entries
  BESIDE the spec-op ones and deleted nothing, because a bare `gt(?x, 5)` in any other
  namespace still resolves to `PartialOrd.gt`. So at SLD the defect stands — MEASURED,
  the rule-body goal `PartialOrd.gt("b", "a")` yields NO SOLUTIONS (`builtin_cmp` reads
  NUMERIC operands only and silently `Failure`s on a string pair) while the same
  comparison in eval answers `true`. WI-879, which also notes that "it runs before
  `load_all`" explains why THAT function cannot read the facts, not why the list is
  hand-written: `build_host_op_mappings` is a post-load pass and could derive it.
  Likewise every other spec-op-keyed EVAL registration (`Numeric.add`,
  `String.concat`, `Bool.not`, …) has the same latent hole — WI-880; the ordering
  family went first because it had a demonstrated defect. And the load check's reach
  is still coarser than the mapping: `check_provider_operations` skips a HOST carrier
  wholesale, so `op_backed`'s new host-mapping leg is correct-by-construction but
  UNREACHED today — retiring that skip is WI-880's, now that backing is knowable per
  operation.
- **`[simp]` IS THE ENABLEMENT, NOT THE DIRECTION** (WI-881), and that is what left 24
  of `anthill.prelude.Float`'s 32 declared operations dying `OperationBodyMissing` on a
  program that LOADED CLEAN. An UNTAGGED equational rule is INERT — the normalizer never
  fires it — while a `[simp]` one is EXECUTED by INLINING LHS→RHS in operation bodies
  before dispatch, so a body-less operation whose defining equation carries the marker
  RUNS. `float.anthill` stated four equations under a bare `-- Laws` heading with no
  attribute, where `set`/`map`/`relation` all tag theirs and argue each one. TWO SPELLING
  TRAPS, both MEASURED: a NULLARY head must carry its PARENTHESES (`rule tau <=> …` never
  fires — the bare identifier is not an application, so no redex matches; `rule tau() <=>
  …` does), the left-hand mirror of `map.anthill`'s recorded right-hand hazard (`<=> none
  [simp]` parses as `none[simp]`). INLINING IS NOT DISPATCH, twice over. (i)
  `op_is_executable` (body │ builtin │ host mapping) does not count a `[simp]` equation,
  so one cannot discharge a SPEC operation's obligation (WI-818) — it gives a sort's OWN
  operation a meaning, which is why `Float.recip` is safe and `Float.neg` (a `Numeric`
  op) is host-mapped. (ii) A `[simp]` head is an APPLICATION, so it rewrites `tau()` and
  NOT a BARE `tau` call site (a `var_ref`) — MEASURED, and it is why `tau` ended up
  host-backed after all: with `[simp]` alone `pi` and `e` answered bare while `tau` died,
  and three constants of one family must behave alike.
  THE FOUR LAWS ARE SETTLED ONE BY ONE, and the dividing line for two of them is THE SIGN
  OF ZERO — IEEE distinguishes `+0.0` from `-0.0` while every COMPARISON reads them EQUAL,
  so no ordering- or arithmetic-over-zero law pins the sign bit. `recip(?a) <=> div(1.0,
  ?a)` IS the definition (`f64::recip` IS `1.0/self`) and is now `[simp]` with NO host
  mapping — the only one of the four. `tau() <=> mul(2.0, pi())` is EXACT too (`2·π` only
  increments a binary exponent) but stays a law, for reason (ii).
  `neg(?a) <=> sub(0.0, ?a)` was FALSE (MEASURED: `recip(neg(0.0))` = `-inf`,
  `recip(0.0 - 0.0)` = `+inf`) and is restated over `mul(-1.0, ?a)`. `abs(?a) <=>
  max(?a, neg(?a))` was DOUBLY dead — it named `Ordered.max`, unreachable for a
  `PartialOrd`-only carrier, and `abs` is not definable by comparison AT ALL (it CLEARS
  the sign bit; the ticket's floated `ite(lt(?a, 0.0), neg(?a), ?a)` answers `-0.0`,
  MEASURED) — so it is replaced by the true part, `abs(neg(?a)) <=> abs(?a)`. Everything
  else is one `f64` intrinsic per operation through WI-876's `operation_map`. `Float`
  DECLARES its own `max`/`min` (IEEE `maxNum`/`minNum`, which ABSORB NaN): they live on
  `Ordered`, `Float` provides `PartialOrd`, so there was NO way to take the maximum of
  two floats — and the `gte`-based derivation is not commutative with a NaN operand
  anyway. `floor`/`ceil`/`round` are the only PARTIAL ones (`f64` has NaN, ±inf and a
  range past `i64`), and they RAISE rather than let `as i64` saturate silently; their
  signatures do not say so, which is WI-882's shape. THREE FOLLOW-UPS, each MEASURED
  here: the sibling audit is WI-884 (`Int64.minValue`/`maxValue` and six `String`
  operations dead the same way; `BigInt` clean); the predicate gap `recip` opens is
  WI-885 (`carrier_override_op` reads a `[simp]`-backed member as ABSENT, which is
  WI-876's own defect shape); and the per-carrier host surface is enumerated in three
  disagreeing hand-written tables — cpp-gen SILENTLY emits a call to a C++ function
  that does not exist for an operation it lacks — which is WI-886.


# Repository rules

- before commit, check - if all test passed. Also run the `/code-review` skill (formerly called "simplicity"); remind if it was not run.
- do not add attribution to commit.
- when running rust test, use script which allows monitoring:  rustland/scripts/test.sh 

# Development principles
 - avoid fallbacks, better know about errors early.
 - prefer a loud error over a silent skip: when a case can't be handled — a not-yet-supported / gated path, an unexpected value carrier, a missing field — surface it as an explicit error or diagnostic rather than silently `continue`/dropping it. Silent skips hide bugs and read as "handled" when they aren't.
- **`[simp]` IS THE ENABLEMENT — AND THE CONNECTIVE IS NOT** (WI-884, the sibling audit
  of WI-881). Driving every operation the four primitive sorts DECLARE found EIGHT dead
  the same way — `OperationBodyMissing` on a program that LOADS CLEAN, because a host
  carrier is exempt from the load-time backing check wholesale (WI-880). `Int64`:
  `minValue`/`maxValue`, host-mapped (`i64::MIN`/`MAX`) and NOT stated as equations,
  because a `[simp]` head is an APPLICATION and `in_bounds` writes the BARE `minValue`.
  `String`: `contains`/`indexOf`/`replace`/`trim`/`split` host-mapped, `isEmpty` backed
  by its OWN `[simp]` equation (`eq(length(?s), 0)` IS the definition; its reach was
  MEASURED across the qualified, dot-on-parameter and dot-on-literal call forms, which is
  the test `tau` failed). `BigInt` was clean.
  TWO SEMANTICS DECISIONS, each settled by DRIVING the alternative. **The index unit is
  the UNICODE SCALAR** for `length`/`substring`/`indexOf` alike — the host `str::find`
  answers in BYTES (`"éb".find("b")` = 2 where the character index is 1), so a byte
  answer makes `substring(s, indexOf(s, sub), …)` cut the wrong span; the round trip
  `substring(s, indexOf(s,sub), +length(sub)) = sub` is what pins the three together.
  **The empty pattern occurs at EVERY BOUNDARY**, which three of the sort's own laws
  already said (`contains`/`startsWith`/`endsWith` of `""` are `true`); `split` keeps its
  empty pieces so that rejoining by `sep` reproduces `s` for EVERY input.
  `Bool.ite` IS THE ONE LEFT DEAD (WI-887), on BOTH routes. Its value-level absence is
  deliberate — an operation's arguments are evaluated BEFORE the call, so a registered
  `ite` evaluates both branches — but the runtime's claim that "rule-level uses are
  handled by the prelude's rewrite rules" was FALSE, and tagging the laws is not the fix:
  a `[simp]` head matches STRUCTURALLY, so it reaches `ite(true, …)` and NOT
  `ite(gte(?a,?b), …)`, which is every real use (MEASURED). Half-backed looks backed.
  THE FIRST DIAGNOSIS OF THAT WAS WRONG AND IS WORTH KEEPING: kernel-language.md §5.3
  says an equational rule's head connective is `<=>` and NOT `=` ("`=` … never binds"),
  which reads exactly like the cause. It is not — `is_equational_head` classifies through
  `is_equality_connective_functor`, which matches the `eq` symbol OR the `unify` symbol,
  so BOTH spellings load as equations. Driven across all four (connective × attribute)
  combinations, THE ANSWER TRACKS THE ATTRIBUTE ALONE: `=` + `[simp]` fires, `<=>` bare
  is inert. The spec states a distinction the loader does not make (WI-888); §5.3 now
  says so. Do not diagnose an inert rule from its connective — check the tag.
  `host_fn_by_key` is now an ITERABLE `HOST_FNS` slice, so the arity-column test is
  exhaustive by construction rather than against a second hand-written key list.
  NOT MIGRATED: `String`'s other eight host operations (and `Int64`'s nine) are still
  registered by hardcoded qualified name, so one carrier's surface sits at TWO altitudes
  — `op_is_interpretable` and `kb.host_op_mappings()` see only the mapped half, and only
  it is arity-checked. Carrier-owned, so they answer correctly and WI-880's spec-op-worded
  acceptance does not claim them; recorded as feedback there.
- **WHAT `host_fn` MEANS IS THE HOST'S TO SAY, AND A SECOND LANGUAGE SPLITS TWO
  PREDICATES THAT WERE ONE** (WI-886). cpp-gen enumerated the per-carrier host surface in
  THREE hand-written Rust tables one commit after WI-876 built the declarative channel,
  and they disagreed with the rust runtime AND with each other — `Float.isNaN`/`isInfinite`/
  `isFinite` and every `Int64` operation WI-876/WI-884 declared were absent, while the
  comparisons were still keyed on the SPEC op `PartialOrd.gt` that WI-876 had moved to
  `Float.gt`. MEASURED through `anthill codegen cpp` on a program that codegen'd
  "successfully": `isNaN(a)`, `compare(a, b)`, `max(a, b)`, `gt(a, minValue())` — four
  unresolvable C++ names in a written header, because the fall-through was
  `Ok(format!("{fn_short}(...)"))`. The tables are DELETED; `HostOpTable` reads
  `kb.host_op_mappings()` filtered to `lang == "cpp"`, fed by
  `rustland/anthill-cpp-gen/anthill/{float,int64}.anthill`, which the CLI now loads for
  the cpp targets (`load_kb_for_cpp_codegen`) and cpp-gen's tests walk from disk.
  A cpp `host_fn` is an EXPRESSION TEMPLATE — `$1`, `$2` for the arguments — not a
  function name, and the difference is not cosmetic: for rust the column is a key into a
  CLOSED registry the runtime owns (`HOST_FNS`), because the host code exists and the
  binding only selects it; a code GENERATOR has no registry, it WRITES the host code, so
  what it needs is the SPELLING. A name alone cannot express `neg` (`(-$1)`), `pi`
  (a literal), `floor` (`static_cast<int64_t>(std::floor($1))` — the signature returns
  `Int64` and `<cmath>` returns `double`), or `compare`/`sign`/`mod`, which read an
  argument TWICE and must BIND it in a non-capturing lambda: the arguments arrive as
  already-lowered expressions, which may be calls. The template is PARSED ONCE into
  literal spans and slots and the PARSE is what is stored, so rendering cannot re-read
  the grammar differently; slots must be exactly `$1`..`$n`, EACH ONCE — the review
  caught a first cut that compared SETS, accepting the repeat its own message forbade.
  THE FALL-THROUGH IS NOW A REFUSAL, and BODY-LESS is the line (the same one `op_backed`
  draws): an operation with a body has an anthill definition the backend could emit; one
  without gets its meaning from the host. It is NOT degraded into `synthesise_body_for`'s
  `// TODO:` comment, because that also emits `return {};` — which COMPILES and answers
  zero, strictly LESS loud than the bogus call it replaced.
  THE SECOND PREDICATE: `op_is_interpretable` asked `is_host_mapped_op`, which indexes
  EVERY language, while `register_operation_mappings` registers `lang == "rust"` only —
  so a cpp-only mapping promised eval an implementation it has none of, and
  `carrier_override_op` selected that member over a spec default that would have worked.
  MEASURED (positive control): `OperationBodyMissing { Box.max }` on a program that loads
  clean. `is_interpreter_mapped_op` (rust) now answers eval; `is_host_mapped_op` (any
  language) still answers the LOAD check, which asks about the PROGRAM.
  THREE SMALLER THINGS FOUND BY DRIVING: `Int64.mod` was mapped to `%`, a SILENT WRONG
  ANSWER (anthill's `mod` is always non-negative; C++ `%` follows the dividend — `%` is
  `rem`); `Includes::render` deduped nothing, so three `<cmath>` probes emitted three
  includes; and `provides Float language cpp` must carry NO `carrier` clause, because
  `CarrierTable` is consulted AHEAD of the keyed `TypeMapping` query and would silently
  disable a profile overlay (MEASURED: `keyed_overlay_test` fails with the clause).
  THE SPEC-OP OPERATOR TABLE SURVIVES AND IS NOW A REAL BOUNDARY: one C++ operator serves
  every arithmetic carrier and no carrier declares an `add` to hang a mapping on, so
  `Numeric.add` / `PartialOrd.gt` / `PartialEq.eq` follow WI-880 rather than this ticket.
  Review found the first cut's "spec ops only" claim FALSE — `Bool.and`/`or`/`not` are
  `Bool`'s OWN operations, a gap list wearing a boundary's clothes — so `Bool` got its
  binding block and the claim became true. `ite` is NOT mapped: C++ `?:` is lazy and
  would tempt one, but `ite` is dead on both rust routes (WI-887 owns it) and cpp must
  not be the single host where it works.
  STILL HAND-WRITTEN: `render_as_float_special` is the LAST per-carrier table, and it
  survives because `infinity`/`negativeInfinity`/`nan` are `const`s, which `operation_map`
  refuses BY DESIGN — so a host-supplied CONST has no declarative channel in ANY language
  (WI-889). `String`/`BigInt` have no cpp binding block at all (WI-890), now a loud
  codegen gap rather than a silent one. AND ONE HAZARD THIS TICKET NEWLY EXPOSES:
  `check_provider_operations` builds its host-carrier skip set from `Implementation` facts
  with NO language filter, so attaching a cpp binding block to a carrier disables its
  RUST-side backing check — recorded as feedback on WI-880, which owns that exemption.
