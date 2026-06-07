# Expansion during unification — implementation design

**Status:** Design (2026-06-03). **Realizes:** [`kernel-language.md`](../kernel-language.md) §8.1 "Expansion during unification". **Prerequisite for:** WI-374 (the typer change), which unblocks WI-368 and *generalizes* WI-357 (element threading) and WI-365 (effect grounding). **Related:** proposal [045](../proposals/045-effect-sets-and-expressions.md) §5.1.1 (the effect-row instance), WI-307 (row-unification — the effect-row close), WI-376 (the projection-types extension — path-dependent `x.A` / `X.L`).

This is an **implementation design** doc, not a proposal. The rule is fixed by kernel-language §8.1; this covers *when* the typer starts expansion, *where* it applies (and where it deliberately does not), and *how* it mints variables. Several points are marked **verify** — open questions to settle against the current typer before coding WI-374.

> **Superseded framing (2026-06-04).** §5's *element threading by within-signature sort-parameter sharing* — "`collect`'s `s` and its return both *are* `Stream.T`" — is **withdrawn**. The element/effect of a value `s` is a **projection off the value** (`s.T` / `s.E` / `s.Sort`, WI-376) or an **operation type parameter** ([042](../proposals/042-explicit-type-parameters-on-operations.md)), **never** a shared `Stream.T`. Threading is always *written*; there is no implicit sort-parameter sharing across a signature. See [`type-parameter-scoping.md`](type-parameter-scoping.md) for the decided rules. Consequently the §2/§6.1/§7 "per-call sort-param scheme substrate" is **not** a separate prerequisite — operation type parameters are already per-call — and WI-374's bare-reference expansion (§4 case 1) is a *convenience*, not the load-bearing thread mechanism.

**Design-dialogue update (2026-06-03).** The earlier *side-channel* framing is **withdrawn**. Guiding principle (§5): type-checking depends on the **type, not on provenance** — neither the enclosing scope's `T` (name-fill) nor a recorded producer (a side-channel "sticker") may steer it, since two values of one type must check alike and `List`/`Stream` are different structures bridged only by a *declared* `fact Stream[T = T]`. Consequences threaded through the rest of this doc:
- the element `T` must be carried **in the type** — via a shared logical variable (`iterator(l: List[T = ?t]) -> Stream[T = ?t]`) or, fluently, an **expression-carried projection** (`iterator(l: List) -> Stream[l.T]`);
- the §1 "expand to fresh vars" rule is **one case of a general elimination at the unify boundary** (§4) that also eliminates the path-dependent projection forms `x.A` (expression-carried) and `X.L` (sort-carried);
- the effect `E` *is* structurally carryable — by **writing the row** (`E = {}`, `E = {Modify[c]}`) once the row model's surface syntax is completed (a surface gap, not fundamental: `{}` is an effect-*row*, the adopted 045 model, **not** the rejected effect-*set*-as-type-argument). When left unwritten it is a residue closed by row-unification against context (WI-307), **never defaulted to pure** (§5);
- **higher-order application** is added as a placement site (§3.5).

The projection forms are a closely-coupled extension (§4); co-deliver with WI-374 or as a tight follow-on. Performance is a separate dimension (§7): two sound caches — load-time signature schemes (which also decides the §2 scoping) and a per-call elaboration record attached to the call's `NodeExpr`.

## 1. The rule

**General principle: the typer introduces a fresh variable for every *ungrounded position* of a type, then lets unification ground it.** A position is ungrounded when the type's *resolved* shape leaves it open — an unwritten parameter of a parametric sort, a slot a defined type's definition did not fill, or a position written as a projection (`x.A` / `X.L`, §4). A position already written as `?` is its own variable; ground positions stay ground.

Kernel-language §8.1 is this principle for **parametric sorts**: a parametric sort referenced as a type with unbound parameters unifies as that sort applied to a **fresh variable per unbound parameter** — `Stream` ≡ `Stream[T = ?, E = ?]`; `Stream[T = Int64]` ≡ `Stream[T = Int64, E = ?]` — covering type parameters *and* effect-row parameters, at **every** sort application. Effect-row params (`effects E`) are ordinary sort parameters carrying the `EffectsRuntime` kind anchor (045 §2), so they expand the same way.

**"Ungrounded" is judged on the *resolved* shape, not the surface reference** (proposal [011](../proposals/011-type-resolution.md): type resolution follows definitions, and a declared `?` is a real parameter slot, not an unfilled hole). A bare reference is all-ungrounded *only* for a primitive parametric sort whose definition fixes nothing (`Stream`). A **defined type / alias with a partially-filled shape** carries what its definition fixed: a bare reference to `sort IntStream = Stream[T = Int64]` resolves to `Stream[T = Int64, E = ?]`, so only `E` is ungrounded → fresh; `T` stays `Int64`. So resolving a defined type to its shape (011) *precedes* counting ungrounded positions; the resolved partial form then routes through §2's `Parameterized (partial)` row.

This makes §8.1's fresh-var expansion one instance of a general **elimination at the unify boundary** (§4): a non-ground type-construction is replaced by fresh variables plus constraints before unification proceeds — a bare/partial/defined parametric sort here (fresh per ungrounded parameter), the projections `x.A` / `X.L` in the closely-coupled extension (fresh var + constraint). "A fresh variable for every ungrounded position" is the single statement that covers them all.

## 2. WHEN — the trigger, and what must be clarified

Elimination fires when the unifier meets a type-construction that is **not already a variable**. Recognizing the form means dispatching on the `Type` head (`type_head`, typing.rs:10280); the head determines the action:

| `type_head` form | action |
|---|---|
| `SortRef(S)`, `S` parametric | **expand** — to `S[every param = fresh]` (§4 case 1) |
| `Parameterized { base: S }` | **expand (partial)** — only the params *not* already in its bindings |
| `ExprCarried` (`x.A`, path-dependent) | **eliminate** — fresh `Ti`, constrain `unify(Ti, typeof(x).A)` (§4 case 2; projection extension) |
| `SortCarried` (`X.L`) | **eliminate** — fresh `Ti`, alias `X.L`, add requirement `X[L = Ti]` (§4 case 3; projection extension) |
| `SortRef(S)`, `S` non-parametric (`Int64`, `Bool`) | none — nothing to expand |
| `TypeVar` (`?T`) | none — already a variable |
| `Denoted(value)` (`Modify[store]`) | none — a value *index* that **stays** (distinct from `ExprCarried`, which projects a type *member* and is eliminated) |
| `Arrow` / `NamedTuple` / `EffectsRows` / `Nothing` | none at the head; recurse structurally into children |

The `ExprCarried` / `SortCarried` rows are the closely-coupled projection extension (§4); WI-374's own scope is the `SortRef` / `Parameterized` expand rows.

A `SortRef(S)` whose `S` is a **defined type / alias** is first *resolved to its shape* (§1, 011) before counting unbound params: a partially-filled definition (`IntStream = Stream[T = Int64]`) arrives in parameterized form and routes through the `Parameterized (partial)` row (only `E` fresh) — *not* the all-fresh `SortRef` row, which only a primitive parametric sort hits.

The trigger needs two inputs the loader already provides:
- **The sort's declared parameter list**, effect-row params included (`sort T = ?` / `effects E = ?` registrations).
- **A fresh-var source** scoped to the current unification context.

**The scoping clarification — the crux (verify first).** The fresh vars must be **per sort application**, not one global var per `(sort, param)`. Two independent `Stream` uses in one check — say a `Stream[Int64]` argument and an unrelated `Stream[String]` local — must not alias their `T`/`E`. Today `unify_parameterized_with_sort_ref` (typing.rs:7965) binds the sort's **loader-cached canonical** param Vars ("shared across B's signature"); that is sound *only* if those canonical Vars are opened fresh per call/check (as De-Bruijn rule vars are via `with_fresh_vars`). Before coding, **verify** one of:
- (a) operation signatures are opened per-call, so the canonical Var is already effectively fresh per application; or
- (b) expansion must mint fresh vars and alias the canonical Var to them.

If neither holds, bare-vs-bare expansion would cross-contaminate independent uses — the failure mode to guard against.

## 3. WHERE — the sites

### 3.1 Operation signatures — the primary site (typer, §8.1)

Parameter types, the return type, and the `effects` row of an operation are type expressions that may be bare parametric sorts. Two moments:
- **At a call** (`check_apply_iter`): each param type is unified against the argument's inferred type, and the return type is resolved. A bare `s: Stream` param must expand so the argument's bindings thread (`T`, `E`) — this is exactly the `collect(iterator(xs))` case where today both sides are bare `sort_ref` and nothing binds.
- **At body-check** (`check_operation_bodies`): params are bound into the env with their declared types; a `s: Stream` bound un-expanded leaves the body's uses of `s` carrying no `T`/`E`.

### 3.2 Type annotations — same unify path

`let s : Stream = e` and a param `x: Stream` are annotations: the annotation is unified against the inferred/argument type. They ride the same `unify_types` `sort_ref` arm, so no separate site — fixing §3.1's unifier covers them. (Note the let-binding interaction: an *un*-annotated `let s = e` simply propagates `e`'s already-expanded type, per the §5.1.1 worked example.)

### 3.3 Rule bodies — split: runtime goals are term-level, but typed / simp-rewritten bodies **are** a site

Two distinct things travel under "rule body," and only the first is outside §8.1:

- **Runtime SLD resolution of logical goals** — *not* a typer site. A parametric sort appearing as a *goal term* (`fact Stream[T = ?x]`, a `:- Stream[…]` goal) is matched by first-order unification in the resolver, where the term-level analog — partial entity patterns (§8.3) — already generalizes missing args to fresh vars. The typer is not involved on this path.

- **Typer processing of rule bodies — a §8.1 expansion site.** The typer *does* touch rule bodies, two ways, both reaching `unify_types`:
  - **`[simp]` rules fire during typing** (proposal 043). The typing pass walks occurrences with `SIMP_FUEL` and calls `fire_simp` → `simp_rewrite::try_fire` (typing.rs:2196/2252); a call matching a `[simp]` equation is rewritten to that equation's RHS — opened (`open_equation`, :1609) and instantiated as an occurrence (`substitute_to_occurrence`, :1612) — and the RHS is then typed. So a body call `r(a, b)` with `rule r(a, b) = f(a) + g(b) [simp]` becomes `f(a) + g(b)` during typing, and `f` / `g` / `+`'s bare parametric sorts expand exactly as at any call (§3.1).
  - **`check_rule_typing`** collects type constraints from the body goals via the occurrences (`collect_occurrence_type_constraints`, typing.rs:11497) through `unify_types` — so a bare parametric sort there goes through §8.1 expansion too.

So §8.1 expansion is **not** confined to operation signatures: it fires wherever the typer reaches `unify_types`, including simp-rewritten rule bodies and rule-typing constraint collection. "Bare parametric reference = all-params-fresh" must hold uniformly across the typer, and must agree with the resolver's term-level §8.3 analog on the runtime path. Note the opener a simp RHS uses (`open_equation` mints fresh vars per firing) is the **same** De-Bruijn/scheme pattern as §7 Layer 1 — a `[simp]` rule's vars are opened fresh per firing, exactly as a signature's are per call.

### 3.4 requires / provides — mixed, and the subtle one (verify)

`requires Spec[…]` and `fact Spec[…]` (provides) reference parametric sorts. Their **matching** runs through the `refines()` / `provides()` rules in `stdlib/anthill/reflect/typing.anthill` (resolver, term-level), so a bare `requires Stream` ≡ `requires Stream[T = ?, E = ?]` is already handled by §8.3 partial-entity-patterns at the resolver. **But** the **typer-side** provider-admissibility reads (`provider_spec_view_bindings`, `spec_resolves_at_bindings` — WI-356) read a spec term's bindings as types; where those reach `unify_types`, they go through §8.1 expansion. **Verify** the two agree on "bare = all-params-fresh" so a bare `requires`/`provides` is not accidentally treated as a *closed* (zero-param) sort on one side and an open one on the other. Keep requires/provides *matching* at the resolver; ensure any typer-side spec-term unification uses the §8.1 expansion uniformly.

### 3.5 Higher-order application — a forward site (verify under WI-289)

Applying a value of arrow type (`Function[A, B]`, `f(f(x))`) is a distinct path from the named-operation `check_apply_iter`: its param/return come from the **arrow type**, not `lookup_operation_info_full`. The elimination mechanism rides it for free — arrow `param`/`result` are themselves type expressions, and `unify_arrow_view` (typing.rs:7543) already recurses them through the generic `unify_types`, so the §4 boundary fires inside `Function[A = Stream, …]` with no separate site. (An expression-carried projection `x.A` needs `x` in scope at the type position; a function value's *result* is not a named binding, so a higher-order result that must expose an element has to declare it in the arrow type — `Function[A, B = List[?t]]` — not project it post-hoc. No provenance is involved either way.) **But** the typer does not yet check higher-order calls of `Function[A,B]`-typed values at all (typing.rs:10571, gated under WI-289). So this is forward-looking: when WI-289 lands, **verify** its arrow-apply path routes through `unify_types`, not a bespoke unifier that bypasses the §4 boundary.

### 3.6 Higher-kinded parameters (Functor / Monad)

A sort parameter may itself be parametric — `sort F { sort T = ? }` inside `sort Functor` — a **higher-kinded** carrier instantiated at different element slots in one signature: `map(fa: F[T = A], f: (A) -> B) -> F[T = B]` (same `F`, `T` varying). It parses cleanly (verified). Three observations:

- **"Ungrounded → fresh" extends, with the carrier var *shared*.** Expanding the scheme (§7 Layer 1) freshens `F`, `A`, `B` → `F̂`, `Â`, `B̂`, and `F̂` is the *same* var at `F̂[T=Â]` and `F̂[T=B̂]` — that sharing is what "same functor, different element" means. The only novelty is that `F̂` is higher-kinded (ranges over type constructors).
- **Grounding `F̂` is provider dispatch, not higher-order unification — the *same* carrier-resolution as §5.** At `map(xs, g)` with `xs : List[Int64]`, the receiver's carrier (`List`) selects `fact Functor[F = List]`, binding `F̂ := List`; then `F̂[T=Â]` is `List[T=Â]`, unified first-order against `List[Int64]` (`Â := Int64`), and the return is `List[T=B̂]`. So the higher-kinded case **reduces to first-order once the carrier is dispatched**, with the identical concrete/abstract split (concrete `List` grounds `F̂`; an abstract `C provides Functor` keeps `F̂ := C` polymorphic). Notably, **Functor has no Stream-style erasure problem**: its carrier `F` is *explicit in the type* and threaded through the signature (`F[T=A] -> F[T=B]`), exactly the "carry it in the type" discipline §5 argued for — nothing is erased, no provenance needed. Functor is the *well-behaved* shape; Stream's trouble was that its carrier was implicit.
- **The genuinely higher-order residue is bounded.** Only an *unbound* variable functor head (`?F̂[…] =?= List[…]` with no dispatch info) is higher-order; it is restricted to the decidable **pattern fragment** (`check_ho_apply_pattern`, §3.5 — "ensures higher-order unification remains decidable"). The arg `T = Â` is a distinct fresh var → in-pattern → decidable; outside the fragment → a loud error, not a silent skip.

The Functor identity law `rule identity: map(?fa, ?x => ?x) = ?fa` sits at the intersection of §3.3 (a rule body typed during typing — the `map(…)` call instantiates this higher-kinded signature) and §3.5 (the `?x => ?x` lambda).

## 4. HOW — the mechanism

The unifier does not act on a non-variable type-construction directly: at the unify boundary it **eliminates** the construction into *fresh variables + constraints*, then unifies the results. One boundary, three cases — **WI-374 ships case 1; cases 2–3 are the projection extension (WI-376)** that plugs into the same hook.

**Case 1 — bare / partial sort application (the §1 rule; WI-374 core).** A bare `sort_ref(S)` behaves as `S[all-params = fresh]`; a partial `S[T = Int64]` fills the rest with fresh. Then `(sort_ref, sort_ref)` with equal base unifies the two expansions param-by-param (fresh ↔ fresh, or fresh ↔ value when one side narrows later). Equivalently: expand each operand to its parameterized form at entry to the `sort_ref` arms, then defer to the existing `(parameterized, parameterized)` / `unify_parameterized` path. Today only the half-rule exists:
- `(parameterized, sort_ref)` → `unify_parameterized_with_sort_ref` (7965): binds the bare side's canonical param Vars from the parameterized side's bindings — one side already carries bindings.
- `(sort_ref, sort_ref)` equal base → **the missing case.** Both bare ⇒ no bindings to copy ⇒ nothing threads. This is the WI-368 leak.

**Case 2 — expression-carried projection `x.A` (path-dependent; projection extension).** Mint fresh `Ti`, emit the constraint `unify(Ti, typeof(x).A)` — resolve `x`'s static type, project member `A`, unify with `Ti` — and proceed with `Ti`. Example: `Stream[l.T]` with `l : List[Int64]` ⇒ `Ti`, `unify(Ti, List[Int64].T = Int64)` ⇒ `Stream[T = Int64]`. **Well-formedness:** `typeof(x)` must declare member `A`, else a type error — *not* a silent fresh var. This lets a producer write `Stream[l.T]` instead of threading a shared `?t`, and it is the type-member sibling of the existing `Denoted` value-in-type form (which *stays* rather than eliminates).

**Case 3 — sort-carried projection `X.L` (projection extension).** Mint fresh `Ti`, alias/replace `X.L` with `Ti` (trivial case: both unbound `?`), **and** add `X[L = Ti]` to the enclosing requirements, then expand `X[L = Ti]` further by these same rules. This is the abstract-type-member → fresh-var + bound encoding (F-ω / Scala's `X#L`). **Termination:** the recursion bottoms out on finite type structure.

**Placement.** A projection enters as a **dotted `name`** in type position (verified — same CST shape as a qualified ref; §6.4): the **loader/converter** classifies it via SymbolKind (the WI-302 `denoted`-vs-`sort_ref` path) into the projection Type node. `type_head` / `extract_type` (typing.rs:10280/10342) then grow the two projection heads (recognition only). The *elimination* runs at the `sort_ref` (and projection) arms of `unify_types` (~7400+), which hold the `&mut subst` needed to mint fresh vars and add constraints — `extract_type` is a pure classifier, so minting cannot live there. Reuse: `type_params_of_sort`, the canonical-param-Var lookup `unify_parameterized_with_sort_ref` already uses, `extract_type`/`type_head`.

## 5. Threading `T`, and the effect-row residue

**Principle: a consumer may rely only on what the *type* carries — not on provenance.** Two values of type `Stream` must type-check identically; neither the enclosing scope's `T` (name-fill) nor a recorded producer (a side-channel "sticker") may steer the result. Both smuggle in *where the value came from*, which the type `Stream` does not carry — and `List` and `Stream` are different structures, bridged only by the *declared* `fact Stream[T = T]`, whose use requires a carrier the bare type erased. So whatever a consumer needs must be **in the type**.

**Element `T` — carried structurally, threads by unification.** The producer states the relationship in its signature: a shared logical variable (`iterator(l: List[T = ?t]) -> Stream[T = ?t]`) or, fluently, an expression-carried projection (`iterator(l: List) -> Stream[l.T]`, §4 case 2). Then `iterator(xs : List[Int64])` has type `Stream[T = Int64]` — element *in the type* — and case-1 expansion threads it through `unify_types` with no provenance, including through composition (`collect(s: Stream) -> List[s.T]` on `Stream[Int64]` ⇒ `List[Int64]`). One signature even covers the concrete/abstract split: `iterator(c) -> Stream[c.T]` gives `Stream[Int64]` for a concrete `c : List[Int64]`, and stays polymorphic for an abstract `c : C` (the projection resolves against `c`'s declared interface member). The bare `iterator(l: List) -> Stream` (list.anthill:67) that *deletes* the relationship is the actual gap — no consumer-side mechanism can soundly reconstruct it.

**Effect `E` — the genuine residue (and it is the *observation* effect).** `effects E = ?` is the "effect row required to **observe**" the stream (stream.anthill:19) — `splitFirst`'s effect (`splitFirst(s: Stream) … effects E`, :21–22), incurred at **consumption**, not at construction. So `E` is **not** the producing op's effect: `List.iterator(l) = l` is pure (`{}`), but `E = {}` comes from **`List.splitFirst` being pure**, not from `iterator` being pure — they coincide for `List` only by that coincidence. The canonical lazy stream (pure `iterator`, *effectful* `splitFirst` — file/network-backed) has them differ, so binding `E` from the producer's effect would silently claim such a stream pure (the unsound effectful-carrier case).

`E` *can* be carried structurally — by **writing the row**: `iterator(l: List) -> Stream[T = l.T, E = {}]` for a pure carrier, `Stream[E = {Modify[c]}]` for an effectful one. That this doesn't parse today is a **surface gap, not a fundamental one**: `{}` is an effect-**row** (the adopted 045 model), *not* the effect-*set*-as-type-argument (`entity effect_set(effects: List[Type])`) that WI-301 proposed and 045/WI-320 superseded. The `Type::effects_rows(EffectExpression)` variant already exists (WI-320); WI-320 only *routed around* the surface gap — its EffectsRuntime bridge rule lives in Rust because `effects_rows(…)` can't yet be written in type-arg position ("parse error tested"), which is a workaround, not a prohibition. Admitting it — an empty-row form, effect-rows in the `SortBinding` value slot, and disambiguation from `set_literal` by the param's kind (§6.5) — completes the row model's surface syntax and lets a producer state `E` exactly like `T`. Then the effectful-carrier case is sound (the effect is in the type, so a pure consumer is correctly rejected), and `E` is a residue *only when left unwritten*.

When `E` is left unwritten (a bare return), it stays a free effect-row var, **constrained by the consumer's context**: `collect`'s `effects E` must fit the enclosing op, so in a pure op `length(collect(List.iterator(xs)))` it closes to `{}` (row-unification, WI-307; `make_effect_expression_empty_row`, mod.rs:3090). **`E` must never be *defaulted* to pure as a rule** — that close is sound *today* only because every carrier's `splitFirst` is pure; an effectful-`splitFirst` carrier with `E` unwritten would be wrongly closed, which is exactly why the *written* form above is the principled fix. (Note `List` has no effect *member* to **project**, so `l.E`-style projection can't carry `E` the way `l.T` carries the element — the written row is the route, not a projection.)

So WI-374's core (case-1 expansion) threads the structural relationships; the projection forms (§4 cases 2–3) make `T` fluent; `E` becomes structural too once the row model's surface syntax is completed (written `E = {…}`, §6.5), and is a context-closed residue only when left unwritten.

## 6. Open questions to settle before coding WI-374

1. **Fresh-var scoping** (§2) — per-application freshness vs the loader-cached canonical Var. **Decided** by §7 Layer 1 (store signatures as De-Bruijn schemes, open fresh per call); what remains is the *implementation* verify that the chosen opening is wired (and that ad-hoc, non-signature type expressions expanded lazily at `unify_types` also mint fresh). Independent of the projection extension.
2. **requires/provides typer-vs-resolver split** (§3.4) — confirm both treat "bare = all-params-fresh".
3. **Effect-row close** (§5) — is the open↔`{}` row-unification at the effect check present, or in WI-374's scope (and how does it relate to WI-307)? The *policy* is settled (close by the consumer's context; never default-to-pure; thread the carrier's `splitFirst` effect once effectful carriers exist); this is about the row primitive that performs it.
4. **Projection forms — scope split** (§4 cases 2–3). **Grammar: VERIFIED** (tree-sitter 0.25.10) — `x.A` / `X.L` parse in type position as a `simple_type` whose `name` has multiple `identifier` segments, the *same CST shape* as a qualified sort ref (`scala.prelude.List`); `Stream[l.T]` (positional) and `Stream[T = l.T]` (named) parse too. **No grammar change.** So the cost is purely semantic: the **loader** classifies the dotted `name` via SymbolKind — head segment a value/param → `ExprCarried`; sort + member → `SortCarried`; namespace path → `sort_ref` — which *is* the existing WI-302 `denoted`-vs-`sort_ref` classifier; WI-376 adds the `ExprCarried`/`SortCarried` *elimination* outcomes. **Caveat:** a projection is not lexically distinct from a qualified name, so a param shadowing a namespace segment is a classification ambiguity (pre-existing, shared with WI-302's `denoted`). Decide co-delivery: the expression-carried form (`x.A`) is the half that pays for WI-374 (it makes `Stream[l.T]` work and resolves the concrete/abstract split); the sort-carried form (`X.L`) drags in the `requires` plumbing and is the natural follow-on seam.
5. **Effect-row surface syntax** (§5) — **grammar LANDED** (this session): a braced effect-row is now admitted in the `SortBinding` value slot (`E = {}` / `E = {Modify[c]}`) via `seq('{', commaSep($._effect_type), '}')` in `_common_type_expr` — conflict-free (`tree-sitter generate` clean; corpus 146/146), the empty `{}` included. It completes the adopted 045 row model's surface syntax (an effect-**row**, *not* the rejected effect-*set*-as-type-argument; WI-320 only routed around the gap in Rust). The **loader/typer follow-on is WI-375**: lower the new CST node to `effects_rows`, disambiguate row-vs-`set_literal` by the param's kind, and bind the written closed row (row-unification, WI-307) so a producer states `E` structurally like `T` (sound for effectful carriers).
6. **Defined-type resolution** (§1) — verify the typer resolves a defined type / alias (`IntStream = Stream[T = Int64]`) to its underlying shape *before* expansion, so a bare alias reference expands only the parameters left as a declared `?` (here `E`), not all of them. 011 is still *Brainstorming*; if the namespace-level alias-resolution path is incomplete, a bare alias reference would wrongly go all-fresh.
7. **Higher-kinded parameters** (§3.6) — verify the typer (a) instantiates a higher-kinded carrier param `F` by provider dispatch so `F[T=A]` reduces to a concrete `List[T=A]` (first-order), and (b) bounds an unbound variable-functor-head unification to the decidable pattern fragment (`check_ho_apply_pattern`), erroring loudly outside it rather than looping or mis-unifying.

## 7. Caching: the two layers

Caching is sound only where it is **substitution-independent**. Two layers sit at different levels; together they mean no phase re-unifies.

**Layer 1 — expansion as normalization (load-time signature schemes).** At load, normalize each operation signature *once*: resolve defined-type/alias references to their underlying shape (§1, 011), expand bare/partial sorts to their parameterized form (§4 case 1), and resolve the projection structure (§4 cases 2–3) — `Stream[l.T]` resolves `Stream.T` to the `T` member of param `l`; a sort-carried `X.L` becomes a scheme var plus its generated `X[L = Ti]` requirement. Store the result as a **De-Bruijn-style scheme** (param vars bound), exactly as the resolver stores rules; per call, *instantiate* (open fresh vars — the `with_fresh_vars` analog) and unify the arguments.
- Does the expansion / projection-resolution work **once per signature**, not once per call.
- **It is the §2 fresh-var-scoping resolution:** instantiation opens fresh, so two independent `Stream` uses in one check cannot alias their `T`/`E`. §2's "verify (a)/(b)" becomes the *decision* "store schemes, open per call."
- Reuse: the resolver's De-Bruijn rule machinery (`with_fresh_vars`); `type_params_of_sort`. The same open-per-use shape already serves `[simp]` rules during typing (`open_equation`, §3.3), so signatures, rules, and simp equations share one scheme/opening discipline.

**Layer 2 — per-call elaboration on the occurrence.** A call's instantiated σ is scratch — **processed once on the call side** (`check_apply_iter`); its *walked* results attach to the `NodeExpr` (`NodeKind::Expr`) as the authoritative record eval reads:
- resolved type-args (`resolved_type_args`, WI-272 → callee `Frame.type_args`), including resolved projections;
- the requirements to pass — **including those *generated* by a sort-carried `X.L`**, which emits a `DeferToRequirement`-style entry that rides `req_insertion::run` (WI-232/239), the *same* channel the existing requirement insertion uses. **This is the WI-376 ↔ `insert_req` seam:** a projection-generated requirement needs no new attachment mechanism.
- the resolved return type (`inferred_type`) and the effect row.

σ is then discarded; only the walked results survive (a half-resolved σ is subst-dependent — do not store it).

**The boundary.** Layer 1 is fully subst-independent (the scheme mentions only the op's own bound vars). Layer 2 stores *walked* per-call results (subst-independent once resolved). The unsound option — a global `unify(A, B)` / call-result memo keyed on type-tuples — stays ruled out: results depend on the live substitution and on fresh-var generativity (two calls with "the same" argument types must still get *distinct* vars).

**Net flow.** Body type-checked once → its signature normalized once into a scheme (Layer 1) → each call instantiates + unifies *its* arguments once, producing the node elaboration (Layer 2) → eval reads the node. No phase re-unifies; the only per-call cost is the single unification of this call's arguments — irreducible.

## 8. Build sequence (reframed 2026-06-04)

After the 2026-06-04 dialogue (§5 superseded — see [`type-parameter-scoping.md`](type-parameter-scoping.md)), the load-bearing mechanism is **not** this doc's bare-vs-bare expansion (§4 case 1) but **bidirectional inference**: threading is *written* (operation type parameters [042] or projection), and the expansion is a convenience. So the dependency graph re-roots — everything that read "depends on WI-374" really depends on **WI-379**.

**Delivered foundation:** WI-307 (effect-row unification), WI-375 (written effect rows, `Stream[E = {}]`), WI-357 (element threading, concrete path), WI-365 (abstract self-typing).

| # | WI | role | depends on |
|---|----|------|-----------|
| 1 | **WI-379** | **Foundation** — bidirectional inference (arguments-before-expected + cross-sort binding); sound `[T]` inference. Subsumes WI-367. | — (reorder + generalize existing helpers in `check_apply_iter`) |
| 2 | **WI-380** | **Stdlib rewrite** — iterator / collect / splitFirst → explicit `[Elem, Eff]` (042) + written `E` (WI-375). The concrete consumer of WI-379; closes the `?_` leak **and** threads the element. **Achieves WI-368's acceptance.** | **WI-379** (+ WI-375 ✓) |
| 3 | **WI-368** | the *effect-grounding* statement of that same acceptance (`length(collect(List.iterator(xs)))` pure) — achieved by WI-379 + WI-380. | WI-379 (field says WI-374) |
| 4 | **WI-376** | projection `s.T` / `s.Sort` (fluent alternative to `[Elem, Eff]`) and `X.L` (sort-carried → `[Ti]` + `requires`, desugars into 042). | WI-379 + 042 (field says WI-374) |
| 5 | **WI-374** | **convenience** — bare-ref expansion `S ≡ S[fresh per param]` (§4 case 1); robustness for unannotated refs, threads nothing on its own (the type-not-provenance Boundary). | — (independent) |
| 6 | **WI-381** | resolve a defined-type / alias to its shape *before* expansion / projection (§6 OQ6 verify) — prerequisite for WI-374 / WI-376 over aliases. | — (relates 011) |
| 7 | **WI-382** / [`future/unification-framework`](../proposals/future/unification-framework.md) | **destination** — per-sort unification framework (CLP); the substrate WI-010 wants. | WI-010 |

**Dependency corrections** (the todo CLI has no dep-edit; authoritative here + in WI feedback): **WI-376 and WI-368 re-root from WI-374 to WI-379.** WI-374 is a convenience and threads nothing, so nothing load-bearing may depend on it.

**§6 open-question disposition.** OQ1 (fresh-var scoping) → moot under no-implicit-sharing; OQ2 (requires/provides bare = all-fresh) → WI-356 (delivered); OQ3 (effect-row close) → WI-375 (written, delivered) + WI-368 (context-close); OQ4 (projection scope) → WI-376; OQ5 (effect-row surface) → WI-375 (delivered); OQ6 (defined-type/alias resolution before expansion) → still **verify** (011), folds into WI-379 / WI-376 alias-resolution.

**Minimal path to the acceptance** (`length(collect(List.iterator(xs)))` pure + element threaded): **WI-379 → WI-380** (WI-380's stdlib rewrite discharges WI-368's acceptance). WI-376 (projection), WI-374 (expansion), and WI-381 (alias resolution) are fluency / robustness / correctness-edge on top, not on the critical path; WI-382 is the long-horizon destination.

### Variance (WI-293, proposal 035) — a parallel soundness track, off the critical path

Per-parameter variance (the typer consuming declared `Covariant` / `Contravariant`
facts, the default flipping covariant→invariant) is **orthogonal** to threading and
does **not reorder** the sequence — the minimal path
(`length(collect(List.iterator(xs)))`) is all-equality (every param pinned by
unification), so no subtyping is exercised. Three points of contact, none a reorder:

- **Seam at WI-379, not a new step.** Variance lives in the *check* primitive
  (`types_compatible` / `parameterized_compatible`) that WI-379's bidirectional step
  already calls — so WI-293 *plugs in*, it doesn't sequence. The one constraint it
  places on WI-379 is the invariant above (*one relation, several implementations
  that must agree*): route arg-vs-param **and** result-vs-expected through the shared
  primitive, so WI-293 attaches without WI-379 hand-rolling a bypassing equality.
- **Synergy — args-before-expected is what keeps variance sound during inference.**
  WI-379 pins the operation type parameters from the *arguments* by **equality**
  (unification); variance is *subtyping*, a directional relation on **ground** types.
  Because the args pin the metavariables first, variance-aware subtyping only ever
  applies to the final ground checks (result vs expected, arg vs param) — never to
  solving a metavariable through a `<:` constraint (the classic hard case of local
  type inference). Expected-first seeding would push a metavariable onto a subtype
  constraint; args-first sidesteps it. So WI-293 lands **after WI-379** and is
  independent of WI-380 / 368 / 376 / 374 / 381.
- **It enriches the WI-382 destination.** Variance is the *order* relation
  (subtyping / join / meet) — the sibling of *unification* (equality) — and 035 already
  expresses it as SLD rules over `Covariant` / `Contravariant` facts. So the per-sort
  framework spans per-sort **ordering**, not only per-sort unification: a second
  citizen of resolver-as-typechecker, alongside the effect-row case.

The default-flip (covariant→invariant) touches the *same* shared primitive that WI-356
provider-admissibility and WI-379 both use, so migrate it carefully (035 *Risk: existing
tests*). (The other half of WI-293 — variance-aware `join_types` for parameterized lubs,
`join(Option[Cat], Option[Dog]) = Option[Animal]` — is branch-lub machinery, independent
of this whole sequence.)
