## Attributes

- id: WI-20260911-SXZ3G-defect-the-order-of-a-relation
- created: 2026-09-11T07:30:57Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-18T10:08:44Z

- acceptance: cargo-test, scaland-sbt-test

## Description

DEFECT: the ORDER of a relation's answers is RUN-TO-RUN NONDETERMINISTIC whenever the query carries a variable at an indexed position -- candidate enumeration follows std `HashMap` iteration order inside the discrimination tree, and nothing sorts candidates afterwards. Declaration order is not available to any consumer today, not even to hand-written facts.

MEASURED 2026-09-11 (CLI, current tree). examples/classic-mini/map-colouring: `anthill query -p colouring.anthill --max-results 0 'classic.mapcolouring.Palette.palette(c: ?x)'` over three facts declared red, green, blue -- SIX runs gave FOUR distinct orders (red green blue x2, blue red green x2, green blue red, red blue green). A scratch three-fact table `letter(l: ?x)` declared a, b, c answered a c b in one run and c a b in the next. So the first row of `colouring(?wa, ...)` under `--max-results 1` is not stable across runs, and every `takeN(n)` consumer of a Relation sees a different prefix per process.

CAUSE (read at the site, not yet driven by a fix): `anthill-core/src/kb/discrim.rs` keeps a node's concrete edges as `HashMap<DiscrimKey, Rc<DiscrimNode<L>>>` (:65) and, when the query has a VARIABLE at that position, walks them with `for (_, child) in &node.concrete` (:1163 and :1206). std `HashMap` uses `RandomState`, seeded per map instance from a per-thread random key, so the walk order changes per process (and can differ between two KBs in one process). `KnowledgeBase::rules_by_functor` (kb/mod.rs:6015) IS insertion-ordered, but its own doc says "SLD goal resolution does not consult this; it matches via the discrimination tree". No candidate sort exists in resolve.rs (`grep -n 'candidates.sort\|sort_by_key' kb/resolve.rs` is empty). A BOUND position is unaffected: the lookup is a single `get`, no walk.

WHY IT MATTERS. (1) Any test that asserts a first row or a prefix passes or fails by process seed. (2) `takeN(n)` on a Relation is not a function of the program. (3) Proposal 060 sec 4 (determinism) and WI-743's acceptance ("in DECLARATION order, once per inhabitant") presume an order the resolver does not have: WI-743 cannot deliver declaration order by deriving rows in declaration order, because the index discards it on every variable-position retrieval. (4) A serialized resolution trace (proof records, explain output) is not reproducible.

FIX DIRECTION (verify before building; measure both). Make the variable-position walk deterministic AND declaration-ordered -- stable-but-arbitrary is not enough for (3). Two candidates: (a) at the index: keep `concrete` as an insertion-ordered structure (a `Vec<(DiscrimKey, Rc<DiscrimNode>)>` beside the hash for `get`, or an IndexMap-style map), so every walk is in assertion order and keying is untouched -- CLAUDE.md's representation note says the tree keys on structural `DiscrimKey`s and never on `TermId`; this changes ITERATION only; (b) at the collection point: sort `results` by RuleId (= assertion order) if `L` exposes it. Prefer (a): (b) re-sorts on every retrieval and depends on the leaf type. Census EVERY walk over `concrete` (two sites found by grep; look for clones, `.values()`, `.keys()`, and any other HashMap of children on the query path, e.g. named-arg edges) -- a second walk left in hash order reintroduces the defect one level down.

ACCEPTANCE (cargo-test via scripts/test.sh). A test loads three facts `p(a) p(b) p(c)` in that order and resolves `p(?x)`, asserting the SEQUENCE a, b, c -- on two independently built KBs in one process (two maps, two seeds), and the CLI run above repeated shows one order. CONTROLS, each stated at its site: a query with the position BOUND (`p(b)`) answers identically with the old walk restored -- passes either way BY DESIGN, it never walks; the COUNT of `p(?x)` answers is 3 either way BY DESIGN -- it is the order row alone that fails when the `HashMap` walk is restored, and the test header must say so. Also drive one multi-level case (`q(a, x) q(a, y) q(b, x)` queried `q(?u, ?v)`) so the order holds through nested walks, not only at the first edge. Then re-read WI-743's acceptance: its "declaration order" row depends on this ticket, and the dependency should be wired once this is filed.

## Changes

### 2026-11-18T10:08:38Z — feedback — user

BUILT (claude, 2026-11-18) with WI-20261115-YR3N7, decided with the user ("fold SXZ3G in"): YR3N7 derives a sort's domain a clause per constructor, and an unbound value generated in the index's map order — `green, blue, red` on one run.

FIX (b), at the collection point: `KnowledgeBase::query_view` sorts its candidates by `RuleId` — the order the clauses were asserted in — inside the facts-before-rules grouping it already had, and skips the sort for a single candidate; a derived `fill`'s candidates are in clause order alone (its order is the derivation's, base constructors first). `query_fact_heads` (`read_facts`' indexed path) sorts by `RuleId`. Scaland's `KnowledgeBase.query` the same key. The CENSUS of other walks: `browse_program_clauses_matching` goes through `query_view`; the Γ overlay's candidates (`gamma_candidates_for`) are each the goal itself up to variable identity, so their order is unobservable; the typer env's `query_raw` and `matchTerm`'s one-pattern tree read no order. Option (a), an ordered map in the tree, was not needed: a sort per retrieval already existed, and the key now orders inside it.

SPEC: kernel-language §8.3, "The clauses are tried in CLAUSE ORDER, facts first".

MEASURED: the CLI, six runs of `palette(c: ?x)` over facts declared red, green, blue, and of the derived domain `colours(?x: Colour)`: one order, red green blue, every run (map-colouring no longer has the palette facts; a scratch file).

ROWS: `wi_sxz3g_clause_order_test` (3: facts declared c, a, b over a sort declaring a, b, c answer c, a, b on two KBs; a nested walk `qv` 7, 5, 6, 8 not grouped by the first edge; a bound position, the control); scaland `ClauseOrderTest` (3, the same). BACK-OUT [S] (the key back to facts-first alone): both order rows in each carrier, and about a dozen domain rows (YR3N7's table); the bound-position controls pass. Delivered with YR3N7's gate: 12 272 passed / 0 failed / 17 ignored (36 binaries; the previous 12 261 and the 11 new rows); anthill-core one-shot and two-step 11 195 / 0 / 9 each.

