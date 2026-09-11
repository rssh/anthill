## Attributes

- id: WI-20260911-SXZ3G-defect-the-order-of-a-relation
- created: 2026-09-11T07:30:57Z

- status: Open
- status_agent: claude
- status_at: 2026-09-11T07:30:57Z

- acceptance: cargo-test, scaland-sbt-test

## Description

DEFECT: the ORDER of a relation's answers is RUN-TO-RUN NONDETERMINISTIC whenever the query carries a variable at an indexed position -- candidate enumeration follows std `HashMap` iteration order inside the discrimination tree, and nothing sorts candidates afterwards. Declaration order is not available to any consumer today, not even to hand-written facts.

MEASURED 2026-09-11 (CLI, current tree). examples/classic-mini/map-colouring: `anthill query -p colouring.anthill --max-results 0 'classic.mapcolouring.Palette.palette(c: ?x)'` over three facts declared red, green, blue -- SIX runs gave FOUR distinct orders (red green blue x2, blue red green x2, green blue red, red blue green). A scratch three-fact table `letter(l: ?x)` declared a, b, c answered a c b in one run and c a b in the next. So the first row of `colouring(?wa, ...)` under `--max-results 1` is not stable across runs, and every `takeN(n)` consumer of a Relation sees a different prefix per process.

CAUSE (read at the site, not yet driven by a fix): `anthill-core/src/kb/discrim.rs` keeps a node's concrete edges as `HashMap<DiscrimKey, Rc<DiscrimNode<L>>>` (:65) and, when the query has a VARIABLE at that position, walks them with `for (_, child) in &node.concrete` (:1163 and :1206). std `HashMap` uses `RandomState`, seeded per map instance from a per-thread random key, so the walk order changes per process (and can differ between two KBs in one process). `KnowledgeBase::rules_by_functor` (kb/mod.rs:6015) IS insertion-ordered, but its own doc says "SLD goal resolution does not consult this; it matches via the discrimination tree". No candidate sort exists in resolve.rs (`grep -n 'candidates.sort\|sort_by_key' kb/resolve.rs` is empty). A BOUND position is unaffected: the lookup is a single `get`, no walk.

WHY IT MATTERS. (1) Any test that asserts a first row or a prefix passes or fails by process seed. (2) `takeN(n)` on a Relation is not a function of the program. (3) Proposal 060 sec 4 (determinism) and WI-743's acceptance ("in DECLARATION order, once per inhabitant") presume an order the resolver does not have: WI-743 cannot deliver declaration order by deriving rows in declaration order, because the index discards it on every variable-position retrieval. (4) A serialized resolution trace (proof records, explain output) is not reproducible.

FIX DIRECTION (verify before building; measure both). Make the variable-position walk deterministic AND declaration-ordered -- stable-but-arbitrary is not enough for (3). Two candidates: (a) at the index: keep `concrete` as an insertion-ordered structure (a `Vec<(DiscrimKey, Rc<DiscrimNode>)>` beside the hash for `get`, or an IndexMap-style map), so every walk is in assertion order and keying is untouched -- CLAUDE.md's representation note says the tree keys on structural `DiscrimKey`s and never on `TermId`; this changes ITERATION only; (b) at the collection point: sort `results` by RuleId (= assertion order) if `L` exposes it. Prefer (a): (b) re-sorts on every retrieval and depends on the leaf type. Census EVERY walk over `concrete` (two sites found by grep; look for clones, `.values()`, `.keys()`, and any other HashMap of children on the query path, e.g. named-arg edges) -- a second walk left in hash order reintroduces the defect one level down.

ACCEPTANCE (cargo-test via scripts/test.sh). A test loads three facts `p(a) p(b) p(c)` in that order and resolves `p(?x)`, asserting the SEQUENCE a, b, c -- on two independently built KBs in one process (two maps, two seeds), and the CLI run above repeated shows one order. CONTROLS, each stated at its site: a query with the position BOUND (`p(b)`) answers identically with the old walk restored -- passes either way BY DESIGN, it never walks; the COUNT of `p(?x)` answers is 3 either way BY DESIGN -- it is the order row alone that fails when the `HashMap` walk is restored, and the test header must say so. Also drive one multi-level case (`q(a, x) q(a, y) q(b, x)` queried `q(?u, ?v)`) so the order holds through nested walks, not only at the first edge. Then re-read WI-743's acceptance: its "declaration order" row depends on this ticket, and the dependency should be wired once this is filed.

