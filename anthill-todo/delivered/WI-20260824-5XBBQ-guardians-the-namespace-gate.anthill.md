## Attributes

- id: WI-20260824-5XBBQ-guardians-the-namespace-gate
- created: 2026-08-24T09:06:49Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-28T19:24:56Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260823-SPGBP-wire-the-reflect-kb

- tags: anthill-side-check

## Description

THE NAMESPACE GATE IS A TEXT SCAN, AND A TEXT SCAN IS THE WRONG MECHANISM. `namespace_violations` (rustland/anthill-core/tests/guardians_test.rs:168) walks `src.lines()` for the prefixes `namespace ` / `sort ` / `enum ` and refuses a name in the trusted namespace that is not under `guardians.agent.`. It runs BEFORE the load, from the `guardians_check` host fn and again from the `check_candidate` helper. It reads lines because that was the only moment provenance existed: the candidate is loaded as `try_load_kb_prepared_files(&[lib…, fixtures…, candidate])`, one flat list into one KB, after which nothing distinguishes the candidate's declarations from the library's. FIX: load the candidate and ANALYSE it. WI-20260823-SPGBP made that possible and this ticket is its stated hand-off ("A gate over DECLARED names is still required, and is a separate ticket").

CORRECT THE NOUN SPGBP HANDED OVER. It said "a gate over DECLARED **names**", so this ticket was first written as a scan repair. Its own measured failure is a CLAUSE — `fact guardians.Checked(…)` — and three of the four attacks below are clauses, not names. The gate is over what the candidate DEFINED *and* what it ASSERTED.

### MEASURED — four attacks, all loading clean

Driven through `rustland/target/debug/anthill load` over `lib/` + `fixtures/` + one candidate, `good.anthill` removed. Baseline (lib + fixtures + good): `loaded: 2895 facts, 218 rules`.

**A1 — the safety fact, forged about itself.** A candidate declaring `sort guardians.agent.ForgeTriage … provides Triage[C = ForgeTriage]`, then

    namespace guardians
      fact Checked(carrier: "guardians.agent.ForgeTriage", spec: "guardians.Triage")
    end

loads at `2896 facts, 218 rules`, and `query --mode functor 'guardians.Checked'` goes from `0 result(s)` to the forged row. This is the attack the ticket already carried, reproduced. It is the LEAST severe of the four: `agent_is_safe` also needs `ToolAlgebraSound`, which has no facts, so the claim is underivable regardless.

**A2 — THE CONCEALMENT GUARANTEE, INVERTED. This is the severe one and it is new.** `guardians.mentions_all` is the `ensures` on `Triage.run` in the trusted `spec.anthill`, and its own comment calls it "exactly the CONCEALMENT half of the injection". Proposal 061 appears to protect it — a bare bodied clause from a second file is REFUSED, loudly, naming both files:

    error: …/evil.anthill:7:3: the predicate `mentions_all` has rule heads in 2 files
    … and no declaration. … write `rule mentions_all(…)` in 'guardians' (proposal 061).

But 061 is a HYGIENE rule, not a trust boundary, and the diagnostic tells the attacker exactly what to write. The candidate supplies the declaration itself:

    namespace guardians
      rule mentions_all(?)
      rule mentions_all(?r) :- omits_some(?r)
    end

`loaded: 2885 facts, 218 rules`, no diagnostic, and `guardians.mentions_all` now has TWO clauses — the trusted `:- not(omits_some(?r))` beside the candidate's `:- omits_some(?r)`. The postcondition now succeeds exactly when the report OMITS a message. Unlike A1 this is live today: `mentions_all` is cited by the trusted spec and is the tier-2 obligation the whole design says no type expresses.

**A3 — reflect metadata, hand-written.** A candidate writing `fact SortProvidesInfo(sort_ref: LiarTriage, spec: LiarTriage)` under `import anthill.reflect.{SortProvidesInfo}` loads clean, and the functor then carries BOTH rows:

    SortProvidesInfo(sort_ref: LiarTriage, spec: SortView(Triage, C: LiarTriage))   -- loader
    SortProvidesInfo(sort_ref: LiarTriage, spec: LiarTriage)                        -- candidate

indistinguishable in the clause store except by well-formedness. THIS DECIDES THE SHAPE OF THE GATE: a query that reads `SortProvidesInfo` / `OperationInfo` / `SortInfo` and believes the answer is reading a channel the candidate can write. Any check phrased over reflect facts needs the loader-emitted rows separated from the source-asserted ones — which is this ticket's one genuinely new piece of Rust.

**A4 — the accepted carrier is a constant.** `guardians_check` returns `entity0(…, "guardians.CheckResult.Accepted", vec![Value::Str("guardians.agent.Generated".into())])`. `Accepted(carrier: String)` is documented in harness.anthill as "the verdict a proof could cite", and it cites a hardcoded name that no candidate ever declares. The checker never learns which carrier it accepted, and its `spec: String` parameter is ignored entirely.

### THE QUESTION TO ASK

Load the candidate into a layer over the trusted base and ask, positively — this is the user's framing ("ask it to implement the given sort, where the operation we call has a fixed set of effects"), made precise:

* **G1 — PROVISION.** There is a carrier `?c` with `SortProvidesInfo(sort_ref: ?c, spec: SortView(?spec, C = ?c))` for the `?spec` the harness asked for, and `?c` is a symbol THE LAYER DEFINED. Refuse if there is none (a candidate that implements nothing must not be Accepted — A4), and refuse if `?c` is not the candidate's (it must not nominate a trusted carrier as its own answer). `?c` is what `Accepted` reports, replacing the constant.
* **G2 — CLAUSE CONTAINMENT.** Every clause the candidate's SOURCE contributed — `fact` and `rule` alike — heads at a symbol the layer defined. One rule, and it refuses A1, A2 and A3 together, with no name list and no spelling enumeration. The `rule` half is not optional: A2 is a rule, and it is the severe one.
* **G3 — NAMING.** Every symbol the layer defined is under `guardians.agent.`. Weakest of the three and it is hygiene rather than security once G2 holds; keep it for the diagnostic, which should name the DECLARATION rather than a line number.

`?spec` must be a REFERENCE, not the ignored `spec: String` of A4, and its budget row must be read from the BASE — before the layer is applied — so a candidate cannot restate the budget it is being held to.

### WHAT IS NOT RE-ASKED, AND WHY

THE EFFECT BUDGET IS DISCHARGED BY THE LOAD, NOT BY THE QUERY. The typer's override-refinement pass already bounds the override's declared row by the spec's (`wide_row` → "effects must not widen"; `wide_row_modify` → the same arm at a `Modify` target) and the body's inferred row by the declared one (`bad_checker` → "got undeclared effect: Model"). Re-deriving that from `OperationInfo.effects` would be strictly WEAKER, because A3 shows that fact is forgeable while the typer's comparison is not. So the row appears in the verdict as REPORTED — `Accepted` carries the carrier and the row it was checked against, making the verdict citable — and not as re-checked. Say this at the gate's site, or the next author re-implements the typer in anthill and believes they have added security.

### HOW THE GENERATED TEXT REACHES THE LAYER — and three gaps

The API is already there and needs nothing new: `KB.loaded(sources: List[T = String]) -> KB effects Error` parses each text and runs `load_incremental(&mut kb, &refs, NullResolver)` over ALL of them as ONE batch, so a multi-file candidate loads with cross-file mutual recursion intact (WI-321's 4-pass `scan_definitions` invariant). Strings in; no paths, no filesystem, no SourceUnit. `expect_string_list` is strict on purpose — a malformed spine errors rather than loading a subset, so a candidate cannot be reported clean on text that never reached the KB.

**GAP 1 — THE SOURCES ARE ANONYMOUS. DOWNGRADED BY GAP 2's SETTLEMENT, NOT CLOSED.** With one candidate source there is nothing to disambiguate: a `line:col:` diagnostic is already actionable, and the parse path's `source {i}:` prefix is sufficient. So this is NOT on the critical path and no `loaded` signature change is required. It becomes live again the moment a candidate may be several files, and the rest of this note is kept for that. `kb_loaded` calls `parse(text)` and never `.with_path(…)`, so `ParsedFile.path` is `None` and `render_located(None, body, _) => body` drops the file name outright — its own comment concedes it ("There is no path to render: a scoped source is a String the caller supplied"). Parse errors carry a positional `source {i}:` prefix; LOAD errors carry nothing. `Rejected(diagnostics)` is fed straight back to the model as `feedback` (harness.anthill: "a model repairs from a diagnostic better than from a structured record"), so with several files in, the model receives errors it cannot localize. A2's own message is the demonstration: `has rule heads in 2 files — <>, <>`. FIX, and it is small: let `loaded` take names beside texts — a `List[Pair[String, String]]` or a `loaded_named` sibling — and thread them to `with_path`.

**SETTLED (user, 2026-08-25): THE EXAMPLE STAYS FILE-FREE.** The model surface is one primitive — `Llm.complete(self, p: Prompt) -> Text[Untrusted]`, text in, text out — and the generated program never touches a filesystem. No write-file / read-file capability is granted, for three reasons. It would move the trust boundary to the wrong side: `Source` is opaque with `Checker.check` its ONLY elimination, which is what makes unverified-ness a TYPE property, and a written file exists in the world before anything checks it. It is `wide_row_modify` at full scale: a filesystem write grants `Modify` over `examples/guardians/lib/`, so a model that can write files can rewrite the spec it is being checked against — a more direct defeat than A1-A3 together. And it buys nothing, since `loaded` takes strings: written files would be read back, adding a round trip and a TOCTOU window between check and use. CONSEQUENCE FOR THIS TICKET: delete `lib_dir` from `entity file_harness(lib_dir: String)` and `entity load_checker(lib_dir: String)` — grep over the whole example and `guardians_test.rs` returns those two declaration lines and NOTHING else, so both fields are dead, and a dead filesystem path on a carrier reads as "this component works on files" when it does not.

**GAP 2 — SETTLED (user, 2026-08-25): A CANDIDATE IS ONE SOURCE.** `sort guardians.Source; entity source(text: String)` stays exactly as declared, and so do `Harness.generate -> Source` and `Checker.check(src: Source, …)`. The example stays small; `loaded` is handed a one-element list. Nothing here changes, and G1/G2 are written against the singular form. Revisiting this reopens GAP 1 with it.

**GAP 3 — UNMEASURED, AND IT CUTS BOTH WAYS.** Under the layer design the trusted `spec.anthill` is in the BASE and only the candidate is in the LAYER; A2 was measured with both in one flat load. Whether proposal 061's "rule heads in 2 files" check consults the base, or sees only the one-file batch and admits the clause, decides whether A2 becomes HARDER (061 still refuses, and the candidate needs the declaration trick) or EASIER (061 never fires, and the bare clause lands). G2 catches it either way, so the gate is unaffected — but 061 stops being a second line of defense in the second case, and the A2 fixture changes. MEASURE THIS FIRST; the fixture depends on the answer.

### WHAT RUST SUPPLIES — "the technical binding, the essence in the example"

1. **The layer delta, as OPERATIONS and not as facts.** `SymbolScopeSnapshot.defs_prefix` (intern.rs:718) fixes the symbol high-water mark and the `rules` rollback (layer.rs:106) fixes the clause mark, so the DEFINED and ASSERTED halves are already exact. Expose them as reflect operations over a `KB` value — NOT as emitted facts, because a fact is a channel A3 shows the candidate can write, and the gate would then read a relation its subject can forge.

   A THIRD CHANNEL EXISTS AND NEITHER G1 NOR G2 COVERS IT: a layer can MUTATE an existing symbol's definition without minting a new one, so the high-water mark does not see it. `SymbolTable::restore_scoped` does `self.defs[..defs_prefix.len()].clone_from_slice(&defs_prefix)` — a full prefix COPY rather than a truncation, which is what one writes when base defs get written to, and SPGBP says so outright ("a kind a layer added to a base symbol is undone"). It is DETECTABLE — compare `defs[..n]` against the snapshot prefix — but is not exposed today. MEASURE whether a candidate can reach it (a redeclaration of an existing trusted name is the obvious probe, and may simply be a duplicate-declaration error) before deciding whether it is a fourth gate rule or a non-issue to record. Do not assume either.
2. **Source-asserted vs loader-emitted clause provenance.** The one new thing in `load.rs`. Without it G2 REFUSES `good.anthill`: its `provides Triage[C = GoodTriage]` makes the loader assert a `SortProvidesInfo` row headed at `anthill.reflect.SortProvidesInfo`, a symbol the candidate did not define (measured — the row is in the baseline KB). The loader knows which it is doing at the moment it asserts; a provenance bit on the clause is enough. A name-based exemption ("head functor not in `anthill.reflect`") is the wrong shape and re-opens A3.
3. Nothing else. `KB.loaded` already exists; the policy is rules in `examples/guardians/lib/`.

### DROPPED: the SourceUnit prerequisite

This ticket previously required emitting `anthill.reflect.SourceUnit` with an added `sorts` field, then joining it to `SortInfo`. Four reasons it goes, and the last is the one that matters:

* **Granularity.** SourceUnit answers "which FILE contributed this"; the gate asks "did the CANDIDATE contribute this". One candidate in one layer makes those the same question, so the file axis is spare — nothing attributes WITHIN a candidate.
* **The marks already exist**, shipped with SPGBP and load-bearing for discard correctness, so reading them costs nothing new.
* **SourceUnit would have to be built and then widened** — declared, documented as emitted, emitted nowhere, no `sorts` field. Three steps to reach a weaker answer.
* **SOURCEUNIT IS A FACT.** A3 measures that a candidate can hand-write reflect metadata rows, so a gate joining `SourceUnit` to `SortInfo` lets the candidate write its own `SourceUnit` row claiming trusted code declared its symbols. The old plan put the provenance channel INSIDE the thing being policed. The layer marks are outside it — Rust-side state, not clauses. This is the same reason item 1 above says operations rather than facts. That SourceUnit is declared at reflect.anthill:164, documented "Emitted by the loader after processing each file", and emitted nowhere (the only hit across rustland is a generated struct under `target/`) stays true and stays a defect — it is simply someone else's.

### ACCEPTANCE

A1, A2 and A3 above are each REFUSED, each diagnostic naming the offending clause and the symbol it heads at (A2's must name `guardians.mentions_all`, not a line). The verdict for an accepted candidate carries the REAL carrier symbol and the row it was checked against — `agent/good.anthill` yields `guardians.agent.GoodTriage` and `{External, Model, Error}`, never the `guardians.agent.Generated` constant. A candidate that loads clean and provides NOTHING is refused rather than Accepted. `namespace_violations` and its `src.lines()` scan are DELETED, and `harness_rejects_a_candidate_that_reopens_a_trusted_namespace` is rewritten against the three attacks. The gate is expressed in `examples/guardians/lib/`.

CONTROLS, which is what keeps this from degrading into refuse-everything: `agent/good.anthill` still passes, and so does a candidate declaring only under `guardians.agent.` and asserting nothing. State at the site which tests fail when the change is backed out — the three refusals — and which pass either way by design — the taint and row tests (`leak`, `wide_row`, `wide_row_modify`, `bad_checker`, `minting`, `generate_from_content`), since none of them touches provenance. ADD a control the current suite lacks: a candidate that redeclares its own `mentions_all` in `guardians.agent` and restates the `ensures` against it, to measure whether contract refinement (WI-20260822-59CDQ) already binds the override's postcondition to the spec's — if it does not, that is a separate finding and is reported, not folded in.

Full workspace green via rustland/scripts/test.sh.

### DELIVERED

`namespace_violations` and its `src.lines()` scan are GONE. The gate is
`examples/guardians/lib/gate.anthill` — anthill, over a discardable layer — and the
Rust side supplies exactly the two things this ticket said it would.

**The three measurements the ticket asked for FIRST, and both changed a decision.**

* **GAP 3 — 061 does NOT consult the base, so it is not a second line of defence.**
  The A2 bare clause (`rule mentions_all(?r) :- omits_some(?r)`, no declaration) loads
  in a layer with NO diagnostic; `guardians.mentions_all` goes from one clause to two.
  On a flat load 061 refuses it loudly and tells the attacker to add a declaration; in a
  layer it never fires. So the FIXTURE is the bare clause — the form that actually
  reaches the KB under the design the checker uses — and the "supply the declaration"
  trick the ticket described is not needed.
* **The third channel is REACHABLE, and it is a fourth rule folded into G3.** A layer
  can redeclare a name the base owns (`sort guardians.Triage`): it loads, the symbol is
  the SAME, so the mint high-water mark never sees it, and it asserts no clause for G2
  to catch. Measured consequence: a SECOND `OperationInfo` row for `Triage.run`, so the
  reported row goes `[External, Model, Error]` →
  `[External, Model, Error, External, Model, Error, Filesystem]`.
* **It does NOT defeat the typer**, and that is why the budget is reported rather than
  re-checked: a widening carrier is refused with the identical `effects must not widen`
  message with and without the redeclaration, because the override-refinement pass
  compares against the stored signature and not against the fact. What it defeats is a
  naive READ of the budget — so `spec_budget` runs BEFORE `KB.loaded`.

**What Rust supplies — the two items, and nothing else.**

1. `KB.layer_symbols(kb) -> List[LayerSymbol]` and `KB.layer_clauses(kb) -> List[LayerClause]`,
   over a `Value::Kb`. `LayerDelta` (in `eval::layer_arena`) records the symbol
   high-water mark, the clause mark, and the layer's DECLARATION ledger at push time.
   The ledger is the third-channel half and cannot be derived later: `decl_sites` is
   PER-SCAN, so a second `loaded(…)` overwrites it. `LayerSymbol` carries BOTH flags —
   `minted` (the layer created the symbol) and `declared` (the layer wrote a declaration
   at it) — because neither implies the other: a rule head mints without declaring
   (§8.6), a redeclaration declares without minting. Both readers REFUSE the ambient
   `kb()` and a layer with a later one on top of it; the empty list is the one wrong
   answer available, since it reads as "this candidate contributed nothing".
2. `ClauseOrigin::{Source, Derived}` on `RuleEntry`, `Derived` at construction and
   flipped by `mark_source_clause` at the three source sites (`load_fact`, `load_rule`,
   the two constraint emitters). `ClauseKind` could not stand in: its own doc says
   `Fact` covers "including loader-synthesized metadata facts". Without it G2 refuses
   `good.anthill`, whose `provides Triage[C = GoodTriage]` makes the loader bank a
   `SortProvidesInfo` row at a symbol the candidate did not declare.

**The gate — G1/G2/G3 in `lib/gate.anthill`, in the order G3, G2, G1.** The order is
load-bearing: G1 reads `SortProvidesInfo`, a relation the candidate can write, so it is
believed only after G2 has refused a source-written clause at a reflect functor.

**Two things the design met on the way, both recorded at their sites.**

* A DOT on an `Iterable.find` callback's parameter does not resolve to a field:
  `lambda ls -> ls.minted` survives the typer and dies at eval as
  `unhandled Expr variant: DotApply`. It is the COMBINATOR and not the lambda — the same
  dot on a `List.filterElems` callback works (`naming_violations` writes `ls.symbol`),
  and `find` reaches its element through `List provides Stream provides Iterable` where
  `filterElems` projects `xs.T` directly. A constructor PATTERN on the parameter needs no
  such projection and binds where the dot cannot, so the gate uses `find` throughout and
  hand-rolls no recursion. (First shipped AS recursion on the wrong diagnosis — that the
  combinator itself could not be used — and corrected on review; re-measured after the
  rebase onto the carrier-projection typer commits, where it still reproduces.) Filed as
  WI-20260828-N2FHM: the gate carries the workaround, and a program that loads clean and
  then dies on a host-level `Internal` is a defect in its own right.
* Reading the spec out of a `SortProvidesInfo` row needs `reify`, not `extract` or
  `term_field`. The loader writes `SortView(Triage, C = GoodTriage)`; the spec is the
  wrapper's first POSITIONAL argument, `term_field` reads named arguments only, and
  `extract` classifies the wrapper (`Parameterized(base: SortView, …)`) rather than
  looking through it. `reify` answers `FnRepr(SortView, [FnRepr(Triage, [])])`.

**A clause at an UNDECLARED name is refused, and that is the rule.** A `fact Note(...)`
whose functor was never declared heads at a bare short-name intern with no qualified
name, so it belongs to no namespace and containment cannot hold for it. Its control is
one `entity Note(text: String)` away.

**A4 — the verdict.** `Checker.check(self, src: Source, spec: Symbol)`: the spec is a
REFERENCE. `Accepted(carrier: Symbol, spec: Symbol, budget: List[T = String])`, and
`agent/good.anthill` yields `guardians.agent.GoodTriage`, `guardians.Triage`,
`[External, Model, Error]`. The dead `lib_dir` field is gone from `file_harness` and
`load_checker`. The four `Checker` fixtures return `Rejected` with a one-line reason —
honest for bodies that perform no check, and they cannot name a carrier they never found.

**CONTROLS — and the ticket's two control clauses conflict, so one had to give.** The
ACCEPTANCE says "a candidate that loads clean and provides NOTHING is refused"; the
CONTROLS list says "a candidate declaring only under `guardians.agent.` and asserting
nothing" passes. For the one program that is both — `sort guardians.agent.PoliteTriage;
entity mk` — those cannot both hold, and the acceptance is the one that names a defect
(A4), so it wins: that program is now the FIXTURE for
`a_candidate_that_provides_nothing_is_refused`.

What replaced it is a stronger control, because the old one could not tell a working
containment rule from one that refuses every clause: `a_candidate_may_declare_and_assert
_freely_inside_its_own_namespace` declares under `guardians.agent.`, writes a `fact` AND
a `rule` of its own, provides `Triage`, and is ACCEPTED. `good.anthill` still passes and
now asserts the VERDICT rather than its success. The taint and row
tests pass either way by design — none touches provenance — and
`harness_accepts_a_well_formed_generated_agent_and_names_what_it_accepted` is the
control for `hand_written_reflect_metadata_is_refused…`: without the provenance bit the
first reds and the second passes for the wrong reason.

**The extra control the ticket asked for, MEASURED and reported, not folded in.** A
candidate that declares its own `guardians.agent.mentions_all` and restates the
`ensures` against it is REFUSED by the typer:
`'guardians.agent.ShadowTriage' overrides 'guardians.Triage.run' but does not refine it:
it weakens the postcondition`. Contract refinement (WI-20260822-59CDQ) binds the
override's `ensures` to the spec's predicate BY SYMBOL, so a same-named local cannot
discharge it. No separate finding.

**One thing did not move, and is stated rather than assumed.** `LoadChecker.check` stays
a Rust host function, because anthill has NO handler surface — there is no `handle … with
Error` and nothing in the stdlib installs one, so an anthill body cannot turn
`KB.loaded`'s raise into `Rejected(diagnostics)`, and that conversion is what feeds the
repair loop. The host function now does exactly three things: read the budget from the
base, load into a layer (catching the `load_failed` payload as the verdict), and call
`guardians.gate`. The POLICY is anthill; the technical binding is Rust.

**`anthill-core` now dev-depends on `anthill-stl`.** `gate.anthill` calls
`qualified_name`, which only `register_reflect_builtins` binds (WI-SPGBP wired it into
`runner::register_runtime`), so without this the example's own test would run against a
smaller reflect surface than the CLI has and the gate would die `OperationBodyMissing`.

**GAP 1 stays open and stays downgraded**, exactly as the ticket left it: one candidate
source, so `source {i}:` and a `line:col:` are actionable, and no `loaded` signature
change was made.

### REVIEW — what `/code-review` at high effort found, and one of them was real

**A `⊥` DENIAL CRASHED THE GATE INSTEAD OF BEING REFUSED BY IT.** `load_rule` marks a
denial `Source` deliberately (the span install skips it, and a denial is every bit as
much a thing the source wrote), but `Term::Bottom` heads at NO symbol — so
`layer_source_clauses` yielded `(None, …)` and the builtin raised an
`EvalError::Internal`, which is not a `load_failed` payload and so never became a
verdict. Three lines of candidate source (`rule ⊥ :- InMailbox(...)`) denied the checker
an answer. My own comment asserting that shape was unreachable was the wrong half of the
contradiction. `LayerClause.functor` is now `Option[T = Symbol]`: a denial is REPORTED
with `none` and refused by the containment rule, because a clause a policy cannot see is
a clause it cannot refuse — and a denial installed over the trusted base is exactly the
kind a policy wants to refuse. Fixture: `a_denial_over_the_trusted_base_is_refused`,
measured.md E7.

The other three, each addressed at its site:

* **Fact dedup can hand back a pre-layer `RuleId`**, so a source `fact` restating one the
  base already holds marks a row BELOW the clause mark and never reaches G2. Recorded at
  `mark_source_clause` rather than worked around: the dedup happened *because* the clause
  was already there, so the layer added nothing to refuse, and a per-layer clause identity
  distinct from `RuleId` would buy a refusal for a program that changed nothing.
* **The declared-only loop skipped the `is_resolved` filter** the minted loop applies and
  the doc promises. Fixed — an unresolved ledger entry would have been refused under its
  bare intern name.
* **`is_innermost` reads the LIVE stack**, which still holds a retired-but-unswept layer.
  That is correct rather than approximate — a released layer stays APPLIED until the sweep
  restores it — and the message now says so.

