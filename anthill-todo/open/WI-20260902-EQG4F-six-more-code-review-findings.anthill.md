## Attributes

- id: WI-20260902-EQG4F-six-more-code-review-findings
- created: 2026-09-02T12:00:08Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T12:00:08Z

- acceptance: cargo-test, scaland-sbt-test

## Description

SIX MORE /code-review FINDINGS ON THE NULLARY-CANON COMMITS (CZJ2N + 719FJ) — NOT RE-MEASURED BY ME.

PROVENANCE AND ITS LIMIT, first, because it decides how to use this ticket. These came
from a `/code-review high` run during WI-20260902-8K4RB, whose scope was
`origin/main...HEAD` — five unpushed commits, wider than the diff being reviewed. I
re-measured only the two findings about 8K4RB's own diff (fixed in that commit) and the
HIGH dotted-citation one (its own ticket, with my own table). The six below are the
reviewer's evidence QUOTED, with the code shape confirmed by reading in one case and
nothing driven in any. TREAT EACH AS A HYPOTHESIS WITH A SITE, NOT A DIAGNOSIS: build the
failing fixture first and drop the ones that dissolve.

1. scaland `discrim/SubstTree.scala:62` (also 114/154/223/300/389) — the index now keys
   `Term.Ref(s)` as `Functor(s)/Arity(0)`, identical to `Fn(s,[],[])`, while
   `KnowledgeBase.alloc:82` deliberately keeps those two DISTINCT for a `SymbolKind.Sort`
   (there is a test asserting `Fn(S) != Ref(S)` — wildcard vs concrete spec identity) and
   `Substitution.unifyMatch:122` still refuses the pair. Claim: a ground
   `:- entity_of(?e, Shape)` retrieves a fact stored with `Fn(Shape)` off the tree walk,
   which for a ground position IS the decision, contradicting `unifyMatch`.

2. scaland `kb/KnowledgeBase.scala:622` — `getBuiltin` now answers through
   `headFunctorOf`, so a NULLARY goal gets a builtin tag; for `BuiltinTag.Not` that
   reaches `stepNaf` (SearchStream.scala:269), whose `Builtins.firstArg:52` falls back to
   `case _ => goal` — the negand becomes the `not` goal itself and a fresh sub-stream is
   made at depth 0, so `maxDepth` never bites. Claim: unbounded recursion, newly
   reachable via 719FJ's dotted spelling (`rule r(1) :- anthill.kernel.not`).

3. scaland `anthill-smt-gen/SmtGen.scala:489` and `:336` — `classifyHead`'s
   `f.posArgs.isEmpty => HeadShape.Bottom` arm is dead now that no zero-arg `Fn` survives
   `alloc`, so a nullary head falls to `HeadShape.Unsupported`; `processBodyGoal`
   likewise hard-errors `non-Fn body goal` for `:- p()`. `Policy.scala` and
   `TacticEmit.scala` were updated for all three carriers; SmtGen is the one missed.

4. scaland `load/Loader.scala:1678` (same at `:1606`) — THE CANON IS SPLIT: `alloc`
   rewrites `Fn(f,[],[])` -> `Ref(f)` unconditionally (modulo the Sort gate) but the
   loader promotes a bare name only `if kb.symbols.isResolved(...)`, so an UNRESOLVED
   name still yields two terms with two discrim keys. Claim: reachable wherever
   `ruleIntroducedFunctor` declines to mint — e.g. a multi-head `rule aa, bb :- base(1)`,
   after which `:- aa` answers and `:- aa()` does not, silently. Note the reviewer's own
   caveat: CZJ2N's 2x2 test uses SINGLE-head rules, which mint, so it passes either way.

5. rustland `anthill-stl/src/reflect/reader.rs:488` — the new
   `Functor{pos_arity:0, named_arity:0} => on_ref` arm is WIDER than the `ViewHead::Ref`
   it replaced, while the inverse walk (`reflect_walk`, ~571) rebuilds `RefRepr` as
   `CoreTerm::Ref`. Claim: a canon-EXEMPT Sort-kinded `Fn{S,[],[]}` (the empty
   `ListLiteral()`) changes `TermId` across a reify round trip, and
   `persistence/print.rs:985` writes the parentheses only for `Term::Fn` — so it
   persists as a bare name and reloads as a name reference, which is the WI-1099 failure
   that arm exists to prevent.

6. rustland `anthill-stl/src/reflect/bridge.rs:267` — CODE SHAPE CONFIRMED BY READING,
   behaviour NOT driven. `find_entity_schema`'s new
   `CoreTerm::Ref(_) | CoreTerm::Ident(_) => return Some(Vec::new())` RETURNS where the
   old `if let CoreTerm::Fn` CONTINUED the scan. Claim: with `fact p` written before
   `fact p(x: 1)`, the scan takes the empty schema off the first row and the `p(x: 1)`
   rows silently vanish. The reviewer's proposed shape is `_ => {}` plus `Some(vec![])`
   only when the whole scan found nothing — which has its own control, since the arm was
   added to fix a real zero-rows bug (its comment records it).

7. rustland `anthill-core/src/kb/load.rs:19375` (LOW) — `create_occurrence` now records a
   `functor_spans` entry for every `Term::Ref`/`Ident`, not only applications. The map is
   FIRST-WRITE-WINS and is the declaration-site fallback (load.rs:15619,
   typing.rs:61317/61480/61574/61731/62301). Claim: an eta reference or data-slot mention
   in an earlier-loaded file claims the span, so a later `DuplicateOperation` / pattern /
   effect diagnostic points at the USE site instead of the declaration.

SPLIT THIS if the measurements diverge — items 1-4 are scaland and 5-7 rustland, and
nothing couples them but the commit they came from.

