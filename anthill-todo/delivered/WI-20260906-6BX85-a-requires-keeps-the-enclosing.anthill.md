## Attributes

- id: WI-20260906-6BX85-a-requires-keeps-the-enclosing
- created: 2026-09-06T09:29:14Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-08T00:53:46Z

- acceptance: cargo-test, scaland-sbt-test

- tags: scoping

## Description

A `requires` KEEPS THE ENCLOSING CHAIN, so writing `requires S` silently puts EVERY NAME OF `S`'s NAMESPACE in the requiring scope, and a consumer's own sort of any of those names goes ambiguous. MEASURED AT 69 OF 75 FOR THE PRELUDE.

THIS IS A RECORDED RESIDUAL, NOT A NEW DISCOVERY, and the point of the ticket is that its SIZE was never counted. `wi_n2865_provision_edge_scope_test::a_requires_beside_a_provides_still_leaks` pins the behaviour and calls it deliberate; `intern.rs`'s `ImportOrigin::Provision` doc says `requires` is "deliberately NOT filed here". What neither says is how wide the reach is.

THE MECHANISM, exactly. `requires S` adds `S`'s OWN SORT SCOPE as a non-enclosing parent (`load.rs`, `add_parent` with `is_enclosing: false`) — that part is §8.6 working as designed, and it is what makes `S`'s operations resolve bare. Resolution then recurses into that parent AND INTO ITS PARENTS, one of which is `S`'s enclosing namespace, and §8.6 never filters an enclosing link. So the walk climbs out of `S` into the namespace that declares it and keeps going; `intern.rs`'s own comment names the endpoint, "reaches through to `<global>`". The stop exists — `parent_edge_stops_enclosing` — but fires only when EVERY writer of the edge is a wildcard import, an invocation flag or a `provides` conversion. A `requires` files its edge `ImportOrigin::Declaration`, which is not in that set, so the edge never stops.

MEASURED, 2026-09-06, by declaring a top-level `sort <N>` beside a `requires anthill.prelude.Field[T]` for every one-segment name `N` of `anthill.prelude`, and reading the load:

  69 of 75   AMBIGUOUS -- "ambiguous symbol 'N' in scope 'user.Poly': candidates [anthill.prelude.N, N]"
   3 of 75   clean: `Bool`, `String`, and `Field` ITSELF -- the consumer IMPORTS `Field`, and a local
             alias resolves at §8.6 step 2, before the parent walk runs at all
   3 of 75   a different error (`Int64`, `Float`, `BigInt` are host-bound)

So a sort that writes one `requires Field[T]` line cannot safely declare its own `List`, `Map`, `Set`, `Option`, `Error`, `Time`, `Duration`, `Function`, `Type`, `Relation`, `Console`, `Cell` ... 69 names, none of which it named, imported, or has any relationship to. The 69 are Field's SIBLINGS in `anthill.prelude`, which is precisely the reach WI-1089 protects.

WHAT IT COSTS TO CLOSE, and this number is already in the tree rather than estimated. `intern.rs` records: "Driven: stopping the chain below EVERY non-enclosing edge fails exactly that one row out of 5,724." The row is `wi1089_import_binds_one_name_test::adding_an_import_beside_a_requires_takes_no_name_away`, and the rule it pins is:

  namespace lib
    sort Sib  ... end
    sort Spec ... end
  end
  namespace app
    sort User
      requires lib.Spec
      entity user(n: Sib)      -- BARE `Sib`, never imported
    end
  end

`requires lib.Spec` must let the author write `Sib` bare. THE RULE IS THE LEAK: the 69 names are siblings exactly as `Sib` is, so there is no partial stop that keeps WI-1089 and drops the 69. Stopping the climb ABOVE the target's own namespace (at `anthill`, at `<global>`) is a separate and much smaller win and does NOT address this; `Ring` collided as a LOCAL of `anthill.prelude.algebra`, not as something above it.

SO THE DECISION IS A STRAIGHT TRADE, and it is the ticket's whole content: is "a `requires` reaches the target's unrelated siblings with no import" worth 69 shadowed prelude names at every consumer? The alternative costs the author one `import lib.{Sib}` line, which also SAYS what the sort depends on. The argument recorded for the current answer is that a `requires` clause is "written BY the author naming the target" while a conversion edge is crossed transitively — true of `Spec`, and not true of `Sib`, which the author never named.

NOT THE SAME AS WI-20260825-N2865, which is DELIVERED and fixed the `provides` half. This is the half N2865 deliberately left, now with a number on it.

WHY IT SURFACED. `stdlib/anthill/prelude/field.anthill` changed `requires Numeric[T]` to `requires Ring[T]` on 2026-09-06 (a field has no order; `Numeric` carries `requires PartialOrd[T]`). `Ring` lives in `anthill.prelude.algebra`, so the new edge added that namespace's two names, `Ring` and `VectorSpace`, taking the reachable set from 69 to 71. That change is defensible precisely BECAUSE the hazard was already 69 wide, and `algebra_spec_test::requiring_ring_across_namespaces_widens_the_sibling_reach` is the characterization row that keeps it visible. This ticket is where the 69 itself is owned.

ACCEPTANCE. Either (a) the chain is stopped below a `requires` edge, WI-1089's row is retired or rewritten to demand the import, and a consumer's own top-level `List`/`Map`/`Ring` beside a `requires` is a clean load -- with the count re-measured and recorded; or (b) the trade is explicitly declined IN THE SPEC, with §8.6 stating that a `requires` reaches the target's siblings and what that costs, so the next reader meets it as a rule rather than as a surprise. A silent third option -- leaving it in a test comment -- is what this ticket exists to end.

CONTROLS, each of which must still hold under (a): `wi1089_import_binds_one_name_test`'s remaining rows; `wi_n2865_provision_edge_scope_test` in full, including `a_requires_still_reaches_the_targets_siblings` (which (a) would REPLACE, and its replacement must be written, not deleted); `m460d_requires_reaches_spec_members_test` -- a `requires` must still reach the spec's own MEMBERS, which is the part nobody disputes; `wi1089_import_binds_one_name_test::control_requires_still_opens_the_spec`; and the workspace suite, whose baseline for this change is the recorded 1-of-5,724.

## Changes

### 2026-09-08T00:53:45Z — feedback — user

DELIVERED AS OPTION (a): the enclosing chain is stopped below a `requires` edge.

THE MECHANISM, one new origin in each port. `ImportOrigin::Requirement` (rustland
`intern.rs`, scaland `SymbolTable.scala`) is written by the ONE `requires` scope-wiring
site in each loader — `add_requires_parent` / `addRequiresParent` — and admitted by
`parent_edge_stops_enclosing` beside the wildcard import and (rustland) the `provides`
conversion. `ImportOrigin::Declaration` could not carry it: that origin also stamps
every ENCLOSING link and the bootstrap's prelude wiring, and stopping the chain below
those is exactly `wi1089…::an_import_of_the_enclosing_namespace_is_not_a_stop`'s failure.
`EnclosingLinks::StoppedByImport` is renamed `Stopped` — three clause kinds write it now,
and only one of them is an import.

THE STOP IS ON THE ENCLOSING HOP ALONE. A `requires` still reaches its target WHOLE: the
spec's own members, and whatever the target's own `requires` / `provides` / imports reach
beneath it. `import anthill.prelude.Ord.{gte}` still resolves through `Ord provides
WeakOrd` and `WeakOrd requires PartialOrd` — two edges the walk still crosses.

THE COUNT, RE-MEASURED with the ticket's own fixture over EVERY one-segment
`anthill.prelude` name (79 of them on this tree, not the ticket's 75):

                             BEFORE      AFTER
  `ambiguous symbol '<N>'`   78 of 79    0 of 79
  loads clean                 1 of 79   79 of 79

The single clean row before was `Field` ITSELF, which the fixture imports — a local alias
answers at §8.6 step 2, before the parent walk runs. CONTROL: the same 79 fixtures with
the `requires` line deleted are 0 ambiguous / 79 clean BOTH before and after, so the
clause was the whole cause and not some other property of a user sort at that name.
The ticket's 69-of-75 split differs only in fixture shape (it counted `Bool`/`String`
clean and three host-bound names as "a different error"); the reach is the same.

WI-1089'S ROW REWRITTEN, NOT RETIRED, as the ticket asked. Its invariant — an additive
`import` line beside a `requires` must take no name away — is restated on the spec's own
MEMBER (`op1`) rather than on `lib`'s sibling `Sib`; the two-writer and clause-order
questions it exists for are untouched by the change. `Sib`'s new answer, plus the one
`import lib.{Sib}` repair, is driven in the new file. Same edit in scaland's twin.

N2865's TWO RESIDUAL ROWS INVERTED, not deleted, each keeping its fixture:
  * `a_requires_beside_a_provides_still_leaks` -> `…_no_longer_leaks`. Its own note said
    it "INVERTS the day that lands"; it did, though not by the per-CLAUSE stop that note
    predicted — `requires` simply joined the admitted set.
  * `a_requires_still_reaches_the_targets_siblings` -> `a_requires_does_not_reach_…`,
    same fixture, opposite verdict, plus the import repair. Its original job (fail if the
    predicate is "simplified" to `!edge_is_enclosing`) is now carried by
    `an_import_of_the_enclosing_namespace_is_not_a_stop` alone, and only for the ENCLOSING
    half — the `Exposure` half cannot be driven, because a variant-exposure edge runs from
    a scope to a sort declared IN it, so the hop back out lands on a `visited` scope. Said
    at the site rather than credited to a neighbouring row.

`algebra_spec_test::requiring_ring_across_namespaces_widens_the_sibling_reach` is
rewritten to `…_costs_a_consumer_nothing`, which is what its own note instructed
("DELETE this row then; do not repair it") — both `Additive` (the reach `Field` always
had) and `Ring` (the reach this file's own change added) now load clean beside
`requires Field[T]`. `field.anthill`'s 40-line cost analysis is replaced by the rule.

A DEFECT THE SUITE COULD NOT HAVE CAUGHT, found by censusing every `ImportOrigin`
reader rather than by a red test. `SymbolTable::import_record_counts` classifies a
parent edge by a NEGATED `matches!` over the enum — the one reader the compiler cannot
fail on a new variant — so every `requires` edge in the corpus landed in the WI-995
audit's IMPORT-edge count. MEASURED: `parent_edges` goes 0 -> 24 on five of the six
corpus groups and 0 -> 28 on the sixth, and `wi995_import_file_locality_test` stays
GREEN throughout, because its only assertion was `alias_entries > 0`. Exactly the slip
WI-20260825-N2865 recorded at that same line for `Provision`. Fixed, and the zero is now
an `assert_eq!` with a message naming both ways the number has been wrong, so a third
variant goes red instead of quiet.

A SECOND FILE'S MEASUREMENT EXPIRED, and it is re-run rather than restated.
`wi_nb88h_member_import_stops_at_the_sort_test` states that backing out its own fix
(pointing the selective import's strategy 2 back at `resolve_in_scope`) fails FOUR rows.
Re-run with 6BX85 in place: THREE. `the_stop_survives_a_requires_hop` now passes, because
its route runs through a `requires` hop that stops the chain by itself — the row is kept
(its fixture is still the only one there that no enclosing link of `Host`'s own can
reach) and labelled as driving nothing today. That file's SECOND stated back-out was not
re-run; the note says so instead of restating a count.

DOCS. §8.6's "An import opens what it names" becomes "A CLAUSE opens what it names",
naming all three stopping clauses and the two that keep the chain, with the 78-of-79
measurement and the import repair. Proposal 044's step-3 sentence follows.
`field.anthill`'s header states the rule instead of the old cost. Both ports' resolver
docs name the three (rustland) / two (scaland) stopping clauses, and scaland's
`ImportOrigin` says at its own site that `Provision` is absent because N2865 is unported,
rather than leaving the reader to infer it.

WHAT `/code-review` FOUND, and it was all about the EVIDENCE rather than the change —
it verified the implementation itself by censusing every `ImportOrigin` reader. Six
findings, all acted on:

  1. THE ALGEBRA ROW STOPPED GUARDING THE STDLIB CLAUSE. Rewriting
     `requiring_ring_across_namespaces_widens_the_sibling_reach` into
     `…_costs_a_consumer_nothing` removed the only thing that failed when
     `field.anthill`'s `requires Ring[T]` was deleted — DRIVEN by the reviewer: with the
     clause commented out, all 23 `algebra_tests` and all 4,259 `wi_tests` stayed green.
     Fixed by writing `a_field_carrier_owes_ring`, the sibling of
     `a_field_carrier_owes_equality`: a carrier providing `PartialEq` + `Field` and no
     `Ring` must be refused naming `Ring`. RE-DRIVEN: with the clause backed out, that
     row alone fails, 23 of 24 pass.
  2. AND ITS COMMENT CONTRADICTED ITS OWN TABLE — the prose claimed the `Ring` arm
     measured the stdlib clause while the table three lines up said it did not.
     Rewritten to say what the row does measure and point at its replacement.
  3. WI-1089'S `requires`-BESIDE-`import` ROW WENT INERT FOR THE `all` QUANTIFIER.
     Restating it on the spec's own MEMBER made it unfalsifiable: `op1` is a local, and
     since this ticket BOTH writers of that edge stop the chain, so `all` and `any` agree
     there. DRIVEN by the reviewer: the flip left the row green. Fixed by writing the
     pair that still discriminates — `sort Outer { sort Inner { requires Outer } }`, one
     `(Inner, Outer)` origin list carrying `[Declaration, Requirement]`. RE-MEASURED over
     `wi_tests`: `.all(` -> `.any(` now fails exactly TWO rows, that one and
     `an_import_of_the_enclosing_namespace_is_not_a_stop`. Before it, one.
  4. SCALAND'S `forall` HAD NO WITNESS AT ALL — the reviewer measured the `exists` flip
     moving ZERO of 540 rows. Same fixture added there; the flip now fails exactly it.
  5. THE UNIT FIXTURES MODELLED A SHAPE THE LOADER CANNOT BUILD. Five `add_parent(…,
     is_enclosing: false)` calls in `intern.rs`'s tests file `Declaration`, and since
     this ticket every `add_parent` call site in `src/` passes `is_enclosing: true`. The
     one that matters is `an_edge_a_requires_also_justifies_is_not_filtered_in_either_order`,
     the sole measurement of the `[requires, exposure]` two-writer edge, which was
     building `[Declaration, Exposure]`. All pointed at `add_requires_parent`.
  6. DEAD CODE AND STALE ENUMERATIONS. `parent_edge_is_import_only` had been uncalled
     since N2865 and carried a live `dead_code` warning; deleted, with its two programs
     folded into `parent_edge_stops_enclosing`, where the `_ONLY` quantifier actually
     lives. Three prose enumerations that listed a `requires` edge as `Declaration` are
     corrected, and the one inside the walk now points at `origin_visible` instead of
     restating the list — that restatement is the reader the compiler cannot fail.

TESTS.
  * rustland, full workspace via `scripts/test.sh`: 36 binaries, 6595 passed, 0 failed.
  * back-out (drop `ImportOrigin::Requirement` from the admitted set), over `wi_tests`
    and `algebra_tests`: FIVE rows fail, 4,277 pass either way —
    `wi_6bx85…::a_requires_does_not_reach_the_targets_siblings`,
    `wi_6bx85…::a_consumers_own_sort_may_share_a_prelude_name`,
    `wi_n2865…::a_requires_beside_a_provides_no_longer_leaks`,
    `wi_n2865…::a_requires_does_not_reach_the_targets_siblings`, and
    `algebra_spec_test::requiring_ring_across_namespaces_costs_a_consumer_nothing`.
  * scaland `sbt test`: 540 total, 2 failed. Back-out (drop `ImportOrigin.Requirement`
    from `resolveRecursive`'s `namesItsTarget`): 3 failed — exactly ONE row moves,
    `ImportOpensWhatItNamesTest`'s "a requires does not open the module around the spec
    it names". The other two are PRE-EXISTING AT HEAD, measured in a
    clean `git worktree` at 78d597ab: `BootstrapTest`'s "WI-1066 CORPUS CONTROL" and
    "WI-1055 … the compiling count is a floor", both raising
    `anthill/prelude/field.anthill: Field's requires: cannot emit the type Ring — Ring is
    imported from anthill.prelude.algebra … Bootstrap emits no Scala import`. That is
    scaland codegen fallout from cb875e77 (`Field requires Ring`), whose evidence was
    36 Rust binaries and no sbt run. NOT TOUCHED HERE and not filed — it is a separate
    decision about whether Bootstrap qualifies a cross-package `requires` or emits an
    import.

