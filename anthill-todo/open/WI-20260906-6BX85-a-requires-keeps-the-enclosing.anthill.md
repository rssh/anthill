## Attributes

- id: WI-20260906-6BX85-a-requires-keeps-the-enclosing
- created: 2026-09-06T09:29:14Z

- status: Open
- status_agent: claude
- status_at: 2026-09-06T09:29:14Z

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

