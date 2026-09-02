## Attributes

- id: WI-20260902-TBZ4T-a-dotted-nullary-op-in-a-rule
- created: 2026-09-02T13:45:03Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T13:45:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DOTTED NULLARY OP IN A RULE-BODY DATA SLOT BINDS THE SYMBOL where the one-segment spelling computes.

MEASURED BY ME (found by /code-review during WI-20260902-VNWAW; re-measured, one file,
four rows, and again with VNWAW's change backed out — identical, so it is not that
ticket's):

  namespace zzf1.inner   operation seven() -> Int64 = 7   end
  namespace zzf1.one
    operation seven2() -> Int64 = 7
    rule oBind(?v)  :- ?v <=> seven2                -- 7
    rule oBindP(?v) :- ?v <=> seven2()              -- 7
  end
  namespace zzf1.outer
    rule dBind(?v)  :- ?v <=> zzf1.inner.seven      -- the SYMBOL `seven`   <- WRONG VALUE
    rule dBindP(?v) :- ?v <=> zzf1.inner.seven()    -- 7
  end

Exit 0, no diagnostic. One of four spellings binds a name where the other three compute,
which is exactly the class WI-20260902-CZJ2N closed for the one-segment spelling and named
at `nullary_op_call_or_ref` ("a rule-body DATA slot is included, deliberately: `rule c(?v)
:- ?v <=> seven` binds 7, matching §5.4").

THE MECHANISM, traced far enough to size it — VERIFY BEFORE FIXING. The dotted spelling
never reaches the arm that decides this. `build_body_atom_occurrence_inner`'s `Fn` arm
falls back to `materialize(convert_term(parse_id))` for an entity or reflect-form functor,
so a `<=>` atom is converted as a TERM, and `convert_term`'s value-position dotted reading
(proposal 052 §6.7 / WI-714, the `Relation[T]` citation) resolves the chain to `Ref(seven)`
before any occurrence-level reading happens. The one-segment name escapes that because it
reaches the walk's own `Term::Ident` arm, where `nullary_op_call_or_ref` builds the
`Expr::Apply`.

SO IT CANNOT BE FIXED AS A TERM, which is what makes it a ticket and not a line in VNWAW:
`nullary_canon` rewrites `Fn{f,[],[]}` straight back to `Ref(f)` for a name with no type
reading, so NO term expresses "call this operation" — the call is an OCCURRENCE-level
distinction (CZJ2N's own "WHY THE NODE AND NOT JUST THE TERM"). Closing it means changing
WHICH atoms fall back to `convert_term`, or reading the dotted child before the fallback
swallows the atom, and the same value-position reading serves operation bodies, where the
choice is TYPE-DIRECTED (§5.4's eta lift vs zero-arg call) and belongs to
WI-20260902-65BTX. Treat this as 65BTX's dotted sibling and settle them together.

ACCEPTANCE: `dBind` binds 7, i.e. the four rows above all compute. CONTROLS, all of which
pass today and must keep passing: `fact holdsOp(ns.seven)` beside `rule via(1) :-
holdsOp(ns.seven)` still answers 1 (measured — the store's nullary canon is what makes an
`Apply` and a `Ref` match, so this is not the WI-756 hazard it looks like, and the
one-segment spelling already proves it); a dotted citation of a RULE in a data slot stays
the `Relation[T]` value (WI-714's `Queen.find`); and a dotted PREDICATE in a data slot
keeps binding its name.

