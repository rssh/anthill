## Attributes

- id: WI-20260902-TBZ4T-a-dotted-nullary-op-in-a-rule
- created: 2026-09-02T13:45:03Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-02T00:06:31Z

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

## Changes

### 2026-11-02T00:06:30Z — feedback — claude

DELIVERED in 78c33c83 (2026-11-02). The ticket's defect was already closed by the later dotted-call work (kernel-language §6.7, a dotted nullary operation is its call where the chain is reduced as an operand): measured on d6f92d5f, `dBind` binds 7 as `oBind`, `oBindP` and `dBindP` do, and the three controls hold (`holdsOp(ns.seven)` met by its goal in one namespace; a dotted rule in a value slot is the relation, `?r <=> tbz.inner.isFlag` binds `isFlag`; a dotted predicate is its name, `flag`). Pinned as controls in wi_tbz4t_dotted_member_one_term_test. FOUND driving those rows from other namespaces, and fixed: a written chain's MEMBER was held as the symbol the word resolves to where the chain is written, so `fact holds(zzf1.inner.seven)` written in `zzf1.outer` (where `inner` names `zzf1.inner`) was met only from that namespace — not from `zzf2`, a sibling, a namespace importing `seven`, or a query; the bare `zzf1.inner` the same; a sort member imported where a fact or goal is written, or by a query's `-i`, met nothing. The member is now the bare intern of its word in the term walk, the rule-body walk and the query walk (`dotted_member_symbol`), and in scaland's `reallocTerm`; §6.7 already states it. LEFT, a question for the user: a relative spelling and the qualified one (`inner.seven`, `zzr.inner.seven`) are still two terms — a namespace receiver is not collapsed to its symbol as a sort's is; whether a qualified operation or namespace name in a data slot is its symbol is the 'qualified name is the symbol' question not yet asked for those kinds. Full workspace 11,434 passed; families green (node carrier too); scaland 51 + 797.

