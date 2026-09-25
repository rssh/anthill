## Attributes

- id: WI-20260925-SHED7-inductive-relations-proposal
- created: 2026-09-25T06:38:27Z

- status: Open
- status_agent: user
- status_at: 2026-09-25T06:38:27Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260925-P7VP4-a-rule-body-call-s-requires

- tags: typing

## Description

FILLABLE AND SORTDOMAIN (proposal 067 + proposal 060 §2.3). `anthill.reflect.Fillable` (067) is the INTERFACE a solver requires: ONE rule, `fill(?x)` — fills ?x with a value of T, generating in mode (out), checking in mode (in); a MONOID under `combine` (ordered concatenation) and `empty`. `SortDomain provides Fillable` (060 §2.3): the implementation the loader derives for every sort with constructors, and its `fill` IS the sort's domain. A typed head means `rule p(?x: T) :- body` ≡ `rule p(?x) :- body, SortDomain[T].fill(?x)`. WI-20260911-5G28A's S3b and later steps build on it (user, 2026-09-25). Filed as "inductive relations"; the design settled on Fillable the same day, so the slug is older than the name.

WHY. For a caller's rigid X the type is a name, not a domain, so the domain reaches a clause as a dictionary (060-typedomains, 060-implementation §7.3). MEASURED on 861b3013, S3a's route answers wrongly: `rule el(?x: T) :- true` in `sort Wrap[T]` answers NOTHING for `Wrap.el(7)` and `Wrap.el([red()])`, and undecided for `[1, 2]`, `none()`, `[]` — each should be one definite row. And MiniSat cannot be written over an abstract collection builder: over List it works (tiny-sat) because the program names the shape; a solver written once must require `Fillable` and reach it through the dictionary its caller hands in.

SCOPE, in order (067 §6):
1. 060 §2.3's decisions — what 5G28A's S3b needs: the spec; SortDomain's `fill` derived PER ENTITY (`SortDomain[List] = combine(SortDomain[List.nil], SortDomain[List.cons])`, applied by the loader) and PER FIELD (the sort itself: the recursion; a parameter: a condition of the provision, filled through its SortDomain; a concrete type: must be Fillable); inside a case the recursive fields first, the cases with no recursive field first (WI-743's two rules, measured); a primitive's `fill` is the waiting type check; a condition is resolved when `fill` READS it and a read WAITS while its type is unpinned (`[]` is a `List[?]`); `fill` found through the provisions — SortOpsTable rows for a spec's rule members — replacing S3a's name lookup `typing::sort_domain_relation`; the type-keyed `domain(?x, T)` / `domain_member(?x, T)` / `domain_leaf` retire into it.
2. 067 §5 question 3 (the monoid's home, `combine` at run time), decided with the user.
3. 067 §4's generalization — MiniSat over a collection builder — as the acceptance, once 067 §5 questions 1 (the collection pattern) and 2 (free cells, labelling) are decided with the user.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven): the six `Wrap.el` rows — red(), 7, [red()], [1, 2], none(), [] — one definite answer each; `q(?h) :- Wrap.same([?h], [red()])` (rule same(?a: T, ?b: T) in sort Wrap[T]) answers red, green; S3a's rigid rows (3 / 2); the S3b flips — `Wrap[T = Colour].dom.takeN(5)` = 3, `List[T = Letter]`'s value face `.takeN(5)` = 5; wi_5g28a_rule_head_type_variables_test's pinned rows (answers 1, mismatched 0, two_calls 1, nested_row 1, anylist with no definite row). Controls: the classic-mini examples (tiny-sat 2, alphabet-words 27 / 12 / 100, map-colouring 6).

## Changes

### 2026-09-25T10:08:48Z — feedback — claude

HANDOFF — IMPLEMENTATION PLAN FOR STEP 1 (claude, 2026-09-25; for the next session). Design: proposal 060 §2.3 (SortDomain), proposal 067 (Fillable), docs/design/060-implementation.md §7.3 (the one-mechanism design and the measured S3a defect). Committed at 763263c4, not pushed.

STARTING STATE. docs/kernel-language.md holds the USER's own two uncommitted hunks (old lines 998 and 1012) — never stage them: stage only your own hunks (take `git diff -U3 docs/kernel-language.md`, keep yours, `git apply --cached`). The spec paragraphs S3b changes — kernel-language §2.2's "A PARAMETERIZED sort has the goal face and no value face yet" and S3a's type-variable paragraph after "Not yet: an ABSTRACT T" — are proposed to the user BEFORE editing.

CODE MAP (S3a's sites; paths under rustland/anthill-core/src unless stated):
- stdlib/anthill/reflect/reflect.anthill:189 `sort SortDomain { sort T = ?; rule domain(?x) }` → add `sort Fillable { sort T = ?; rule fill(?x) }` and `SortDomain provides Fillable[T = T]`.
- kb/sort_domain_derive.rs `run` — SortDomain rows PER PARAMETER (HXGXF's shape) behind a demand gate (a requirement names the spec, or a type-variable bound; ~55 ms per load in a debug build when open) → per entity / per field (060 §2.3).
- kb/load.rs:16140 derive_domain_member_clauses (the type-keyed `domain_member` clauses and the `domain_leaf` catch-all); :16835 emit_domain_value_face (`<Sort>.domain`; DECLINED for a parameterised sort); :5789 mint_domain_value_face_name; :16472 expand_rule_head_bound_type_params; :15635 build_sort_ops_table.
- kb/typing/rules.rs:586 install_typed_head_domain_goals — prepends `domain(?x, T)` (conformance) and appends the member goal: `S.domain(?x)` for a named sort, :913 implicit_domain_goals (read + apply_domain) for a type variable, `domain_member(?x, B)` for a parameterised bound; :886 sort_domain_relation (the "<Sort>.domain" name lookup that SortOpsTable rows replace).
- kb/resolve.rs:6759 lower_apply_domain (hands the dictionary to the provider's SortDomain reads via :13420 within_requirements_goal), :6801 builtin_apply_domain, :6821 builtin_domain_leaf, :6555 builtin_type_domain (the conformance goal), :3434 domain_member_goal_is_undetermined, :13493 bind_citation_reads; kb/typing/value_type.rs:2335 pin_bound_from_value.
- kb/typing/rule_requirements.rs:2133 requirement_read_out (with requirement_read_specs / requirement_read_counts): S2's read identity.
- kb/typing/relation.rs:282 domain_value_face_refusal (its parameterised arm goes); settle_citation_routes / citation_requirement_routes (S2's routing).
- kb/mod.rs:638 SortOpsTable (operation rows only — add rows for a spec's RULE members); register_builtin_tag (TypeDomain, DomainLeaf, ApplyDomain).
- eval/eval.rs:710 build_relation_value, :877 citation_requirements (a citation's dictionaries, evaluated in the citing frame and captured on the Relation's root goal).
- domain_member's other readers (the census): typing/relation.rs, typing/value_type.rs, kb/layer.rs, kb/node_occurrence.rs; declared in stdlib kernel.anthill; three test files write its 2-ary spelling.

SUGGESTED INCREMENTS, each driven by its rows with a measured back-out:
 a. The spec and `SortDomain provides Fillable`; SortOpsTable rows for rule members; `fill` resolved at an impl.
 b. SortDomain's `fill` derived per sort — per entity, per field, WI-743's two ordering rules — beside today's clauses; a primitive's `fill` (the waiting type check).
 c. A condition resolved when `fill` READS it, a read WAITING while its type is unpinned (`[]` is a `List[?]`); `SortDomain[?]` never resolved by a provider search (X9PB4's wildcard rule would come back ambiguous).
 d. The sweep: ONE goal per bound, AFTER the body — `SortDomain[T].fill(?x)`. T known at typing: a dictionary built at typing and spliced in (a rule has no citing frame to run a route in; `resolve` + the resolver's `Dictionary::build`). T mentions a variable: the implicit read, routed by S2. The conform step is folded in: it reads the value's type into the bound's variables, which is what ties two columns.
 e. Retire `domain` / `domain_member` / `domain_leaf` (the census above).
 f. The parameterised value face — `List[T = Letter]`'s; its name is 060 §2.3's open question.

MEASURED BASELINE on 861b3013 (fixture: sort Colour { entity red, entity green, entity blue }; sort Wrap[T] { entity wrap(v: T); rule el(?x: T) :- true; rule same(?a: T, ?b: T) :- true; rule dom(?x: Wrap[T = T]) :- true }):
  Wrap.el(red()) 1 definite; Wrap.el(7) NOTHING; Wrap.el([red()]) NOTHING; Wrap.el([1, 2]) undecided; Wrap.el(Option.none()) undecided; Wrap.el([]) undecided — TARGET one definite answer each.
  q(?h) :- Wrap.same([?h], [red()]) NOTHING — TARGET red, green.
  Wrap[T = Colour].dom.takeN(5).length() raises relation_floundered — TARGET 3. List[T = Letter].domain.takeN(5) refused at load, naming 5G28A — TARGET 5.
  KEEP: rule ints(?w: List[T = Int64]) :- true resolved gives [] definite, then cons(head: ?a, …) conditional; ints.takeN(1).length() = 1 and ints.takeN(3) raises; rule skel(?l) :- ?l <=> [?, ?] gives skel.takeN(3).length() = 1, the row [?1, ?2] definite.
  The probes were a scratch test binary, not committed: load with common::load_kb_with, call an operation with common::interp_for, read rows with common::query_unary (the bool is definiteness).

PROCESS: rust tests via rustland/scripts/test.sh; /code-review before a non-doc commit; each test site states which rows its back-out reddens; no attribution in commits; commit only when the user asks.

### 2026-09-25T10:09:54Z — feedback — claude

AFTER THE MERGE 400ae6cd (origin/main pulled 2026-09-25): WI-20260925-P5G39 rewrote `check_provider_requires` (kb/typing/coherence.rs) — the pass S3a measured at +12 ms per load for the SortDomain rows. It now asks the resolver one question per concrete required goal, with the carrier's sort-level requires and ONE clause's conditions as assumptions and the carrier's parameters rigid; the hand-rolled self_provides_required / conditions_entail route is gone. SortDomain's and Fillable's derived CONDITIONAL provisions (conditions per field, step b) go through it: read its route before deriving them, and re-measure the demand gate's cost after it — the ~55 ms figure predates it.

### 2026-09-25T12:11:59Z — feedback — user

STEP 1 IMPLEMENTED, NOT COMMITTED (claude, 2026-09-25; awaiting the user's review of the kernel-language §5.3 text). DECIDED WITH THE USER: every type has a SortDomain — a primitive's fill is the waiting type check (060 §2.3 amended). BUILT: anthill.reflect.Fillable { rule fill(?x) } and SortDomain provides Fillable; each sort's SortDomain entry (fill relation, parameters, per-FIELD conditions, layout offset) derived per entity/per field in kb/fill_derive.rs with a fillability greatest fixpoint and a conditions least fixpoint, WI-743's two orders; primitives' fill; (S, fill) rows in the operation table; apply_domain reads a dictionary or a TYPE (built one level deep, conditions pending until read); the typed head is ONE goal after the body (apply_domain(?d, ?x, B) conforms with an OPEN pin, then fills), conformance alone for a type with no domain; a SortDomain read filled by a caller is trusted, routed at a citation from the TYPE (typing::sort_domain_route); domain_member / domain_leaf / the dispatch guard retired. FINDING: the typer lays a SortDomain dictionary out with the Fillable conversion FIRST, so derived fills read conditions at an offset (SortDomainEntry::sub_offset, checked against dict_layout once rows exist). GATE: rows cost ~115 ms/load debug when always derived; now derived only for a WRITTEN SortDomain/Fillable requirement (citations no longer need them). ROWS: the six Wrap.el rows definite, q = red/green/blue, Wrap[T = Colour].dom = 3, List[T = Letter].domain = 5, rigid 3/2, 5G28A pins hold; classic-mini unchanged. MOVED BY DESIGN: anylist(?w: List) answers [] definite then undecided skeletons (nil reads no condition) — the acceptance line said 'no definite row'; Bool/String have a domain (waiting check). Six back-out axes measured (wi_shed7_fillable_test header). Full workspace 7624 passed / 0 failed; scaland testFull 578 + 35 + 1 passed. /code-review high: 7 findings, 4 fixed, 3 skipped (non-Term placeholder opening; interning 'fill'; one shared requirement walk for the TypeValue and SortDomain gates). OPEN: steps 2 (067 §5 q3, the monoid's home) and 3 (MiniSat over a builder, q1/q2).

### 2026-09-25T16:35:18Z — feedback — user

FOR THE REWORK (code review, 2026-09-25): THE TYPED-HEAD PIN PATH GROWS THE HASH-CONSED TERM STORE PER RESOLUTION STEP. `value_type_open` opens a value's partly known type (`[]` is a `List[?]`) by minting a FRESH variable per call, and the pinned bound is then walked (`walk_type_deep_value`) into an interned term holding it — a fresh variable never deduplicates, so every answer of `rule typed(?w: List) :- ?w <=> []` interns 2 terms its untyped twin does not (MEASURED: 4 vs 2 per query). Making `open_term_placeholders` transient alone changed nothing (the downstream walk interns the same), so it was reverted; the fix is a transient pin path end to end (WI-20260905-N20EZ's class), which belongs to this ticket's rework of the typed head. ALSO FOR THE REWORK: kernel-language.md (§5.3 and the rule-body dictionary text) is out of sync with SHED7 step 1 and P7VP4 — the spec draft waits for the reworked design and the user's review.

### 2026-09-25T20:29:50Z — feedback — user

CODE-REVIEW ROUND 2, SHED7's side (2026-09-25, not committed). A typed head's FILLABLE bound gets an EARLY guard in front of its body — `domain(?x, B, early: true)`: it decides a value already bound and STANDS ASIDE otherwise, so a generating call is what it was. With the fill appended alone a body FAULTED on a wrong carrier before any test (`add(2.5, 1, ?y)` under `?x: Int64` — a fault, not a refutation), a cut committed first, and a long body ran for nothing; it replaces round 1's cut-only prepend. A condition's type left UNWRITTEN or unpinned is read off a bound value (`DomainEvidence::Unpinned`; `holder(p: pr(a: 1, b: 2))` floundered). An ALIAS has its target's domain (`typing::dealias_type`, at the derivation, the typed head, the resolver and the citation route; `circle(r: Radius)` declined `Shape`, and stdlib `ProcessResult` lost its domain through `sort Path = String`). A condition is the parameter the sort DECLARES for it, not its index among the sort's type parameters (a WI-452 marked parameter shifted it). The `(S, fill) ↦ S.domain` OPERATION-TABLE rows are gone: `fill` is found through the SortDomain entry, a map of the rule member's own — the rows listed a relation in `Dictionary.ops` and shadowed a later load phase's `fill` operation (proposal 067 §3 and 060-implementation's table updated). A no-domain type's conformance has a REFUTING control (`tieBad`). Stale back-out records corrected: wi743's historical names, wi_5g28a's axis B (three pin sites now — early guard, fill conform, `Unpinned` read; all three together redden 10 rows) and [S], SHED7's [P] (0 red since the early guard). Rows +6 in wi_shed7. Full workspace 7655 passed, 0 failed.

