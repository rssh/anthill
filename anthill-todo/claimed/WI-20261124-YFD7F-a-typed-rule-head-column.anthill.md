## Attributes

- id: WI-20261124-YFD7F-a-typed-rule-head-column
- created: 2026-11-24T10:02:24Z

- status: Claimed
- status_agent: claude
- status_at: 2026-11-27T11:05:00Z

- acceptance: cargo-test

## Description

A typed rule-head column checks its whole value again at every call: a recursive rule over a typed List costs more than O(n^2)
WHO NEEDS IT. Every rule whose head types a column with a recursive sort (List, a tree) and recurses on a part of it: membership, lookup and walk rules over a cons spine, which is how anthill-traces' specifications hold their entities (WI-20261122-96QKW measured such a membership rule). Found while drafting proposal 076 (docs/proposals/076-goal-scope-in-the-search.md §7); the user asked whether the sort domain generates where it should check.

WHAT IS THERE TODAY (read from the code on 2026-11-24). install_typed_head_domain_goals (kb/typing/rules.rs) gives a clause with a head bound ?x: T two goals: __domain_guard(?x, T) IN FRONT of the written body (WI-742's conformance check, which waits on an unbound or partly bound ?x), and domain(?x, T), the fill, APPENDED after it (WI-743: a generator ahead of the body enumerates a recursive type forever). At the resolver, domain(?x, T) is apply_domain, and with ?x ground lower_apply_domain (kb/resolve.rs) turns it into the provider's fill(?x) goal, proved by the domain's clauses one constructor at a time, so a ground value is CHECKED, not generated, by walking all of it. Both goals run at EVERY call of the rule, including the rule's own recursive call on a part of a value the clause has already checked: in mem(?x, ?t) below, ?t is the tail: Self of a List[T = Int64]. And because the fill comes after the body, it is still pending when the recursive call opens the next level, so each level leaves one more fill in the resolvent, which proposal 076 measured as quadratic on its own.

MEASURED 2026-11-24 (debug build at or near 5e721bf5e; anthill query --max-depth 100000; wall time, peak RSS). Membership of the LAST element of a ground list [1, ..., n]:
  rule mem(?x: Int64, ?l: List[T = Int64]) :- (?l <=> cons(head: ?x, tail: ?)) | (?l <=> cons(head: ?, tail: ?t), mem(?x, ?t))
  n                        100              200              400
  ?l: List[T = Int64]      0.75 s / 241 MB  2.46 s / 1.1 GB  20.0 s / 7.6 GB
  ?l untyped               0.51 s / 85 MB   0.55 s / 99 MB   0.73 s / 145 MB
Time grows about eightfold per doubling. The split between the guard, the fill and the pending resolvent is not measured: no step counts were taken.

WHAT IS ASKED. A typed column whose value is already known to conform is not checked again, so the typed mem costs within a small factor of the untyped one. The approach is open; to choose before implementing:
  (a) Discharge statically: where the typer knows the argument conforms (a part of a checked value, a typed variable, a typed column of the caller), the call does not run the callee's guard and fill: the clause gets a checked entry and an unchecked body.
  (b) Remember per search the ground values that passed the fill at a type, keyed by the hash-consed term, so a tail already walked as part of its list is not walked again.
  (c) With ?x ground at the call, run the fill at the guard's place and not after the body, so no fill is pending across the recursive call. That removes the growing resolvent but still walks each tail once per level, O(n^2).
Note why the fill is not redundant beside the guard on a ground value: the guard's closed reading cannot tell [[]] from [] against List[T = Int64], and the fill refuses the first (install_typed_head_domain_goals' doc). Whatever is chosen keeps that refusal.

WHAT IS NOT ASKED. Changing what a typed column admits or refuses, or when a column with an unbound value generates. The 2^k of ground goals with several proofs (WI-20261122-P6G1P, WI-20261122-VT9S7, proposal 076): separate, though each replayed branch re-runs its checks.

DONE WHEN. A test: the typed mem above on a ground list of 400 runs in steps within a small factor of the untyped one (count steps, not time), and at 100 and 200 the steps grow linearly with n; the control is the same test before the change, where they do not. The refusals still hold: [[]] against List[T = Int64] is refused, a value of the wrong type is refused before the body runs (WI-742's rows), and WI-743's word(?w: List[T = Letter]) :- ?w <=> [?, ?, ?] still answers 27 and stops.

## Changes

### 2026-11-24T10:35:11Z — feedback — user

APPROACH PROPOSED, agreed with the user 2026-11-24 (not implemented; the typer's part below is not yet checked against the code).

(a) THROUGH THE DICTIONARY CHANNEL, not through two versions of a clause. The user: 'during call we pass dictionaries, so we can look on untyped as on translated typed'. Every call is elaborated and carries its dictionaries, so there is no untyped caller: an untyped rule is a typed one whose column types are variables, and the caller always has a place to say what it knows about each argument. The hidden parameter of a typed column gets TWO STATES, one value of two variants:
  - check with d: the caller does not know the argument conforms. The callee tests a bound value and generates for an unbound one, as today.
  - trusted, d for generation only: the typer has the column's type for the argument at that occurrence. The callee tests nothing, and uses d only when the value is not ground.
'Trusted' with no dictionary is not representable, so generation (WI-743's word(?w) answering 27) cannot be lost. A dictionary says the TYPE has a domain; it is not evidence that this VALUE is in it, which is why the second state is needed and the dictionary alone is not enough.
In mem: ?l is typed by the head, ?t is the tail of a List[T = Int64], so the recursive call passes 'trusted' and the list is walked once, at the first call. A type mentioning a variable (apply_domain(?d, ?x, B)) reads nothing from the value when the call site instantiates B's variables and passes ?d; the citation route becomes the only route. What is still walked, once: a value from outside any elaboration (a CLI or execute query argument, a host-decoded value).

TWO CAUTIONS. A type is per occurrence (WI-20261124-C6VN0: two branches of | may each type a variable), so a use in one branch does not make the other trusted. And 'trusted' rests on TYPE PRESERVATION: every binding of a variable the typer has at T is a T. Whether the typer establishes that for rule bodies is TO BE CHECKED FIRST; the approach depends on it.

FALLBACK WHERE NO TYPER ELABORATES (scaland; a value from outside): option (b), a per-search memo of ground values that passed the fill at a type, keyed by hash-consed term and type. The fill's own walk of a list visits every tail, so one walk records them all and each later call on a tail is one lookup. Not covered: values that are not hash-consed terms (occurrences, entities).

WITH EITHER: 'nothing to generate' decided in O(1) by a ground bit set when a term is hash-consed; walking the value to learn it is ground is O(n) a level again.

Option (c) (the fill at the guard's place when the value is ground at the call) removes the pending fill by itself. MEASURED 2026-11-24 (proposal 076, MEASURED): the pending fill is what makes a typed recursion's memory quadratic. cnt(?n: Int64) 208 / 537 MB at n = 1000 / 2000 against 107 MB untyped at 2000; the control chain(?n: Int64) 498 MB / 1.63 GB against 123 / 145 MB untyped. Proposal 076 Stage A (a linked continuation) makes a pending fill O(1) to carry without it.

STILL NOT MEASURED: how the typed cost splits between the guard, the fill and the pending resolvent. It decides whether the memo alone brings typed mem within the small factor DONE WHEN asks for, or the guard needs it too. Take step counts before choosing between (b) alone and (a).

### 2026-11-27T11:31:16Z — feedback — claude

REVIEW BEFORE BUILDING (claude, 2026-11-27, session with user). MEASURED on HEAD 2fe680bc5 and on the ticket's own tree 5e721bf5e, debug CLI, anthill query --max-depth 100000 --max-results 1, wall time and peak RSS (the stdlib load alone is 3.6 s / 97 MB). Probes in a scratch directory, deleted after.

1. THE UNTYPED BASELINE ABOVE DOES NOT REPRODUCE, ON EITHER TREE. The ticket's untyped mem, written as above: n = 100 / 200 / 400 = 4.9 s / 220 MB, 11.1 s / 872 MB, 62.5 s / 5.5 GB on HEAD; at 5e721bf5e, n = 200 = 11.35 s / 865 MB (built in a worktree for this). The ticket records 0.51 / 0.55 / 0.73 s and 85 / 99 / 145 MB. So the 27x gap is not there: typed is 5.0 s / 257 MB, 11.9 s / 1.16 GB, 68.7 s / 7.7 GB, about 10% time and 40% memory over untyped. Not a regression since the ticket (both trees agree); what the ticket's untyped row measured is not known.

2. WHAT IS SLOW IS A LIST TAIL BOUND TO A BODY VARIABLE, typed or not. n = 200: rule lenOk(nil()) :- true / rule lenOk(?l) :- ?l <=> cons(head: ?, tail: ?t), lenOk(?t) = 11.06 s / 869 MB. The same walk destructured in the HEAD, rule lenH(cons(head: ?, tail: ?t)) :- lenH(?t) = 3.79 s / 102 MB (the load). Through a head-matching helper, split(?l, ?, ?t), lenS(?t) = 11.36 s / 873 MB (slow: ?t is still a body variable bound to the tail). A body <=> that FAILS at each level = 4.12 s / 102 MB. An integer recursion binding a body variable each level, ?m <=> ?n - 1, cntB(?m) = 3.72 s / 101 MB at n = 800. Not the |, not the query literal (the list written in the program costs the same), not the type. Memory grows about n^2.6. Cause NOT identified; read as a lead only: the bound tail is copied per binding and every retained frame keeps its copy (proposal 076 §8 names Substitution::bind_compressed as unmeasured).

3. STEPS DO NOT SEE THE TYPED CHECK. The fewest --max-steps that answer, untyped / typed / typed list column only: n = 25: 1997 / 2097 / 1997; n = 50: 7122 / 7322 / 7122. The list column's check costs no counted steps (its walk is inside steps that count one), so DONE WHEN's 'count steps, not time' cannot measure it. Separately, the untyped count is itself super-linear (3.6x per doubling).

4. TYPE PRESERVATION, the precondition of approach (a), DOES NOT HOLD. Load clean: rule p(?l: List[T = Int64]) :- ?l <=> cons(head: ?, tail: ?t), ?t <=> "x"; and ((?l <=> cons(head: ?, tail: ?m)) | (?m <=> "x")), memL(1, ?m) with memL's list column. Refused, correctly: passing ?t to a rule whose inferred column is String. Today these answer correctly because the callee checks; under 'trusted' a call p(cons(head: 1, tail: ?)) would bind the tail to "x" and skip the check. So (a) needs a <=> at a mistyped value refused at load first; (b) and (c) do not depend on it.

CONSEQUENCE FOR THIS TICKET: its measured problem is dominated by item 2, which is not about types. Re-measure the typed overhead once a list walk is linear; until then the choice between (a), (b) and (c) has no number to rest on.

### 2026-11-27T11:38:03Z — feedback — claude

CORRECTION to the entry above (claude, 2026-11-27, the same session): its items 1, 2 and 3 are WRONG and are withdrawn; item 4 (type preservation) stands. The user pointed out the ticket was measured on another machine; re-measured with an optimized CLI (cargo build --release) on this one.

THE TICKET'S NUMBERS REPRODUCE. Its untyped row is mem(?x: Int64, ?l) — ?l alone unannotated: n = 100 / 200 / 400 = 0.46 s / 82 MB, 0.50 s / 95 MB, 0.67 s / 141 MB (ticket: 0.51 / 85, 0.55 / 99, 0.73 / 145). Its typed row: 0.70 s / 239 MB, 2.24 s / 1.14 GB, 18.55 s / 7.67 GB (ticket: 0.75 / 241, 2.46 / 1.1 GB, 20.0 / 7.6 GB). Same tree behaviour on HEAD 2fe680bc5.

WHY THE ENTRY ABOVE WENT WRONG: its 'untyped' rules were not untyped. The clauses as stored (TermPrinter::print_rule, a temporary test):
  memU(?x, ?l) [nothing written] :- __domain_guard(?l, List[T = ?e]), <body>, apply_domain(?d, ?l, List[T = ?e]), find_dictionary(SortDomain, SortDomain, ?l, out: ?d)
  memX(?x: Int64, ?l)           :- __domain_guard(?x, Int64), <body>, apply_domain(Int64, ?x)          -- NO list check
  memT(?x: Int64, ?l: List[T = Int64]) :- both guards, <body>, apply_domain(Int64, ?x), apply_domain(List[T = Int64], ?l)
An unannotated column gets its INFERRED type as a bound (install_inferred_column_bounds, the user's 2026-10-21 rule), and so the check — but only where that type mentions a variable (List[T = ?e]); where it is concrete (List[T = Int64], from ?x: Int64) it gets none. So every 'list walk' probe above that was slow had an inferred check, and the ones that were fast had none (a head-pattern column, an Int64 column, a clause that failed before its appended fill).

STEPS DO SEE THE CHECK: the fewest --max-steps that answer, n = 25 / 50 / 100: unchecked memX 396 / 796 / 1596 (linear, 16 a cell); written memT 2097 / 7322 / 27147; inferred memU 1997 / 7122 / 26747 (quadratic). The entry above compared a check against a check. DONE WHEN's step count stands.

WHAT THIS ADDS TO THE TICKET: the cost reaches UNANNOTATED list rules too, whenever the element type is left open — the common way a list walk is written — while annotating the element (?x: Int64) removes the list check entirely. An approach must cover the inferred bound as well as the written one.

### 2026-11-27T12:14:23Z — feedback — claude

DESIGN PROPOSED FOR REVIEW — approach (a), the trusted dictionary (claude, 2026-11-27, session with the user; the user chose (a) as the more principled). NOTHING BUILT. Measurements it rests on: the correction entry above.

0. THE PRINCIPLE (from the user's question 'why is it runtime?'). Only two things belong at run time: GENERATING an unbound value, and checking a value ONCE where it crosses into the typed world (a query argument, a fact asserted while running, a host-decoded value). Inside a typed program, with type preservation, a call between typed rules is already known to conform, and a check there changes no answer. The per-call check exists because a call carries nothing of what the typer knows.

1. REPRESENTATION. A plain dictionary, Dictionary(sub0 .. subN, impl: S), keeps meaning CHECK, so every dictionary built today stays valid. ONE new kernel value, __trusted(d): the same instance plus one fact about the call — the caller has established that this argument conforms. A dictionary describes the TYPE's instance and says nothing about a value (the 2026-11-24 entry), which is why the fact is a wrapper and not a field. Nothing about the value is stored: no type, no copy.

2. WHERE IT LIVES. Written by the typer at each call site; carried by the existing marker, __within_requirements(goal, relation, dictionaries), as citations and apply_domain carry theirs; bound in sigma when the callee's clause opens, to the column's read variable (resolve::bind_citation_reads, merged.bind_waking(?d, ...)). A call that routes nothing reads as CHECK, as an unrouted read does today.

3. WHAT THE CALLEE DOES WITH IT. __trusted means 'conforms, AND its generation is owned upstream' (the user's question: why walk an unground value?). The column's guard and fill then do NOTHING: no walk, no ground test. Generation is not lost: the value is a part of one the caller owns — mem's ?t is the tail of the caller's ?l — and the caller's own appended fill fills every hole of it, the callee's included; fills are appended after the body already, so moving one later only leaves more goals to prune first. A plain d: check and generate as today.

4. EVERY TYPED COLUMN GETS A READ. Today a GROUND bound has none: apply_domain(List[T = Int64], ?l) hands the TYPE to run time (a departure from 'no type values at run time'). The typer builds that column's dictionary at load from the table (typing::sort_domain_route already builds such terms for a citation) and uses it where no caller passes one. INFERRED bounds (install_inferred_column_bounds — memU's List[T = ?e]) are columns like any other.

5. THE EVIDENCE RULE — the one rule the design adds. A call passes __trusted only for an argument that is (part of) a value something upstream has ESTABLISHED: a typed column of the caller, whose own check and fill cover it (a part destructured from it included); a typed operation parameter (v: X); a value the clause built from constructors. And only where that established type matches the callee's bound, instantiated at the call (T := X from Wrap[T = X], A := Int64 from cmp[A = Int64]), up to the SAME variables — the same rigid, the same rule-scoped variable. Never trust made by unifying at the call (?u := Int64 against a column List[T = Int64] is an assumption, not evidence). Anything else passes the plain d.

6. RULES PARAMETERISED BY TYPES. Their columns already have a read the caller routes (the bracket; a rigid's requires slot); the caller wraps what it routes. Skipping the column's conform (apply_domain(?d, ?x, B) reads ?x's type into B's variables — what ties rule same(?a: T, ?b: T)) is safe: the caller proved the tie at its instantiation, and a body requirement at T comes through the dictionary channel (060.1), not off the value. A call that routes nothing conforms as today.

7. GENERATION IS UNAFFECTED. A caller that wants values — Wrap[T = X].el.takeN(9), ?x unbound — owns nothing and passes the plain d; the callee generates through it.

8. PRECONDITION — close the type-preservation gap at LOAD first. MEASURED 2026-11-27, refused today, correctly: ?l <=> "x" and ?l <=> 5 at ?l: List[T = Int64]; a mistyped head element (?h <=> "x" gives List[T = String]); passing the tail to a String column. LOADS CLEAN, must be refused: rule p(?l: List[T = Int64]) :- ?l <=> cons(head: ?, tail: ?t), ?t <=> "x" — the typer knows ?t: List[T = Int64] (the String-column call is refused) but never compares it with ?t's own <=>; and the same through a | branch (?m <=> "x") followed by a list use. Until refused, __trusted could skip a check that is needed: p(cons(head: 1, tail: ?)) would bind the tail to "x" unchecked.

9. WHAT IT DOES NOT NEED. No second version of a clause (rejected 2026-11-24 for the dictionary channel); no type on a value (the reverted Value::ty, constrained-term-substrate.md); no memo — (b) stays the fallback where no typer elaborates (scaland, a value from outside).

10. STAGES, each measured on its own: S0 the preservation gap refused at load (its rows: the two shapes above refused, the four already refused kept); S1 every typed column gets a read, a ground bound's dictionary built at load, no answer moves; S2 the evidence rule and __trusted at call sites; S3 the callee's guard and fill skip on __trusted.

11. ACCEPTANCE, from DONE WHEN with this session's numbers (fewest --max-steps that answer, membership of the last element): typed mem at n = 25 / 50 / 100 is 2097 / 7322 / 27147 today, the unchecked mem(?x: Int64, ?l) 396 / 796 / 1596; after S3 the typed one and the all-unannotated one (1997 / 7122 / 26747 today) within a small factor of the unchecked, linear at 100 / 200 / 400. CONTROLS: the same rows before the change; the refusal of [[]] against List[T = Int64] kept; generation kept — WI-743's word(?w) answering 27, tiny-sat's 2 models, wi_09e6m's 1, 1, 2, 5, 14 trees; a query argument still checked once.

12. OPEN FOR REVIEW: (i) the concrete-inferred rule — a column whose inferred type is concrete gets NO check today (mem(?x: Int64, ?l)'s ?l); under this design it could get a read like any column, so a value from a query is checked once at entry — keep the exemption, or drop it? (ii) the marker on every rule-body call to a rule with a typed column: O(1) a call; acceptable? (iii) proposal 076 Stage B (a waiting fill kept in its scope) and 077 (where a dictionary comes from) touch the same goals; neither blocks this.

### 2026-11-27T12:19:43Z — feedback — claude

OPEN QUESTION (i) OF THE DESIGN ABOVE, MEASURED — now a recommendation (claude, 2026-11-27; the user asked what the exemption is). THE EXEMPTION: install_inferred_column_bounds gives an unannotated column its inferred type as a bound, and the check with it, EXCEPT where that type is concrete; its doc's reason: 'a concrete type the clause gives holds for every value it makes, so a check there would change no answer'. MEASURED (release CLI), the query firstR(5, cons(head: 5, tail: "junk")) with cons imported:
  rule firstX(?x: Int64, ?l) :- ?l <=> cons(head: ?x, tail: ?)                  -- ?l inferred List[T = Int64], exempt: 1 solution
  rule firstT(?x: Int64, ?l: List[T = Int64]) :- ?l <=> cons(head: ?x, tail: ?) -- written: no solutions
  rule firstU(?x, ?l) :- ?l <=> cons(head: ?x, tail: ?)                         -- inferred List[T = ?e], checked: no solutions
and all three answer the well-typed cons(head: 5, tail: [7]). So the exemption DOES change an answer: for a value from OUTSIDE the typed program (here a query argument). From inside it cannot: building that value in a rule is refused at load (cons.tail expects List[T = Int64], got String). That is exactly the boundary of point 0. RECOMMENDED under (a): drop the exemption — a concrete inferred column gets its read like any other; a value from outside is checked once where it enters, and a call inside passes __trusted, so nothing inside gets slower. firstX then refuses the junk list as firstT and firstU do. This is a change of answer (a query that answered 1 answers none), so it is the user's to confirm.

### 2026-11-27T12:22:04Z — feedback — claude

DECIDED (user, 2026-11-27): the concrete-inferred EXEMPTION IS REMOVED with (a). A column whose inferred type is concrete gets its read and check like any other typed column; a value from outside is checked once where it enters, a call inside passes __trusted. The row that moves: firstX(5, cons(head: 5, tail: "junk")) answers no solutions, as firstT and firstU do; its control, the well-typed cons(head: 5, tail: [7]), keeps 1 for all three. Remaining review items of the design: (ii) the O(1) marker on every rule-body call to a rule with a typed column; (iii) proposals 076 and 077 touch the same goals and block nothing.

### 2026-11-27T13:24:32Z — feedback — claude

S0 BUILT (claude, 2026-11-27, session with the user; not yet committed): the type-preservation gap closed at load. The sides of a committed <=>, === or !== goal of a relational clause are held to one type, as ='s and !='s are by their parameters.

WHAT. rule_constraints::settle_equality_sides: the walk sets each such goal aside (LatePosition::EqualitySides) and its two sides are compared after every other position of the clause, by unification on a copy or conformance either way; a mismatch is OperationArgument on unify / struct_eq / struct_neq, at the second side ("type mismatch in unify.b (op-arg): expected List[T = Int64], got String"). Not compared: a side the clause leaves untyped or types Term; a goal in a | branch, a negation or a quantifier (and a side whose variable one of those types too — ClauseConstraints::uncommitted_vars, since the walk records a branch's positions in the clause's one map); an equation's or a guarded law's guard; a query's goals. WRITTEN FIRST (?t <=> "x", ?l <=> cons(head: ?, tail: ?t)): the literal's placeholder reached ?t before the list field's, and the field's was dropped; constrain_vid now records such a clash of two placeholders (ClauseConstraints::placeholder_clashes, committed positions only), and the check reads it for any variable side.

WHY THE CHECK WAS MISSING: = and != are spec operations, which the call check types; <=>, === and !== are resolver builtins, which call_dispatch_shape skips, so their sides met at one placeholder T, a disagreement there was 'the call's fault' (constrain_vid), and no call check ran.

ROWS: tests/include/wi_yfd7f_unify_side_types_test.rs, 10, written failing first. BACK-OUTS, each RUN: [C] no mismatch reported -> the six *_is_refused rows; [P] the clash not recorded -> the two *_written_first rows; [U] a branch-typed side compared -> the branch row (refused 'expected List[T = Int64], got Int64', a clause that answers). Passing under all three by design: the =/!= refusals, the well-typed controls, the | row.

FIXTURES REWRITTEN, with the user (each wrote the ill-typed value in the clause as a run-time negative control, refused at load now as = refuses the same shape; each now takes the value from the QUERY and tests what it tested): wi523 unify_occurs_check_fails (?v <=> some(?v): the rule refused, the occurs check driven from a query); wi_wt8wg ×3 (?y <=> red(), domain(?y, Int64) and ?x <=> [a()], domain(?x, Int64)); wi_shed7 a_type_with_no_domain_is_checked_not_refused (tieBad's element handed in through ?v, still bound after tie pins its type). Two messages kept as they were (wi742's rule-bound, shed7's rule-column).

SPEC: kernel-language.md §5.3, a paragraph after 'A call written in a rule body…', text agreed with the user.

/code-review (high): 6 findings; 2 real bugs of this change fixed with rows (the branch clash; the var-vs-var written-first gap); skipped, minor: a possible double report beside a call check (not observed), two state copies per <=> at load (not measured), the infinite-type message reading less clearly than ='s, the claimed ticket file to be added at commit.

GATE (scripts/test.sh, full): 12970 passed, 0 failed, 26 ignored. Families: green. Scaland: no typer, nothing to port. NEXT: S1 (every typed column gets a read; a ground bound's dictionary built at load).

### 2026-11-27T15:14:21Z — feedback — user

S1-S3 BUILT (claude, 2026-11-27, session with the user; not yet committed). S4 MEASURED AND SET APART (user's decision).

S1 - every fillable typed column gets the SortDomain read a caller routes to: a GROUND bound too (frame var ?d, find_dictionary read, fill apply_domain(?d, ?x, D)), D its dictionary built at load (typing::ground_domain_dictionary, from sort_domain_route); no type is handed to the run time to fill. No answer moved (anthill-core green), steps identical to HEAD.

S2 - the evidence rule (typing/trusted_columns.rs), at route_goal: a rule-body goal hands a typed column's read __trusted(d) (resolve::TRUSTED_READ) where the caller ESTABLISHED the argument at the column's bound: a typed column of the caller that has a fill; a part of one destructured by a <=> on the conjunction path to the goal (the branch of | it is in; never under not / a quantifier), at its field's type (instances::field_type_at); a literal. The type is the CHECK's (the stored bound and its fields), never the goal's typer stamp. Match: callee bound ground and established ground and compatible; a bound with a variable only in the clause's own recursion at the same variables. A clause holding a cut trusts nothing (the cut would commit past cells the callee's fill no longer fills first). Not covered, each keeps its check: a citation from an operation body (operation parameters), a construction with a variable, a column with no fill.
S3 - the open (resolve::bind_citation_reads -> ReadRoute::Trusted) binds ?d to the unwrapped d and drops that column's guard and fill (typed_column_goal_positions, read off the stored body).

MEASURED (release CLI, fewest --max-steps that answer, n = 100 / 200 / 400): memT 1704 / 3404 / 6804 (was 27147 at 100); memU 1700 / 3400 / 6800; memX 1200 / 2400 / 4800. memT at 400: 0.76 s / 139 MB (was 18.55 s / 7.67 GB). Linear; within 1.1 of the unchecked memX's 1596 at n = 100 before.

ROWS: tests/include/wi_yfd7f_trusted_columns_test.rs, 11. BACK-OUTS, each RUN: [T] no trusted slot / [D] no drop -> the two linearity rows; [S] evidence from the typer stamp -> 3 rows (strs(["a"]) answers; the other-branch row; memU); [C] cut ignored -> the cut row (4 answers for 1); [P] every <=> of the body on the path -> the other-branch row. Controls by design: generation through a trusted call (outerPair 4), a query argument checked where it enters, [[]] refused, a branch binding a part to another type refuted by the root's waiting guard, a ground bound's dictionary in every spelling.

S4 (the concrete-inferred exemption removed) MEASURED: such a column GENERATES too, not just checks - 33 rows in 19 files move (q(?a, ?b) :- eq(append(?a, [3]), append(?b, [4])) enumerates 2933 list skeletons where it suspended once; conditional answers turn definite; reflected rows lost) and anthill-core goes from ~260 s to 1231 s. It changes when an unbound column generates, which this ticket's WHAT IS NOT ASKED excludes. User, 2026-11-27: ship S1-S3, decide S4 (check-only vs. generating at an inferred concrete column) apart; reverted, firstX keeps answering the junk list.

SPEC: kernel-language.md s5.3, 'A typed column is checked where its value enters the typed program, not again inside it', text agreed with the user.

/code-review (high): 7 findings. 2 important, both no_change_needed after measurement: a branch-local fact binding a trusted part to Float is refuted by the root column's waiting guard before the trusted callee runs (row added); the ground-dictionary panic is unreachable - the loader writes every parameter of a head's bound and condition_arg reads a default (row added over five spellings). Fixed: stored/opened body alignment is an assert; a trusted slot carries the goal's bracket dictionary; pattern fields named first. Skipped: load time not measured; operation-body citations not covered (recorded here).

### 2026-11-27T15:22:09Z — feedback — user

GATE (scripts/test.sh, full) after the review fixes: 12981 passed, 0 failed, 26 ignored (36 binaries). Families: green. Scaland: no typer, nothing to port. DONE WHEN met for S1-S3 (typed mem linear in steps, within 1.1 of the old unchecked one; [[]] refused; WI-742's guard rows and WI-743's 27 unchanged). OPEN: S4, to be decided apart; operation-body citations as evidence; load time of S1/S2 not measured.

