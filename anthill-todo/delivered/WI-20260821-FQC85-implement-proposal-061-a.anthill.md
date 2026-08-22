## Attributes

- id: WI-20260821-FQC85-implement-proposal-061-a
- created: 2026-08-21T14:23:09Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-22T00:07:02Z

- acceptance: cargo-test, scaland-sbt-test

## Description

IMPLEMENT PROPOSAL 061 — a logical rule's head names a DECLARED predicate.

A predicate is the only name in the language with no declaration: four core constructs,
and only `rule` brings a name into existence as a side effect of using it. That is the
whole of WI-980 — the head's name is created during the pass that decides it, so WHEN the
ladder is asked was load-bearing. Every other name kind is immune because pass 1 defines
all of them first (WI-321).

THE RULE (061): a rule head is always a clause OF something. A predicate whose heads are
all in ONE file is auto-declared, in the scope §WI-896's ladder already picks; one with
heads in MORE THAN ONE file must be declared explicitly, or the load is refused naming the
files. The file is the unit for 059 §Definitions' own reason -- it is the smallest place
where "two parties" is real, and it is the unit `import` already uses.

CENSUS, MEASURED over stdlib + anthill-stl + examples/github-todo: 102 predicates carry
rule heads and EVERY ONE has its heads in exactly one file; zero span more than one. So
the multi-file requirement refuses nothing that exists, and the 43 distinct
rule-introduced names are all auto-declared.

WHAT IT REMOVES from the loader, all of it cross-FILE and therefore exactly on the
auto-declaration boundary (each measured under WI-980):
 * a sibling file's head MOVED another file's clause -- `zlib.q` 2->1 and `zdemo.q` 0->2,
   with the first file unedited;
 * a mutual-import cycle picked its owner by FILE ORDER;
 * the same pair at one address, split across files, gave two different programs;
 * ownership had to be keyed per `(scope, name, FILE)` because two heads of one predicate
   can sit in files with different imports (WI-995).
What remains is the single-file case, decided by §WI-896's ladder as today.

EQUATIONAL RULES ARE OUT OF SCOPE. `lhs <=> rhs` extends UNIFICATION; its clauses index
under the connective, not under its subject (WI-898), so the subject owns no clauses and
there is no predicate to declare. The two shapes already earn different symbol kinds for
that reason. `[simp]`'s enablement is untouched.

DECIDE BEFORE IMPLEMENTING -- 061 lists five, and the first is on the critical path:
 1. SPELLING. A body-less head is today an ordinary FACT (`rule parent("alice","bob")`),
    so a declaration must be distinguishable from a ground fact whose arguments happen to
    be variables -- `rule p(?x, ?x)` is a legitimate clause. All-variable form, a keyword,
    or an arity-only form.
 2. Does the declaration fix ARITY? Clauses may differ in arity today.
 3. A single-file mutual cycle is auto-declared with no outermost scope to pick, so
    WI-980's cycle handling survives for it. State it; do not assume it away.
 4. A declaration must NOT join the dispatch surface (059: the surface is exactly the
    operations), while 052 OQ2 wants `Sort.rule` citable as a `Relation[T]` -- the two
    proposals must agree on what a declaration makes citable.
 5. The multi-file rule is a WHOLE-PROGRAM property: adding a second file can require a
    declaration elsewhere. Same discomfort 059 records for secondary entries; record it.

ACCEPTANCE: drive it. The four cross-file shapes above must each be a located load error
naming the files, or load with the declaration present and the clauses on ONE predicate --
assert the clause counts and the answers, not that it loads. Single-file shapes keep
today's behaviour (control: WI-980's own suite stays green). An equational head is
untouched in both spellings (control). Say at each site which rows fail on a back-out.
cargo-test green via rustland/scripts/test.sh.

## Changes

### 2026-08-22T00:06:52Z — feedback — user

DELIVERED (rustland). Proposal 061 is implemented and marked DELIVERED; scaland is green
and unported (SBZ2A amended to carry both rules).

THE FIVE DECISIONS THE TICKET ASKED FOR, taken before implementing:
 1. SPELLING — 061 had already settled it: a rule with no body. The split point is the
    SYNTACTIC absence of a body (`body: None`), told from an equation by the head's
    functor through the reader the loader already ran (`parse_connective_head` +
    `is_minted`). One decider, `rule_reading`, shared by pass 1's mint and the load.
 2. ARITY — A DECLARATION DOES NOT FIX IT. It writes its head's arity and enforces
    nothing; clauses of differing arity load exactly as today. One-arity-per-predicate
    stays WI-20260821-6WVJB, which depends on the user's open operation-side question
    WI-20260821-ZW940 — settling it here would have pre-empted both. Stated in
    kernel-language.md §5.3 and at the site.
 3. THE SINGLE-FILE MUTUAL CYCLE is auto-declared, and WI-980's cycle handling survives
    for it — and for every cross-file cycle whose members each keep their own predicate,
    since each predicate is then written in one file. What the file rule removes is a
    cycle member ABSORBING another file's clause. §8.6; driven both ways in
    `a_cycle_can_no_longer_absorb_a_third_files_clause`.
 4. THE DISPATCH SURFACE — a declaration mints `SymbolKind::Goal`, exactly what a rule
    head mints today: no signature, no return type, never an operation, so it does not
    join the surface (059). 052 OQ2's `Relation[T]` citability stays derived at the
    reader from the clause index. §8.6.
 5. THE WHOLE-PROGRAM DISCOMFORT is recorded in §8.6, next to 059's own.

WHAT SHIPPED (kb/load.rs):
 * `RuleReading` — no body ⇒ DECLARES, a body ⇒ asserts — asked by `scan_rule` (pass 1,
   which now mints the declared predicate like every other name, WI-321) and by
   `load_rule`, so the name pass 1 mints and the clause the load declines to store
   cannot disagree.
 * `true` in a body IS THE EMPTY CONJUNCTION, which is what makes `rule H :- true`
   produce exactly the clause `fact H` produces.
 * `PredicateHeadsSpanFiles` — a predicate whose heads span more than one FILE and has no
   declaration is refused, NAMING the files, keyed on the predicate the decision assigned
   each head to (not on the scope the head is written in — every absorption this removes
   moved a clause ACROSS scopes).
 * Three refusals for what would otherwise be silent drops: a body-less rule that can
   declare nothing (⊥ / multi-head / qualified / paren-less nullary), a declaration
   carrying a label, description, tag, `[t]` introducer or typed column, and a
   declaration the defining pass never reached (a `provides … language … end` block's
   interior — WI-20260821-TTHRK).

FIVE MEASURED CORRECTIONS TO THE PROPOSAL, all recorded in its new "Delivered" section:
 1. `:- true` DID NOT WORK. Driven, `rule p(1) :- true` LOADED CLEAN AND ANSWERED
    NOTHING — `true` is a boolean_literal, so the body carried a constant goal nothing
    resolves, and WI-1034's refusal cannot reach it (a constant names no name). The
    proposal called both migration targets "live" on the evidence that they LOAD.
 2. `fact` IS NOT AN AVAILABLE TARGET for a named predicate: a fact head introduces no
    scoped symbol (measured — `fprobe.ff` does not resolve, `fprobe.hh` does), so the
    proposal's per-site reading for the logic axioms would have deleted the very names
    `logic_sorts_test` drives. That gap is WI-20260821-RDGQC's; recorded at §6.1.
 3. THE LOGIC AXIOMS ARE DECLARATIONS, not assertions — their own file says so ("they
    exist as named symbols"), and as facts their variable heads asserted that every pair
    of propositions satisfies modus ponens. 11 sites keep their body-less spelling and
    now mean it.
 4. THE CENSUS WAS 31 CORPUS SITES, not 20 (+3 in anthill-todo's rules, +8 in
    typing_pass_spec, which typing_test loads), plus 116 in 31 Rust fixture files — a
    population no .anthill census sees.
 5. The four refusals above are not in the proposal; each would have been a silent drop.

TESTS: `wi_fqc85_rule_declaration_test.rs`, 13 rows, every one driving the goal — the
four cross-file shapes each in BOTH arms (refused naming the files / declared, clauses on
ONE predicate, answers driven), the declaration reading with its `:- true` control, the
§6.1 desugaring, the four can-declare-nothing shapes with bodied controls, the carrier
refusals, and the equational control in both spellings. WI-980's 24 rows migrated and
green.

BACK-OUTS, ALL EIGHT RUN, not predicted (two of my own predictions were WRONG and the
runs found them: the `DeclaresNothing` and carrier refusals return BEFORE the line I had
credited): declaration reading 14 rows; pass-1 mint 12; empty conjunction 24; file
boundary 6; `DeclaresNothing` verdict 1; carrier check 1; minted-here check 1;
already-declared check 1. WI-980's own four were RE-RUN because the declarations change
what they reach — ownership guard 11 to 7, `<global>`'s two roles 3 to 1 (the stdlib
axiom's declaration is now a stronger guard than the rule that back-out removes), asking
file 4 (two rows now in the FQC85 file), SCC scope 2.

/code-review (high) RAISED NINE, ALL ADDRESSED, and two were live defects in guards I had
just written:
 * THE "PASS 1 NEVER REACHED IT" GUARD ASKED THE LADDER, so any prelude name satisfied
   it: `provides Widget language anthill { rule eq(?x) }` LOADED CLEAN and declared
   nothing — the exact drop the guard exists for, one name from the fixture that caught
   it. It now asks the SCOPE'S OWN LOCALS, and the missed arm is its own test row.
 * PASS 1'S MINT MERGED ONTO ANOTHER CONSTRUCT'S DECLARATION: `operation has(x) -> Bool`
   beside `rule has(?x)`, and `sort Foo` beside `rule Foo(?x)`, both loaded clean with a
   `Goal` kind added to the other symbol — a no-op line that 059 R4 clause 3 refuses
   everywhere else. Refused now, at LOAD (not at the mint, which walks in text order).
 * `head_carries_typed_column` keyed on the SPELLING `typed_var` with no `is_minted`
   pairing — WI-948's own trap — so `rule typed_var(?x)` was refused with a message about
   syntax the author never wrote. Narrowed to ARGUMENTS, where the marker can only be.
 * A dead `descriptions` arm (a description requires a label at parse time, WI-1072, so
   the label arm always answers first) and the test row that "measured" it; a dead
   fallthrough in the detail helper; an over-claiming doc comment on
   `rule_body_is_empty_conjunction` (it and `load_rule` judge emptiness at different
   points — before and after WI-582 guard folding); a duplicated load recipe in
   `tests/common`; and `a_chain_deeper_than_any_recursion_loads`, whose name said the
   opposite of what it now measures (renamed `..._is_decided`, with the per-link
   structure restored alongside the refusal count).

ACCEPTANCE: cargo-test green via rustland/scripts/test.sh — 29 binaries, 0 failures.
scaland sbt test green — 507 passed.

