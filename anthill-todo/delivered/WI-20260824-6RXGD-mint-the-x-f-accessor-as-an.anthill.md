## Attributes

- id: WI-20260824-6RXGD-mint-the-x-f-accessor-as-an
- created: 2026-08-24T10:21:45Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-01T16:17:40Z

- acceptance: cargo-test

## Description

MINT THE `x.f` ACCESSOR AS AN ABSOLUTE PATH, so `anthill.reflect.field_access` can leave the implicit tier. ATTEMPTED AND BACKED OUT 2026-08-24 (claude) — the design is sound, the corpus says one mechanism is not yet understood. Everything below is measured.

WHY. `KERNEL_VOCAB_QUALIFIED`'s own doc says the table is for names the CONVERTER synthesizes and a user never writes. `field_access` is the biggest of those — emitted for every `x.f` — and it does not need a short-name fallback: the converter cannot emit a resolved SYMBOL (it runs per file at parse time with its own `ParsedFile` symbol table, no KB, no scope, no `by_qualified_name`), but it CAN emit a qualified NAME. `..` is the language's own absolute spelling (`intern::ABSOLUTE_PATH_MARKER`, resolved by `absolute_path_target` / `dotted_absolute` with no scope walk), so the mint's spelling can BE its identity.

THE SECOND PRIZE, and the reason this is worth more than one table row: the bare spelling bought a HEURISTIC, not just a fallback. `visit_load` has to tell the converter's accessor from a user-written call to a same-named functor, and does it by `named_args.is_empty()` (kb/load.rs, the `field_access` arm) — see that arm's own comment. An absolute mint makes the two unmistakable by spelling.

WHAT WAS DONE. A `MINTED_FIELD_ACCESS = "..anthill.reflect.field_access"` constant beside `ABSOLUTE_PATH_MARKER`; both converter mint sites (parse/convert.rs, the dotted-name folding arm and `BuildFrame::FieldAccess`) switched to it; the four loader readers keyed on the parse spelling switched with them (`skip_name_slot`, the `visit_load` accessor arm, `dot_call_receiver_chain`, `field_access_dotted_name`); the table entry removed. Builds clean.

WHAT THE CORPUS SAID: 5614 passed, 43 FAILED across 12 files, and the distribution is the diagnosis rather than noise — 38 of the 43 are the PROJECTION / RELATION path (wi_7x7nk 10, wi714_project 9, wi731_rename 6, wi714_drain 4, wi714_recursive 4, wi639_distributive 2, wi732_project_ctor 2, wi762_projection_provenance 2). The dominant error is a TYPER one, `type mismatch in <f>.name: expected resolved name, got unresolved` — the accessor's NAME SLOT being resolved as a reference instead of kept as a label. Two failures are expected and correct: `parse_test::parse_field_access_in_operation_body` asserts the rendered spelling, and `wi040_reserved_vocab_test::query_pattern_bare_field_access_resolves_qualified` is the SECOND CONSUMER (below).

THE LEAD, and it is a lead rather than a diagnosis. `kb/body_specialize.rs:799` reads `if qn != "anthill.reflect.field_access" && qn != "field_access"` — the projection path compares the QUALIFIED NAME against two spellings, the resolved one AND a BARE-INTERNED one. That disjunct exists because a bare-interned accessor is a known state. A THIRD spelling therefore makes this guard decline, which is exactly the observed failure shape. So the evidence points at the absolute name SILENTLY BARE-INTERNING instead of resolving (`remap_name_str` interns rather than erroring, and NO `UnresolvedName` appeared in the run — only downstream typer complaints, which is what a silent intern looks like). NOT ESTABLISHED: why `resolve_dotted_in_kb` does not answer for it, given `absolute_path_target` is checked at its top. FIRST STEP: assert what the functor resolves to. If it bare-interns, fix that; if it resolves, the missing site is elsewhere and `body_specialize.rs:799` is a red herring.

THE SECOND CONSUMER, which must be handled either way: the tier entry answers TWO questions. Converter synthesis (this ticket removes it) and REFLECTION QUERY VOCABULARY — a bare `field_access` in a query pattern with no import, driven by `wi040_reserved_vocab_test::query_pattern_bare_field_access_resolves_qualified`. The census run recorded the same split structurally: `div`, `mod`, `SortInfo`, `OperationInfo`, `SortView` answer ONLY at `resolve_name_in_kb`, never at the term reader. DECIDED (user, 2026-08-24): the CLI should PREPEND THE IMPORTS automatically before parsing a query, so the capability survives through `ImportOrigin::Invocation` — the mechanism the spec already names for "a resolution with no file" — rather than through the tier. `supply_import_flags` (anthill-cli/src/main.rs) is where `-i` enters `<global>`; a default set goes in beside it. Decide the set: exactly the reflect names the tier held, not `anthill.reflect.*` (the wildcard would expose `kind` / `fields` / `rules` / `constructor`, which `KERNEL_VOCAB_QUALIFIED`'s doc says are deliberately excluded as plausible user definitions).

ALSO NOTE, measured while investigating: a user's own `operation field_access` does NOT capture the accessor for a VALUE receiver — `boxed(7).v` answered 7, not the rival's 999, because `visit_load`'s accessor arm lowers that shape structurally and never consults the ladder. ONE SHAPE ONLY; the arm's own comment says the ladder can decline and fall through to the name-resolving path, so this is not evidence that every `x.f` shape is safe.

ACCEPTANCE: the accessor mints absolutely; `anthill.reflect.field_access` is out of KERNEL_VOCAB_QUALIFIED; a bare `field_access` in a CLI query still resolves, via prepended invocation imports; the `named_args.is_empty()` heuristic is replaced by the spelling (or its retention is justified at the site); `parse_test`'s spelling expectation updated; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-08-25T03:16:37Z — feedback — user

DELIVERED IN THE SAME SESSION THAT FILED THIS (2026-08-25, claude), so the ticket's own "ATTEMPTED AND BACKED OUT" opening is now WRONG for the tree and is left standing only as the record of the first attempt. Read this note first.

WHAT THE BACKED-OUT ATTEMPT MISSED, and it was one thing: `distributive_projection` (parse/convert.rs) mints the accessor too, via `self.intern(if is_value_recv { "dot_apply" } else { … })` — the literal sits inside a CONDITIONAL, so a grep for `intern("field_access")` finds two producers and not three. That single miss caused 38 of the 43 failures, all in the projection/relation path. The census must be by NAME across the file, never by call spelling.

AND THE LEAD IN THE TICKET TEXT WAS WRONG: `body_specialize.rs:799` (`qn != "anthill.reflect.field_access" && qn != "field_access"`) is NOT the mechanism. Driven before re-attempting — `resolve_name_in_kb` answers Found(Symbol(137)) for all three spellings (`..anthill.reflect.field_access`, `anthill.reflect.field_access`, `field_access`), so the absolute name resolves fine and nothing bare-interns. Three lines of probe killed the hypothesis the ticket spent a paragraph on.

DELIVERED: `intern::MINTED_FIELD_ACCESS = "..anthill.reflect.field_access"`; all THREE converter producers mint it; the four loader readers keyed on the parse spelling re-keyed; `anthill.reflect.field_access` removed from KERNEL_VOCAB_QUALIFIED. The query consumer is served by `QUERY_VOCABULARY` / `supply_query_vocabulary` (anthill-cli), an `ImportAttribution::Invocation` import — the user's own design, and the mechanism §8.6 already names for a resolution with no file. Named, not wildcard, so `kind` / `fields` / `rules` / `constructor` stay unreachable as their doc requires.

TESTS: `wi6rxgd_query_vocabulary_test` (CLI: wiring, plus a `kind` narrowness control) and, in the core, `wi040::a_supplied_import_binds_field_access_to_its_reflect_home` (the bound SYMBOL) and `wi040::the_minted_accessor_target_is_declared_by_the_standard_load` (the orphan watchdog the removed table row used to provide). `wi040`'s query row and `parse_test`'s rendering expectation are INVERTED, and say so at their sites. Full workspace green.

TWO THINGS THE `named_args.is_empty()` GATE READER SHOULD KNOW, because both this ticket's acceptance and a review comment got them wrong: the conjunct is NOT redundant after the absolute mint, and it does NOT still separate "minted vs written". Written calls are excluded EARLIER, by the spelling. What the conjunct separates now is two MINTED producers — the plain accessor (empty named args) from the distributive projection (one named arg per member). Remove it and a projection takes the accessor ladder and silently drops its member subtrees. Stated at the gate. Consequently `wi749_named_args_on_field_access_are_not_dropped` no longer reaches that arm; it still passes, for a different reason, and its doc now records that.

NOT DONE: scaland. It still mints the bare `field_access` and has no `QUERY_VOCABULARY`, so the two implementations disagree on what a bare `field_access` means and on whether a namespace-level `operation field_access` captures every `x.f`. This ticket's `scaland-sbt-test` acceptance is therefore UNMET and the port is the remaining work.

### 2026-08-25T04:45:04Z — feedback — user

RETRACTION — the previous feedback note on this ticket contains a FABRICATED MECHANISM, and it is retracted here rather than edited away.

WHAT IT CLAIMED: "the conjunct is NOT redundant after the absolute mint … What the conjunct separates now is two MINTED producers — the plain accessor (empty named args) from the distributive projection (one named arg per member). Remove it and a projection takes the accessor ladder and silently drops its member subtrees."

THAT IS FALSE, and was never measured. `parse::pratt::mint_op_node` hard-codes `named_args: SmallVec::new()`, and `distributive_projection`'s `named` vec collects `(label, access)` pairs for the ENCLOSING `TupleLiteral` — every accessor inside it has NO named args. Parse-IR probe of `p.(x, y)`: the `TupleLiteral` carries named=2, all three `..anthill.reflect.field_access` nodes carry named=0. Found by /code-review; verified at `pratt.rs` and `convert.rs` before writing this.

WHAT IS TRUE: the `named_args.is_empty()` conjunct is now UNREACHABLE among minted nodes. The absolute spelling already separates a converter accessor from a user-written `field_access(…)` call, which is the job the conjunct used to do. It is kept as an invariant guard against a future producer that emits named args, not as a discriminator that fires today. Both the gate comment and `wi749_rule_ref_zero_arg_member_test`'s note now say so.

HOW THE ERROR HAPPENED, since the shape is the reusable part: I read `let mut named: SmallVec<…> = SmallVec::new();` a few lines below the functor mint inside `distributive_projection` and concluded the vec was the functor's named args. It is the tuple's. I then asserted the mechanism while explicitly CORRECTING a reviewer's framing — "both the reviewer's framing and my earlier 'redundant but harmless' were wrong" — which is the sentence that should have triggered a probe rather than a claim. The reviewer's original framing was closer to right than my correction. Proximity in the source is not a data-flow argument; three lines of parse-IR probe settled it.

### 2026-08-25T06:35:03Z — feedback — user

SECOND /code-review — FIVE FINDINGS AGAINST THE DELIVERED field_access WORK, all measured. I had called this half "comparatively clean"; it is not. Recorded because the implementation may not survive and these are the durable part.

1. THE REMOVED TIER ROW HAD A THIRD READER, NOT TWO — and this is the one that matters most. Three places in the diff (intern.rs, anthill-cli/main.rs, wi040's header) say the row "answered TWO questions": converter synthesis and reflection-query vocabulary. But `resolve_name_in_kb` is ALSO `KnowledgeBase::resolve_name_in_global` — the WI-908/913 HOST-NAME ladder. `QUERY_VOCABULARY` restores the name only inside `run_query`, so every other host-name consumer now misses at every rung: `reflect.lookup_symbol("field_access")` -> `builtin_lookup_symbol` returns Failure with NO diagnostic, then `resolve_host_name` -> `EvalError::Internal("lookup_symbol: unknown symbol `field_access`")`. Same for `make_fn`, `make_apply`, `Store.monotonicity`, `make_sort_ref_by_name`, and extent mount owner names — i.e. `anthill run` / `check` / `prove`, codegen, and any embedding. Under `anthill query` the CLI import MASKS it, which is why no test sees it. A metaprogram naming the accessor is broken.

2. `dot_apply` WAS LEFT BARE ONE COORDINATE AWAY, inside the same conditional the absolute mint edited: `self.intern(if is_value_recv { "dot_apply" } else { MINTED_FIELD_ACCESS })`. `dot_apply` is the only converter marker a user-written call can still be mistaken for, and its reader has NEITHER an `is_minted` gate NOR an absolute spelling, where `field_access`'s now has both. MEASURED live hijack: a user's `operation dot_apply(a, b)` plus a written `dot_apply(1, zz)` is silently re-read as `1.zz` and reports "expected operation declared on the receiver's sort, got no such member (dot dispatch)"; the byte-analogous `field_access(2, zz)` is clean and reaches the user's operation. The two were symmetric BEFORE this diff. Three sites now ask "is this the converter's marker?" three different ways.

3. THE CAPABILITY REMOVED, AND THE PRESCRIBED REPAIR DOES NOT LOAD — documented in three places. Narrowing the accessor gate to `name == MINTED_FIELD_ACCESS` makes all three re-routes below it (WI-280 local-value root, WI-714 whole-chain rule citation, WI-749 rule-prefix zero-arg member) unreachable for a hand-written `field_access(recv, field)`, which used to desugar exactly like `recv.field`. All three spellings fail: bare -> "type mismatch in x.name: expected resolved name, got unresolved" (blames the argument, never names `field_access`); the documented repair `import anthill.reflect.{field_access}` + `field_access(p, "x")` -> "expected a type for 'Name'"; and `field_access[Name = "x"](p, "x")` -> "expected Int64, got FieldOf[...]". §6.7's new "A HUMAN writing `field_access(x, \"f\")` imports it" is an unrun repair.

4. `QUERY_VOCABULARY` CHANGED PRECEDENCE CLASS, it did not "move" the capability. The tier row was a LOWEST-precedence fallback in `resolve_name_in_kb`'s `.or_else(..)`; a selective import into `<global>` is consulted BEFORE that scope's parent links, so it OUTRANKS the author's own `-i <ns>.*`. MEASURED with an isolating control: two byte-identical rules `field_access` and `zz_access` in one namespace, imported by `-i 'probe.kb6.*'` — `zz_access` answers 1, `field_access` answers 0; the clause exists (`--mode functor 'probe.kb6.field_access'` -> 1). The doc's "SHADOWABLE, like any import: a program declaring its own top-level `field_access` wins" covers `<global>` LOCALS only, and a query run has none.

5. THE SUPPLY MAKES `UnresolvedImport` UNABLE TO FAIL FOR THIS ONE NAME. The selective-import resolver's strategy 2 climbs to `<global>`, where the vocabulary already bound `field_access`, so the existence test always succeeds. DRIVEN with a sibling control: `-i 'mylib10.{kind}'` correctly errors "unresolved import"; the byte-identical `-i 'mylib10.{field_access}'` exits 0 and silently binds `anthill.reflect.field_access`. A typo or mis-import of a user's own `field_access` is now unreportable — a loud error became a silent wrong binding.

ALSO: `body_specialize.rs:799` and its mirrored copy in `anthill-smt-gen/src/lib.rs:1679` — the `|| == "field_access"` fallback arms are now unreachable, AND an unresolved mint bare-interns as `..anthill.reflect.field_access`, matching neither string, so both accessor recognizers fail CLOSED and silently.

### 2026-09-01T16:17:39Z — feedback — user

DELIVERED 2026-09-01 (claude) — BUT NOT AS THIS TICKET'S TEXT DESCRIBES, and the whole
opening is now historical. Read this note first; the ticket above is the 2026-08-24 record.

THE TICKET'S OWN SUBJECT HAD ALREADY SHIPPED, under two other tickets, and neither of them
is named above. `..anthill.reflect.field_access` entered the code in ceb203b7
(WI-20260825-5W3RJ, "a desugared functor names its target, absolutely"), and
WI-20260831-S66VH generalized it to twelve addresses in `parse::desugar_target`.
6RXGD's OWN delivery was never committed: `git log -S'QUERY_VOCABULARY' --all` finds that
string only in this file's prose, never in a `.rs`. So the three feedback notes above
describe a tree that does not exist, and the five review findings had to be re-measured
rather than worked from.

RE-MEASURED, ALL FIVE:
 #2 (`dot_apply` left bare) — CLOSED BY CONSTRUCTION. `DOT_APPLY` carries an address now.
    Driven: a user's `operation dot_apply(a,b) = 999` and `operation field_access(a,b) = 888`
    are BOTH reached by written calls (999 / 888). Symmetric again.
 #4, #5 (`QUERY_VOCABULARY` precedence; unfailable `UnresolvedImport`) — MOOT. That code
    never landed. `wi040_reserved_vocab_test` took the opposite route and its rows are
    inverted to say so: the qualified spelling is required.
 #1 (the host-name ladder had a THIRD reader) — CONFIRMED, and now general rather than
    about one name. `KnowledgeBase::resolve_name_in_global` answers NotFound for
    `field_access`, `dot_apply` and `ListLiteral`, Found for `SortInfo` and `cons`, and
    Found for both QUALIFIED spellings of the accessor. So a host-supplied name must be
    spelled qualified — the same decision `wi040` made for query patterns, reached
    independently. Not re-litigated here.
 #3 (a hand-written accessor) — INVERTED, and this is what the ticket became. The
    capability came BACK with S66VH's `desugar_target::is`, whose third arm admits the
    SHORT spelling. What is still broken is the other half of #3: the repair §8.6
    prescribes — import the declared operation and call it — did not load, in ANY spelling.

WHAT WAS FIXED: `anthill.reflect.field_access` IS CALLABLE BY HAND.
`operation field_access[R, Name](object: R, field: String) -> FieldOf[T = R, Name = Name]`
takes the selector name TWICE, once per channel, because there are no singleton types — its
own doc says so. Every hand-written spelling came back `FieldOf[T = P, Name = ?Name]`, an
irreducible residual: `[Name = "x"]`, the positional `[P, "x"]`, and a written
`FieldOf[…]` annotation alike.

THE CAUSE WAS A CARRIER, NOT THE SIGNATURE, and the tree already stated it. A denoted
written in a bracket rides as a `Value::Node` (`Loader::type_expr_to_value`, because a
denoted may carry poison — `Modify[c]`), and the `TermId` deep σ-walk that resolves a
term-backed return type STOPS at a non-`Term` binding (WI-394).
`typing::synthesize_field_access` — what `q.x` rewrites to — already grounds its own `Name`
argument for exactly that reason and says so at the site. The channel a PERSON writes had no
route to it. `typing::ground_literal_denoted` gives it one, at `seed_op_type_args`, for a
CLOSED LITERAL only.

TWO WIDER REPAIRS WERE BUILT AND REJECTED ON MEASUREMENT, not on taste:
 - RE-GROUND AT THE LOADER (`TypeExpr::Denoted`, which is emitted for literals ONLY, so it
   looked like the general fix). Full workspace: 2 failures.
   `wi366_value_in_type_facts_test::provides_block_value_in_type_spec_loads_without_panic`
   went red because `lower_value_or_gate` decides by term-representability — so
   `provides Foo[Int64, 3]` STOPPED reporting the WI-366 "not yet resolved" diagnostic and
   started silently accepting an unresolved clause. That is the silent-skip the gate exists
   to prevent, and it is what disqualified the repair.
   `wi404_denoted_self_conformance_test::differing_denoted_literal_rejected` went red too,
   rendering `Name = TermId(16082)` — a SECOND, pre-existing defect the repair exposed:
   `type_display_name` has no `Term::Const` arm while its Node peer's `denoted_value_display`
   does, and both docs claim the two are paired arm-for-arm. SEE THE REVIEW BELOW: I first
   recorded that arm as undrivable and left it, and that was wrong.
 - TEACH THE σ-WALK to follow a Node binding (WI-394's stop). Not built: it widens a hot
   resolution relation to fix one channel, and the narrow repair makes the surface channel
   do what the synthesized one already does.

/code-review (high) FOUND FOUR THINGS, and the first one is the important one.
 1. THE NARROW REPAIR MAKES THAT `Term::Const` ARM DRIVABLE — my comment saying nothing
    could drive it was FALSE, and this diff is what falsified it. Grounding a written
    bracket's literal puts a `Term::Const` denoted into σ for EVERY operation with a
    value-in-type parameter, not only `field_access`. Re-driven independently on a fixture
    with no `field_access` in it — `mk[T, N]() -> Vec[T = T, N = N]` called as
    `use2() -> Vec[T = Int64, N = 4] = mk[Int64, 3]()` — which reported
    `got Vec[T = Int64, N = TermId(8960)]`. That is exactly the illegibility WI-404 exists
    to prevent, and every WI-404 row is green either way because none of them writes a CALL
    bracket. FIXED: the one-line `Term::Const(lit) => literal_display(lit)` arm, with
    `a_written_literal_bracket_renders_its_literal` as its own control (that row, and only
    that row, fails when the arm is removed).
 2. THE NEW DOC BLOCK STOLE `denoted_name`'S DOC — inserted above the new function, which
    sits above the old one, so the WI-759 three-liner headed the wrong function and
    `denoted_name` was left undocumented. Invisible to the compiler and the suite. Restored.
    (Same footgun as two earlier sessions; anchoring a doc insert on a `fn` line is what
    does it.)
 3. `an_annotation_written_by_hand_still_does_not_reduce` did NOT pin the rendering, though
    its doc claimed to: its denoted comes from an ANNOTATION, rides the Node carrier, and is
    green with the change backed out. Doc corrected; the claim moved to the row that earns
    it.
 4. The 2026-08-25 note's closing paragraph ("this ticket's `scaland-sbt-test` acceptance is
    therefore UNMET") is SUPERSEDED — the acceptance attribute is now `cargo-test` and the
    port is WI-20260901-ERF7T.

TESTS: `wi6rxgd_field_access_call_test`, six rows. THE CONTROL IS `ground_literal_denoted`
returning `None`: three rows fail — the two calls stop type-checking with
`expected Int64, got FieldOf[T = P, Name = ?Name]`, and
`a_name_the_receiver_does_not_have_is_refused` fails because its refusal changes from
"`P` has no field `zz`" (the name was READ) to the same `?Name` residual (the name was never
read). That third row is what separates "resolved" from "made to disappear"; the first two
alone cannot. `the_dot_form_is_unaffected` passes either way BY DESIGN — the representation
control that bounds the change to the written bracket. Measured, not asserted.
`a_written_literal_bracket_renders_its_literal` has a SEPARATE control — the `Term::Const`
arm — and needs both halves: grounding puts the denoted where a diagnostic reaches it, the
arm renders it.
Full workspace green.

NOT DONE, AND WHERE IT WENT:
 - The BARE SHORT SPELLING still takes the accessor ladder, and §8.6 says three times that
   it must not. Driven with a control: `field_access(q, x)` answers 7 in an operation body
   where `foo_access(q, x)` is a load error; the same spelling is a loud error as a
   rule-body goal and a bare intern in a query pattern. `dot_apply` behaves identically.
   Corpus: ZERO hand-written short-spelling calls. Recorded AT the rescue site (kb/load.rs,
   the accessor arm) and owned by WI-20260901-92VA4 — which side moves is a decision, and
   the objection that used to block narrowing is what this ticket removed.
 - SCALAND: split out as WI-20260901-ERF7T, and this ticket's `scaland-sbt-test` acceptance
   dropped (user, 2026-09-01). The port is no longer "mint `field_access` absolutely" — it
   is the whole twelve-address mechanism plus the `ExprMarker` question.
 - A `FieldOf[…]` a user writes in their OWN return-type annotation is not a
   `CtorReduceSite` and stays unreduced. Pinned by
   `an_annotation_written_by_hand_still_does_not_reduce` rather than left as prose; a caller
   does not need it, since declaring the field's concrete type is what works.
 - The WI-366 gate and the loader's carrier rule are UNCHANGED. Only `seed_op_type_args`
   re-grounds, and only a closed literal, so every other consumer of a written type still
   sees the Node it saw before.

