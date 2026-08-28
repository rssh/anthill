## Attributes

- id: WI-20260827-3ZNBC-eliminate-the-value
- created: 2026-08-27T14:59:27Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-28T12:26:24Z

- acceptance: cargo-test

## Description

ELIMINATE THE VALUE-NORMALIZATION FAMILY — the eval bridge converts operands into native values to work around operations that cannot read a carrier, and at least one of those operations can now read it.

THE FAMILY, and it is smaller than it looks. Every path bottoms out at THREE call sites:

    kb/resolve.rs (3 sites, the eval bridge)
      -> Interpreter::materialize_value        eval/mod.rs:798
           -> builtins::term_to_value          (2 callers, both inside materialize_value)
                -> builtins::value_to_native   (private)
                     -> builtins::materialize_entity

`persistence/term_ser.rs::term_to_value` and anthill-stl's `reify_term_to_value` share the stem and are UNRELATED — a JSON serializer and a reflect reifier. Do not sweep them in.

`materialize_entity` has one legitimate caller outside the family: `term_as_entity`, the reflect operation whose whole job IS Term -> Entity. That one stays.

WHY IT EXISTS, in its own words. resolve.rs:7767 — 'materializing each term/occurrence operand into the interpreter's native form (Value::Term(box(…)) / Value::Node -> Value::Entity), else a body that reads a field errors with "receiver is not an entity"'. That error came from `reflect_field_access` matching `Value::Entity` alone. WI-20260827-2YHZ3 gave it a `TermView` arm, so the stated reason for at least one of the three sites no longer holds — MEASURE whether it holds for any of them.

`Interpreter::materialize_value` ALSO CONTAINS A NODE->TERM LOWERING (eval/mod.rs:801, WI-685: 'lowered the same way — to a term, then to the native form'). That lowering interns a term per bridged operand — a store write for a read, pinned for the KB's lifetime — and discards the occurrence's span. WI-20260827-2YHZ3 added the identical lowering one level down, measured it, and removed it in favour of carrier-neutral arms; this is the same code one level up and has never been re-examined.

WHAT THE ARMS LOOK LIKE, since 2YHZ3 shipped two as worked examples:
  * `reflect_field_access` — read the receiver's functor / named args / positional args through `TermView` instead of destructuring `Value::Entity`. This REMOVED a case: Entity, Term and Node all view as `ViewHead::Functor`, so one arm replaced what would have been three.
  * 21 binary scalar wrappers (Int64/Float/BigInt arithmetic, Bool.and/or, String.concat/startsWith/endsWith) — operands read through `scalar_operand`, which asks `TermView::head` what literal the operand denotes. A non-scalar passes through unchanged and meets the caller's existing refusal, so it widens what an operand may be CARRIED AS, never what it may BE.

THE REMAINING SURFACE IS MEASURED, and it is the reason this is its own ticket rather than more of 2YHZ3: 112 functions in eval/builtins.rs touch a native `Value` variant and there are 99 `type_mismatch` refusal sites. NOT all of them need an arm — only those an operand can actually reach — and deciding which is the work. Some SHOULD discriminate on carrier (a reflect operation whose subject IS the handle), and telling those apart from the ones that merely forgot is the judgement this ticket buys.

WHY IT MATTERS BEYOND TIDINESS. Normalization is an UNENFORCED DUTY at every producer: nothing makes a new bridge site call `materialize_value`, and forgetting fails at runtime with a type error rather than at compile time. That is exactly how WI-20260827-2YHZ3's relation-column drain came to hand `Int64.add` something it could not read. Moving the read to the point of USE makes the consumer's own code the enforcement.

A PREMISE THAT LOOKS LOAD-BEARING AND IS FALSE, recorded so it is not re-derived: 'the interpreter's value operations are native-only and are not meant to be carrier-neutral'. Reflect `Term` values ALREADY flow through anthill code as `Value::Term` — `Substitution.lookup` returns one, `term_as_entity` takes one — so handles are already first-class runtime values. The operations simply did not know it.

ACCEPTANCE: `Interpreter::materialize_value` and `builtins::value_to_native` are GONE, or each surviving call site says at its own line which operation still cannot read a carrier and why that is right; the three bridge sites pass their operands through unconverted; the Node->Term lowering at eval/mod.rs:801 is deleted with it. A test DRIVES a bridged operation body over an operand on each of the three carriers (Term, Node, native) and asserts the SAME answer — asserting the value, since a count is 1 for all three. CONTROLS THAT MUST STAY GREEN, and say at each site which fail on a back-out: `term_as_entity` keeps refusing a non-handle carrier LOUDLY (`term_as_entity(5)` is an error, not `none()`); WI-685's own coverage (a rule-body eq/neq occurrence operand reaching a bridged body); and every eval_test. Full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-08-27T16:23:10Z — feedback — claude

SCOPE MEASURED 2026-08-27, by removing the drain's conversion and running the full suite: 76 TESTS FAIL. That is the number this ticket is worth, and it is much larger than the three bridge call sites suggest.

THE FAILURES ARE ALL ONE SHAPE and none of them is a builtin: a relation row column holds `Value::Term { id }` (or a `Value::Node`) where the consumer expects `Value::Str` / `Value::Int`. Families hit: `wi730_boolean_condition_test` (join/where conjunction, disjunction, negation, mixed nesting), `wi731_rename_test`, `wi733_relation_head_eval_test` (head / headOption / head-and-tail decompose), `wi741_spec_typed_column_test`, `wi_yqb1y_one_column_relation_test`, `wi_7x7nk_projection_names_no_column_test`, `wi_9c2pz_per_application_type_params_test`, `wi751_namespace_root_shadow_test`. Representative message: `expected a String column in the row, got Term { id: TermId(16049) }`.

SO THE CONSUMER SET IS NOT eval/builtins.rs. A relation row is read by RUST-SIDE code and by test assertions that pattern-match the native variant directly, not only by anthill operations dispatched through a builtin. Any plan that fixes the 112 `Value`-matching functions in eval/builtins.rs and stops there will still fail these 76 — the row's NATIVE SHAPE is load-bearing well past the builtin surface, and deciding what a row column IS (a native value, or a handle the reader views through) is the actual design question. That question is this ticket's, and it is bigger than 'add the missing arms'.

WHAT ALREADY LANDED under WI-20260827-2YHZ3, so it is not re-done here: `TermView` gained the carrier-neutral literal accessors (`as_literal` plus `literal_bool` / `literal_int64` / `literal_f64` / `literal_big_int` / `literal_string`), 21 binary scalar builtins read their operands through them (the read IS the guard, no normalize line to forget), and `reflect_field_access` reads its receiver through `TermView` — which REMOVED a case, since Entity/Term/Node all view as `ViewHead::Functor`. Those stand on their own and are unaffected by the drain keeping its conversion.

NAMING TRAP FOUND AND AVOIDED, worth knowing before adding more accessors: `Value` carries INHERENT `as_bool` / `as_int` / `as_str` that read the native variant ONLY, and an inherent method WINS over a trait method. A trait accessor spelled `as_bool` resolves silently to the carrier-blind one at every `Value` call site. Hence the `literal_*` stem.

### 2026-08-27T16:24:36Z — feedback — claude

THE FIX FOR THOSE 76 IS KNOWN, and it is the same move one level out: the readers ask `TermView::literal_string` / `literal_int64` instead of matching `Value::Str` / `Value::Int`. The accessors already exist (WI-20260827-2YHZ3). Nothing is blocked; the work is deciding, not discovering.

BUT IT IS A CONTRACT CHANGE, NOT A REFACTOR, and that is the reason it belongs here rather than in the ticket that surfaced it. `materialize_solution`'s own doc STATES the current contract: 'REIFY it to a native value (scalar const -> scalar Value, constructor -> entity) so the column reads as its element sort, not a raw Term handle — a `Relation[String]` yields `Value::Str`, a `Relation[Board]` an entity' (eval/mod.rs, WI-714). The 76 tests are that sentence, asserted. Changing them is changing WHAT A RELATION ROW IS — from 'a native value' to 'a handle the reader views through' — and several of those suites pin a neighbouring WI's own convention on top of it (WI-20260818-YQB1Y's one-field-tuple row, WI-731's column positions, WI-741's spec-typed columns).

SO THIS TICKET'S FIRST DECISION IS THAT SENTENCE. Either it stands — and the conversion stays, with each surviving call site saying which consumer still needs it — or it is rewritten, and WI-714's doc, the 76 assertions, and any host embedder reading a row move together. Do not change the readers without changing the sentence: a test suite updated to match new behaviour, over a doc that still promises the old one, is how the next reader gets it wrong.

WORTH CHECKING EITHER WAY: whether a row ever leaves the interpreter to a HOST embedder (the Relation face is public), because that consumer cannot be updated by editing this repo's tests.

### 2026-08-27T20:12:47Z — feedback — claude

THE CARRIER-NEUTRAL WIDENING WAS WRITTEN, MEASURED, AND THEN BACKED OUT of WI-20260827-2YHZ3 — it belongs here, and the reason it was pulled is a finding this ticket should not repeat.

WHAT EXISTED AND WORKED: `TermView` gained `as_literal` + `literal_bool` / `literal_int64` / `literal_f64` / `literal_big_int` / `literal_string`; 21 binary scalar builtins read operands through them; `reflect_field_access` read its receiver through `TermView`. Full suite green with all of it in (36 binaries / 0 failed, wi_tests 3618).

WHY IT WAS BACKED OUT ANYWAY — /code-review, and it is the repo's own rule: THE SET WAS ARBITRARY AND NOTHING TESTED IT. Widened: int/float/bigint add/sub/mul/div/mod/rem, bool and/or, string concat/startsWith/endsWith. NOT widened, sitting immediately beside them: `int_neg`, `int_abs`, `bool_not`, `value_compare` (which backs gt/gte/lt/lte), and every `str_operand`-based String op. So `Int64.add(handle, 1)` succeeded while `Int64.gt(handle, 1)`, `Int64.abs(handle)`, `Bool.not(handle)`, `String.length(handle)` still raised. And NO test drove a handle into any widened arm — with the drain normalizing, no path could — so all 13 would have passed identically backed out. CLAUDE.md: 'a test for a capability must DRIVE the capability' and 'assert the CONTROL too'.

A SECOND INCOHERENCE THE HALF-WIDENING CREATED, worth designing against here: `reflect_field_access` on a handle receiver returns its CHILDREN as raw handles (`ViewItem::to_value` yields `Value::term`/`Value::node`), where the `Value::Entity` arm returns already-native children (entities are built by `materialize_entity`, which reifies each field). So one field read answers native or handle depending on how the RECEIVER arrived, and only the widened subset can consume the handle form. Widening consumers piecemeal produces exactly this; the set has to close.

WHERE TO START: the diff is preserved at scratchpad/builtins-widened.rs for this session, but it is reconstructible in an hour and the ticket body's two worked examples describe it. What is NOT reconstructible is the above: close the set, and drive each arm with a handle-carried operand.

TWO CARRIED-OVER TRAPS: (1) `Value` has INHERENT `as_bool`/`as_int`/`as_str` reading the native variant only, and an inherent method WINS over a trait method — a trait `as_bool` silently resolves to the blind one at every `Value` call site, hence the `literal_*` stem. (2) `as_literal` CLONES `String`/`BigInt` (`Value::Str(s) -> Const(Literal::String(s.clone()))`), so `startsWith`/`endsWith` in a filter allocate two owned Strings per call where they used to borrow — a borrowing variant, or a native fast path first, is wanted before this goes on a hot path.

### 2026-08-27T21:00:59Z — feedback — claude

CORRECTION to the previous entry: the carrier-neutral widening was NOT backed out. It shipped with WI-20260827-2YHZ3, and the set is CLOSED — so this ticket does not inherit it.

I backed it out on a /code-review finding ('the set is arbitrary and nothing tests it') and cited CLAUDE.md's 'a test for a capability must DRIVE the capability' as if it forbade shipping untested code. THE USER CORRECTED BOTH HALVES. That rule is about what a TEST must do, not a prohibition on code; and more to the point, reading an operand through `TermView::literal_int64` instead of matching `Value::Int` is not a new CAPABILITY needing its own driving test — it is asking the existing question correctly. It strictly widens what is accepted, changes nothing for previously-accepted inputs, and the existing arithmetic/string/comparison suites already cover the behaviour.

THE SET IS NOW CLOSED, which was the finding's substantive half: `int_neg`, `int_abs`, `bool_not`, `value_compare` (backing compare/gt/gte/lt/lte/max/min) and `str_operand` (15 call sites: contains/indexOf/replace/split/length/substring/…) read carrier-neutrally alongside the original 21. So the incoherence that finding named — `Int64.add(handle, 1)` succeeding while `Int64.gt(handle, 1)` refused — is gone; it was an artifact of a half-done set, not of the approach.

`str_operand` RETURNS `Cow<'a, str>`, which also answers the review's allocation concern about `as_literal` cloning: a native `Value::Str` still BORROWS exactly as before, so a filter over a long stream allocates nothing new; only a handle carrier pays a clone, and that carrier could not be read at all previously. The concern therefore does NOT carry over to this ticket for the String surface.

WHAT THIS TICKET STILL OWNS, unchanged: eliminating `Interpreter::materialize_value` / `value_to_native` and the Node->Term lowering at eval/mod.rs:801 — i.e. whether a relation ROW column is a native value or a handle the reader views through, which is WI-714's stated contract and the 76 tests that assert it. The builtin surface being carrier-neutral is a PREREQUISITE that is now in place, not part of the remaining work.

### 2026-08-28T12:25:58Z — feedback — claude

DELIVERED. The normalization is gone from both live paths and every reader now asks the carrier-neutral question instead.

WHAT WENT. `Interpreter::materialize_value` (with the WI-685 Node->Term lowering that interned a term per bridged occurrence operand) and `builtins::term_to_value` are DELETED. The three bridge sites (`bridge_op_to_eval` x1, `bridge_eq_op_to_eval` x2) hand `call_op_bridged` the operands on the carrier the resolver proved them on; `materialize_solution` hands each column through unconverted.

WHAT STAYED, and the line says why. `value_to_native` has exactly ONE caller left -- `materialize_entity`'s field conversion, i.e. `term_as_entity`, the reflect operation whose product IS a native entity for the anthill `case` that asked for it. Handing back an entity whose fields were still handles would leave the decode half-done and reintroduce the very incoherence this ticket removed. It is `fn` now, not `pub(crate)`.

THE SENTENCE IS REWRITTEN, which the ticket said had to move with the readers. `materialize_solution`'s doc no longer says "REIFY it to a native value ... a `Relation[String]` yields `Value::Str`"; it states that a column is the bound value ON ITS OWN CARRIER and the reader asks `TermView::literal_*`. `docs/kernel-language.md` never stated the row's Rust-level carrier, so nothing moved there.

MEASURED, AND THE NUMBER IS 95, NOT 76. Removing the conversions alone fails 95 tests: `wi_tests` 3588 passed / 91 failed, `builtin_tests` 2, `resolve_tests` 2. The earlier 76 measured the drain only; the bridge sites are the rest. Every one is green with the readers widened.

THE SET, CLOSED. Each of these refused (or silently mis-answered) a value it could read:
  * `eval/eval.rs` `runtime_carrier_sort` -- THE ONE THAT COST REAL THINKING. A handle that DENOTES a scalar named NO carrier: `value_functor` answers `None` for a `Const` head, so the value reached spec dispatch with no receiver sort and the goal RESIDUALIZED. `vec_scale(c: Float, v: Vec3) = Vec3(x: c * v.x, ...)` from a rule body is the witness, and `vec_sub` PASSING beside it is what localizes the case: a field read (`v.x`) is not what breaks, a BARE LITERAL operand is.
  * `eval/eval.rs` `if`-condition -- `Value::as_bool` is the INHERENT accessor and sees `Value::Bool` alone (the trap WI-20260827-2YHZ3 recorded: an inherent method wins over a trait one, which is why the neutral reader is spelled `literal_bool`).
  * `eval/pattern.rs` `constructor_sub_values` -- four carrier arms collapsed onto ONE `TermView` read, and an APPLIED occurrence now destructures. Its comment said declining one "costs nothing today"; it cost nothing only while the bridge normalized. Named args are canonicalized here because an occurrence holds a SOURCE-order slice where the record builders canonicalize -- without it `Vec3(y: 2, x: 1)` in a rule body would hand `x`'s sub-pattern the `y` component (the WI-788 family).
  * `eval/pattern.rs` `literal_matches` -- `case "alice" ->` over a handle fell through to the NEXT ARM. A wrong branch taken silently, the worst shape a missing carrier arm has.
  * `eval/map_arena.rs` `MapKey::try_from_value` -- a term-carried `"alice"` keyed as `MapKey::Term(tid)` and SPLIT from the native key, so `Map.get` answered `none()` for an entry `Map.put` had just stored. Merging them is the same rule WI-1015/WI-1023 already applied to a symbol's two carriers, applied to a literal's.
  * `eval/builtins.rs` -- `float_val` (whose doc ALREADY claimed to mirror the resolver's carrier-neutral `value_f64` and did not); the three `Float` IEEE predicates; a new `int_operand` / `big_int_operand` beside the existing `str_operand`, used by `substring` / `repeat` / `slug` / `digestBase32` / `Dictionary.sub` / `Int64.to_string` / `to_float` / `to_bigint` / `to_int` / `bigint_neg`; `term_as_string` / `term_as_int`; the reflect name arguments and `field_access`'s selector; and `value_compare`'s dead native fallback deleted -- every pair it could still answer reads as `Const` above it, so its only REACHABLE arm was its own error.
  * `anthill-stl/src/reflect/builtins.rs` -- `str_arg`, `option_string_arg`, `decode_literal_repr`'s payload.

THE ONE BEHAVIOURAL DELTA, stated so it is not rediscovered as a bug. The reifier bottomed out in `materialize_entity`, which DEFAULTS a declared `Option[T]` field the fact leaves unsupplied to `none()` (the loader fills the slot with a synthetic Var so the discrim tree can index the fact uniformly). A handle-carried entity column keeps that Var. It fails LOUDLY -- `case some(v)` / `case none()` over a var matches neither and raises `MatchFailed` -- and no corpus path reaches it (no relation ranges over an entity with unsupplied optional fields). The defaulting is not lost, only no longer applied at the drain; if a column ever needs it, the honest home is the field READ, where it would serve every carrier at once. That is a capability, not part of this move. Recorded at `materialize_solution`'s doc.

NO NEW TEST, ON INSTRUCTION AND ON EVIDENCE. The user's steer was "refactoring should ensure that old test works", and it does: 95 existing tests fail on a back-out and pass with the change, and NO EXPECTATION was edited -- a test that asserted `"alice"` still asserts `"alice"`, read through `common::scalar_str` instead of `matches!(_, Value::Str(_))`. Between them they already drive what the acceptance asked one test to do: a Term-carried operand (fact-matched columns -- wi714, wi727, wi741), a Node-carried one (rule-body occurrences -- vec3_ops, wi1096, wi625, push_choice) and a native one (host `interp.call` args -- wi1127's parameter channel), through bridged bodies and relation columns alike, all answering the same values.

TWO ASSERTIONS DID CHANGE, and they are contract statements rather than expectations, so their prose moved with them: `map_arena`'s `both_symbol_carriers_key_one_map_slot` and `a_non_canonicalized_nullary_constructor_keys_as_its_name` each pinned "a term-carried literal keys as `MapKey::Term`" -- the split this ticket removes. They now pin the MERGE, and assert the native twin keys identically.

CONTROLS. `term_as_entity`'s loud non-handle refusal (`other => Err(type_mismatch("Term", ...))`) is UNTOUCHED -- there is no dedicated `term_as_entity(5)` test in the corpus and none was added; wi260's two `returns_none_for_*` rows keep the `none()`-vs-error split. WI-625's own bridge coverage (26 rows) and every `eval_test` are green. Full workspace green via `rustland/scripts/test.sh`.

/code-review (high) FOUND SEVEN, ALL FIXED, and two of them were the ticket's own defect reappearing one arm short:

  1. `MapKey::try_from_value` keyed a term-carried entity by `TermId` and REFUSED the same entity on the occurrence carrier — so `Map.put(m, Board(1,2), v)` worked for a board proved by a fact match and hard-errored for one bound by a rule-body builtin. Closed by `MapKey::of_value_interning`, which every `Map` builtin now goes through: it interns the occurrence to the term it denotes (the same `occurrence_to_term` the resolver and `proof_verify` use). The intern is paid ONLY where the alternative was an error — natives, `Value::Term`s, literals and name occurrences all key without touching the store, so no `Map.get` that worked before now writes to it, which is the cost this ticket removed from the drain and is not reintroducing.
  2. `option_string_arg` (anthill-stl) widened its INNER `str_arg` and left its outer scrutinee matching `Value::Entity` alone, so a rule-body-bound `some(…)` into `KB.sorts` failed on the exact carrier the inner read had just learned. Now one `TermView` read serves all three.
  3. `relation_project_run`'s spec column name was the last native-variant string read in `eval/builtins.rs`. Widened.
  4. `anthill-todo`'s `forge::string_field` hand-rolled `Value::Str` + `Value::Term(Const)` and missed the occurrence. Widened.
  5. A REAL REGRESSION I INTRODUCED: routing `bigint_neg` through `big_int_operand` smuggled a SORT widening in with a carrier one — `big_int_operand` accepts an `Int64` because the CONVERSIONS always did, but `neg` refused one and must keep refusing, or `BigInt.neg(5)` answers `-5` where it used to raise. Now reads `literal_big_int` directly, with the distinction stated at the site.
  6. THE OPTION DEFAULTING IS RESTORED rather than merely documented, and the review was right to push: "no corpus path reaches it" is a statement about this repo's fixtures, not about a user's KB. It now lives at the field READ (`absent_option_as_none`, called from both of `reflect_field_access`'s scans), which is where it should have been all along — `Value::Entity`, `Value::Term` and `Value::Node` receivers all answer `none()` for a declared-`Option[T]` field the value does not supply, where before only the entity did, and only because something upstream had filled it in. Both spellings of "does not supply" are handled: an ABSENT slot, and a PRESENT slot holding the loader's synthetic Var. A non-Option field is untouched in both directions — absent stays the loud "entity has no field", since widening that would turn a missing REQUIRED field into `none()`.
  7. `constructor_sub_values` destructuring an APPLIED occurrence was challenged as "a loud failure became a silent wrong binding". MEASURED, and the premise does not hold: a `Value::Term` over `Vec3(add(1,2), 0.0, 0.0)` has ALWAYS destructured here and bound `x` to the un-reduced `add(1,2)` (the old `Term::Fn` arm handed each child back with no reduction), and the bridge's own normalizer agreed — `handle_to_native` returns a non-constructor application UNCHANGED. So the old rule was never "an un-reduced child does not bind"; it was "the occurrence carrier does not destructure", which is exactly the cross-carrier disagreement WI-1025's own comment calls a hazard. Kept, with that reasoning written at the site.

