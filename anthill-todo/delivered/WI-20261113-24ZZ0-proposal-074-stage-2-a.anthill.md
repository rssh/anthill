## Attributes

- id: WI-20261113-24ZZ0-proposal-074-stage-2-a
- created: 2026-11-13T23:01:18Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-20T22:26:42Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 2 — A CONSTANT HOLDS A DICTIONARY (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§2; T12). `const ints: Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()` is folded at load, and `add2(ints, 2, 3)` answers 5. Today: "const has a non-foldable body". A constant at an application stage 1 refuses is refused as there. Its value in a data slot is not part of the stage (§2, "In a rule body"). Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

## Changes

### 2026-11-20T21:47:25Z — feedback — user

MEASURED FIRST on 5175d999 with the debug CLI (2026-11-20). T12 runs already: const ints: Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]() and add2(ints, 2, 3) answer 5, as do the bracket left to the declared type (= Dictionary.instance()), the const named dotted (C.ints), a const naming another, a let over it, a lambda over it, T2 through two consts, a provider named by a key in the const (Tag = Alt answers 2 beside Leaf's 1), and Tag.tag(leaf(k: 0)) with altTag in scope and not passed answers Leaf's 1. The 'non-foldable body' of the proposal's 'today' predates stage 1 (2KSAA, 2026-11-14), whose built-in is effect-free and whose stamp the const's typed value carries. Every application stage 1 refuses is refused in a const, in stage 1's sentence (the 11 rows of dictionary_instance_refuses_what_has_no_dictionary). The C++ and Rust generators refuse the const loudly (no mapping for Additive; Rust: only literal const bodies). DEFECTS: (1) a query ?r <=> add2(ints, 2, 3) PANICS the CLI (bridged_value's debug_assert: add2's x handed a Node, not the instance), and ?r <=> ints answers the bare symbol ints: query_slot_const folds a computed const only to a literal and keeps the symbol otherwise; (2) a mismatch between two dictionaries of one spec, const k: Additive[T = Float] = Dictionary.instance[Additive[T = Int64]](), is refused with KSSA4's provider note ('Additive provides it, so its operations may be used on a value of Additive ... Type it Additive'), also in an op return, an argument and a let. A fact and a rule body naming the const are refused (computed body in a data slot), as section 2 has it. Pre-existing and general, not this stage: any computed non-literal const in a query is its symbol (?r <=> origin over const origin: P = pt(x: 4) answers origin) and a call over it is left undecided. DECIDED WITH THE USER (2026-11-20): a query naming a dictionary const is refused where it is read, as a rule body is, not evaluated.

### 2026-11-20T22:14:24Z — feedback — user

DONE, NOT COMMITTED (2026-11-20; spec text awaiting the user's approval). (1) A query naming a const that holds a dictionary (its declared type a sort of SortClass::Dictionary) is refused where it is read, bare or dotted, as an argument or as the value of <=> (load::query_data_slot_const, LoadError::DictionaryConstInQuery naming the const and its type), where it panicked the bridge and answered ?r <=> ints with the name; a rule body keeps its computed-body refusal (it converts mid-load, before a const's type is recorded). (2) callable::provider_at_a_spec_type_error gives no provider note where the found type is a dictionary: const k: Additive[T = Float] = Dictionary.instance[Additive[T = Int64]]() is the plain 'expected Additive[T = Float], got Additive[T = Int64]' in a const, an op return, an argument and a let. Rows (wi_2ksaa_dictionary_instance_test, 8): T12 (5, and the const prints Dictionary(impl: Int64)); read as any value (S from the declared type, dotted C.dict, const to const, a const computed from it, let, lambda, T2 through two consts); a key names the provider (1, 2) and a const not passed is not used (Leaf's 1); a const refused at every application of stage 1's table (NO_DICTIONARY, lifted and shared); the call fixes its type (add2(ints, 1.5, 2.5) refused; const k: Additive leaves ?T open); two dictionaries of one spec mismatch plainly; no value in a data slot (fact, rule body, three query spellings refused; controls: a literal const and held() through a query); a compound form reads it as an operation body does (let and if in a rule body and a query, 5). cpp-gen unsupported_test::a_dictionary_held_by_a_const_is_refused_until_stage_7 (the const's type refused; with Additive mapped, its value refused naming stage 7). Back-outs over the whole wi_tests (9683), one optimized build, a switch each: control 0 fail; query refusal 1 (the data-slot row); hint exclusion 1 (the mismatch row); stage 1's stamp skipped in a const's value 5 (every row answering a value). /code-review high: 6 findings, 1 fixed (an assertion tightened), 1 no change (the exclusion covers a witness without constructors too, rightly: its value is a dictionary), 4 skipped (the bridge still has no fold of a const node at a dictionary parameter, with no route left that reaches it; a dictionary nested in a const's type, List[T = Additive[...]], keeps its symbol in a query as every non-literal computed const does; a dictionary const as a query goal matches nothing, as any non-Bool const does; kernel-language 5.9's query exception says a computed const is evaluated there, true only where its value is a literal: pre-existing). Gate 12428 / 0 / 17 (36 binaries); families.sh green on both carriers, no verdict moved; scaland testFull 811 + 51 (2 skipped).

### 2026-11-20T22:26:40Z — feedback — user

DELIVERED (2026-11-20): committed f794036dd; kernel-language 5.9 and 8.2 approved by the user. Gate 12428 / 0 / 17; families green on both carriers; scaland testFull 811 + 51 (2 skipped).

