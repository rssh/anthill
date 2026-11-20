## Attributes

- id: WI-20260903-2VPHT-an-op-effects-type-mismatch
- created: 2026-09-03T13:20:57Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-20T23:50:38Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN `op-effects` TYPE MISMATCH NAMES ITS OPERATION BY SHORT NAME, SO TWO SORTS' FINDINGS ARE ONE SENTENCE.

MEASURED on the WI-20260903-2M5XR tree. Two sorts in ONE file, each with an `operation div` whose body raises `Error[DivisionByZero]` and declares no effects:

  namespace zzprobe
    sort Money  … operation div(a: Money, b: Money) -> Money = Money(cents: a.cents / b.cents) … end
    sort Cash   … operation div(a: Cash,  b: Cash)  -> Cash  = Cash(cents:  a.cents / b.cents) … end

Both report:

  type mismatch in div.effects (op-effects): expected declared: [], got undeclared effect: Error[T = DivisionByZero]

BYTE-IDENTICAL, and the diagnostic carries NO SPAN. So the two findings are indistinguishable to the reader: which sort is `div` on? Is there one problem or two? Nothing in the message answers either question.

THE CONTROL IS IN THE SAME BATCH, and it is what makes this a defect in THIS message rather than a general limitation. The provider-coverage errors for the same two sorts DO name their carrier —

  'zzprobe.Money' provides 'anthill.prelude.EuclideanDomain' but backs no operation …
  'zzprobe.Cash'  provides 'anthill.prelude.EuclideanDomain' but backs no operation …

— and are therefore two readable, separable findings. The effects message is the one that does not say what it is about.

THE NAME COMES FROM `local_name_of` (`typing.rs`, `TypeErrorContext::name`), which is the SHORT name; the sort that owns the operation is known at the raise site and dropped.

WHY IT MATTERS BEYOND READABILITY. WI-20260903-W9D4Z gave the load-error channel a batch-wide dedup keyed on what the reader sees. A span-less, subject-less sentence is the one shape where that key cannot tell "the same finding twice" from "two findings" — and it collapsed `Cash`'s away: the batch went 14 -> 8 with `Cash.div` and `Cash.mod` silently gone. That was caught by `/code-review` and answered by EXEMPTING unlocated errors from the dedup, which is a mitigation and not the repair: it means a genuine duplicate of this message is now printed twice, because the channel has no way to know it is one.

ACCEPTANCE. The message identifies its operation unambiguously — the qualified name, or the sort plus the operation — so the two sorts above give two distinct sentences. Then the W9D4Z channel dedup can be re-narrowed to include unlocated errors (its `dedup_rendered_load_errors` doc names this ticket as the owner and says what it would take back), and `wi_w9d4z_one_mistake_one_diagnosis_test`'s exemption rows change with it. Say which rows fail when the change is backed out, and check the assertion corpus: ~15 rows match on `in {op}.` shaped text and a qualified name will move them.

NOTE THE SPAN, SEPARATELY. This diagnostic has none at all, which is why it cannot be told apart by position either. If the raise site can reach the operation's declaration span, carrying it would fix the identity question independently of the wording — and would let the dedup key work on it as it does on every other located error. Either repair satisfies the acceptance; doing both is better.

Raised by `/code-review` (high) on WI-20260903-2M5XR, and confirmed by the measurements above rather than taken from the report.

## Changes

### 2026-11-20T23:36:17Z — feedback — user

MEASURED FIRST on 20107e7a with the debug CLI (2026-11-20): the ticket's two-sort program printed 'path: type mismatch in div.effects (op-effects): expected declared: [], got undeclared effect: Error[T = DivisionByZero]' twice, byte-identical, with no line:col. The span was missing because OpInfo.span is kb.functor_span(op), the first TERM the loader built with the operation's functor: an operation no clause writes as a term has none (a call in an op body or a rule body did not give one either). FIX: (1) TypeErrorContext::entity_name names OperationEffects by the operation's QUALIFIED name (every raise site of that context: the body mismatch, the pool-write refusal, Branch x External, the @[simp] rewrite gate, callback rows); the other operation contexts keep the local name. (2) the body's undeclared-effect mismatch and the pool-write refusal are reported at the body (body_node.span), as a default's mismatch already was at the default. Now: 'zz.anthill:6:50: type mismatch in zzprobe.Money.div.effects ...' and '11:47: ... zzprobe.Cash.div.effects ...'. Branch x External's expected no longer repeats the name (found by /code-review). THE W9D4Z DEDUP: the op-effects mismatch is located now, so it is deduped by the located key (one body incurring one label at two calls is one line). The unlocated exemption is KEPT, decided on measurement rather than re-narrowed: keying unlocated errors on their sentence fails wi_0rp29_nested_projection_value_in_type_test::a_call_site_bracket_reaches_the_fallback_contradicted, whose let-annotation mismatch ('type mismatch in r.annotation (let-binding)') is unlocated and names the variable, not its operation, so two operations' copies read alike. The exemption is now held on the function by load::unlocated_exemption_tests (2 rows, with a located control). The misplaced W9D4Z doc (attached to drop_derived_member_cascades) moved onto dedup_rendered_load_errors. ROWS: wi_w9d4z D rewritten (one_body_incurring_one_label_twice_is_one_diagnosis: one line each for div and mod, at the body), D2 rewritten (two_sorts_sharing_an_op_name_are_two_findings: two qualified sentences, each at its body, provider control checked by its own text); wi_809jn a_write_through_a_knowledge_base_value_is_refused asserts each pool-write refusal at its body and qualified; 10 assertions on 'in {op}.effects' text moved to qualified names (wi733 x2, wi_0rp29 x2, wi_450ka, wi_6mpn2 x3, plus W9D4Z's). Guardians README excerpts updated to the printed output. BACK-OUTS over the whole anthill-core (11356 tests), one optimized build, a run-time switch each: control 0 fail; the qualified name backed out 9 (wi733 x2, wi_0rp29 x2, wi_450ka, wi_6mpn2 x2, W9D4Z D and D2); the body span backed out 2 (W9D4Z D and D2) and, separately, the pool-write span alone fails the wi_809jn row; the unlocated key 2 (the unit row and the wi_0rp29 row); the dedup returning its input 17 (W9D4Z A, C, D, the unit control, 13 rows in other files). Families green on both carriers, no verdict moved. /code-review high: 5 findings, 1 fixed (Branch x External named twice), 1 no change (location is the body start, not the incurring call: incurred effects carry no per-call span), 3 skipped: OpInfo.span is still functor_span for the OperationMatch diagnostics and the signature projection errors (OperationArgument/Return/Effects), and eliminate_declared_row_projections / check_branch_external_exclusion still read functor_span, all unlocated where nothing writes the op as a term; the root is a declaration span per operation, which moves many diagnostics' locations; and the let-annotation mismatch above is unlocated and subject-less (pre-existing).

