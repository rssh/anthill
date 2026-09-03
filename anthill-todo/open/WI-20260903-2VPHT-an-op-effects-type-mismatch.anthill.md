## Attributes

- id: WI-20260903-2VPHT-an-op-effects-type-mismatch
- created: 2026-09-03T13:20:57Z

- status: Open
- status_agent: claude
- status_at: 2026-09-03T13:20:57Z

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

