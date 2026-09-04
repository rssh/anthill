## Attributes

- id: WI-20260904-QQPQ2-a-multi-binder-lambda-in-a
- created: 2026-09-04T14:24:49Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-04T17:11:14Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a multi-binder lambda in a rule body loads and is never applied

DIAGNOSED AND FIXED 2026-09-04. The lambda was never the subject: A TUPLE COULD NOT BE
DESTRUCTURED ON ANY CARRIER BUT `Value::Tuple`.

THE MECHANISM, measured. `bridge_op_to_eval` (kb/resolve.rs) hands a bridged operation
each operand ON THE CARRIER THE RESOLVER PROVED IT ON, so a written `(a: 1, b: 2)`
reaches the callee as a `Value::Node` occurrence, not a `Value::Tuple`. Every tuple read
in eval went through `Value::tuple_components`, which matched `Value::Tuple` and answered
`None` for everything else — and `None` there is not "not a tuple", it is
`match_tuple_pattern` DECLINING, which `enter_closure` turns into a raised
`Error[MatchFailed]`, which the bridge residualizes. The rule floundered: one solution,
NOT DEFINITE, `?r` unbound. Instrumented at the bridge, the raise was
`match_failed(<the Tuple pattern>, <the TupleLit occurrence>)` — pattern and scrutinee
side by side.

THE TICKET'S ROW WAS ONE OF FOUR, and the census is the reason the fix is at the ACCESSOR
and not at the lambda. All four red before, all four green after:

  apply2(lambda (a: Int64, b: Int64) -> a + b, (a: 1, b: 2))    a closure param pattern
  match p case (x, y) -> x + y            over a named tuple    a match arm
  let (x, y) = p                          over a named tuple    a let binder
  match p case (x, y) -> x + y            over a POSITIONAL one the other gate side

`spread_eta_args` — `tuple_components`' SECOND consumer, the OPERATION spelling of the
same destructure — is repaired by the same edit and is driven by its own row.

THE FIX. `Value::tuple_components` now takes a `&KnowledgeBase` and reads a non-native
carrier through `TermView`, gated on the functor DENOTING `TupleLiteral` via
`desugar_target::is` (the shared owner of the three carrier spellings). `TupleComponents`'
two halves became `Cow`, so the native carrier still borrows and allocates nothing. This
is `constructor_sub_values`' repair (WI-20260827-3ZNBC) on the sibling reader.

AT THE ACCESSOR, NOT AT THE TWO CALL SITES, and the reason is written at
`TupleComponents::by_label_index`: it is documented as the ONE rule the two readers must
agree on, and a per-site fallback would have left the NEXT reader with the
`Value::Tuple`-only answer — the shape this repo keeps paying for.

THE CARRIER IS NORMALIZED, NOT FORWARDED, and that took a SECOND back-out to justify. A
positional `(1, 2)` is `Tuple { pos: [1, 2], named: [] }` natively while its occurrence
twin is ALL-NAMED with the synthetic `_1` / `_2` labels (convert.rs's `TupleLiteral`
build; the parser refuses a mixed literal, so exactly one half is ever populated).
Forwarding as-is makes the two carriers disagree about `is_name_keyed`, which GATES the
by-label arm. So the `_N` half is put back in `pos`, through
`TupleComponents::labels_are_positional` (WI-790's owner) rather than an open-coded test.

TWO BACK-OUTS, MEASURED SEPARATELY:

  A  the non-native arm restored to `_ => None`
       -> 8 of 11 rows fall. The three that stand are the two operation-body CONTROLS
          (never leave `Value::Tuple`) and the eta known-gap row (fails earlier).
  B  the view's halves forwarded, no `_N` renormalization
       -> EXACTLY ONE row falls, and finding it took writing a second fixture: the
          obvious positional row is GREEN under B, because its own pattern labels are
          synthetic too and gate the by-label arm off from the other side. The row that
          decides is a POSITIONAL literal reaching a NAME-KEYED declared parameter
          (`named_match((1, 2))`) — 3 with the normalization, one FLOUNDERED without it.

TWO GAPS THE CENSUS FOUND, both PINNED as rows rather than left to be rediscovered:

  1. AN OPERATION NAME IN A RULE-BODY FUNCTION SLOT IS NOT CALLABLE — `apply1(inc1, 2)`
     dies `UnknownOperation { name: "<ns>.apply1.f" }` before any argument is read, and
     reproduces at ONE parameter where no tuple exists at all, so `spread_eta_args` is
     never entered. A DIFFERENT root, measured and not assumed; filed as
     WI-20260904-833DK.

  2. A RULE-BODY LAMBDA'S BINDERS ZIP A PERMUTED NAMED TUPLE BY SLOT, and this ticket is
     what makes it VISIBLE — before the repair that program had no answer at all, now it
     has a WRONG one:

       rule  apply2(lambda (a: Int64, b: Int64) -> a - b, (b: 2, a: 1))   ->  1
       op    apply2(lambda (a: Int64, b: Int64) -> a - b, (b: 2, a: 1))   -> -1
       rule  named_sub((b: 2, a: 1))       -- a `match` pattern, same carrier    -> -1

     THE CAUSE IS ON THE PATTERN SIDE, MEASURED, NOT THE CARRIER SIDE: a tuple pattern
     takes its labels from the EXPECTED type (`bind_and_label_pattern`, WI-803) and a
     lambda in a rule-body DATA slot receives no expectation — the same `None` that
     leaves WI-20260904-50B2K's rung 2 unreachable. With no labels the matcher zips in
     source order, and the value's source order is the LITERAL's. `match` / `let` are
     unaffected: their labels come from the operation's DECLARED parameter type. OWNED BY
     50B2K PART (b), and recorded on that ticket.

     The trade is stated rather than hidden: the four rows the repair buys all write
     their components in declaration order, where slot and name agree.

TEST: `rustland/anthill-core/tests/include/wi_qqpq2_tuple_carrier_test.rs`, 11 rows —
four capability rows, one back-out-B driver, the spread reader, a by-name control, two
operation-body controls and the two known gaps.

/CODE-REVIEW (high) — THREE FINDINGS ON THIS CHANGE, all addressed; four more landed on
the ALREADY-COMMITTED 50B2K tree and are recorded on that ticket.

  * THE NAMED LOOP WAS SILENT WHERE ITS POSITIONAL SIBLING WAS LOUD. A key `named_keys`
    itself had just yielded that `named_arg` does not read back returned `None` for the
    whole accessor — and `None` here MEANS "not a tuple", so it reaches
    `match_tuple_pattern` as a declined match and residualizes: the very failure this
    change removes, re-introduced quietly. Now a `debug_assert` + `return None`, the
    same stance as the positional loop ten lines up.

  * THE MIXED CARRIER WAS AN ASSUMPTION, NOT A RULE, and the reviewer measured why that
    was thin: parse REFUSES `(1, b: 2)` but REPORTS AND CONTINUES, folding the
    positionals in after the named ones — so the shape is reachable past a load error
    rather than impossible. The all-or-nothing gate is gone: `labels_are_positional` is
    now asked about the SYNTHETIC SUBSEQUENCE, so `(1, b: 2)` reconstructs as
    `pos: [1], named: [(b, 2)]` — exactly the native layout — with one rule and no
    exception. NOT DRIVABLE (the literal is refused), and the site says so.

  * THE BY-SLOT GAP NEEDS A REAL OWNER, not only a name in a doc comment. Checked:
    WI-20260904-50B2K is CLAIMED with part (b) listed as not done, and the measurement
    is now written into that ticket beside it.

ACCEPTANCE: full rust suite 6420 passed / 0 failed (36 result lines); scaland
`sbt test` 539 passed / 0 failed (untouched — scaland has no evaluator to port this to).

