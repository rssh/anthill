## Attributes

- id: WI-20261016-YM8HD-071-c-error-reify-requires
- created: 2026-10-16T14:51:24Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-23T23:02:12Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261016-SQZPQ-071-b-typepattern-and

- tags: proposal-071

## Description

071 (c): `Error.reify` REQUIRES `TypePattern[T = T1]`, AND `ErrorTag` IS RETIRED. Proposal 071 §1.4.
THE CHANGE: `operation reify[Rho, X, T1](…) requires TypePattern[T = T1]`; the boundary calls `TypePattern.admits` with the raised value's type — its head sort as a type until stage (d) — instead of reading the `TypeValue` sub-dictionary of `ErrorTag`'s evidence by position (`ErrorLayer::reify_payload_sub`). Every verdict is unchanged. Retired with it: `sort ErrorTag`, `Error provides ErrorTag[T = T] :- TypeValue[T = T]`, `is_error_tag_spec` and every gate that reads it (the rule-body refusal that is the marker exemption's exception, `former_repair`'s and `library_instances`' arm, the bridge's absence), and WI-20260908-9WVT7's finding F1.
MEASURED (2026-10-16, F1): `sort Wrapper … provides ErrorTag[T = Boom]` is selected over `Error`'s row and carries no `TypeValue`, so every `Error.reify` at `Boom` dies at run time; `provides ErrorTag[T = (a: Int64, b: String)] :- TypeValue[T = Other]` makes the tuple's boundary catch `other(n: 7)` (exit 11, where 22 is right).
ACCEPTANCE (cargo-test via rustland/scripts/test.sh, scaland sbt testFull): the reify rows re-pointed and their verdicts unchanged; `ErrorTag` named in a program is an ordinary unresolved name; F1's two programs no longer reach a boundary through a written row; the rule-body refusal of an unbuildable slot still refuses, now through `TypePattern`.

## Changes

### 2026-10-23T23:02:10Z — feedback — user

Delivered 2026-10-24 (6373227e, merged with origin/main in 73d1ca41). Proposal 071 stage (c): `Error.reify` requires `TypePattern[T = T1]`, and `ErrorTag` is retired — the sort, `Error provides ErrorTag :- TypeValue`, `is_error_tag_spec` and every gate reading it (the rule-body refusal, `library_instances`' and `former_repair`'s arms, the bridge's absence marker).

THE BOUNDARY: it keeps what answers `TypePattern.admits` for the dictionary its call is handed, resolved where it is installed — the dictionary must be the one row's (`impl` = `TypeValuePattern`; a marker refused with its own account; anything else `ReifyPayloadUnread`, before the thunk runs), and the row's member is resolved once per interpreter (`ErrorLayer::admits_member`). A raise asks each boundary, innermost first, after discarding the raise's dead frames above it (`ActivationStack::discard_above_boundary`), with the raised value's head sort as a type, its arguments left out, until stage (d). A payload whose sort cannot be read is admitted by none. Every verdict of the reify rows is unchanged. An `ErrorLayer` that finds `reify` but disagrees with the rest of the stdlib panics at interpreter construction instead of going silent.

THE TYPER: a rule-body call that builds no pattern evidence is refused by the rule-body gate any spec with a member gets (TypePattern is no marker; its one row is written for every T). Where the call pins every element it gets an operation body's account: a tuple, the structural former's; a ground goal no row answers (a spec payload, a collection whose element is open), the unprovided one. The generic advice says how a rule body pins an element. The TypePattern repair text adds "for an `Error.reify`, raise a value of one in the thunk".

DECIDED WITH THE USER (2026-10-23): the bridge keeps no absence marker for an unpinned pattern slot (071 §2's sentence revised; the boundary's account names the two routes that hand none); a catch whose pattern is written at the call, `Error.catch(pattern, body)`, the typer discharging what the written pattern admits, recorded as 071 §7 open question 5 (note on WI-20261016-BDVYW); proposal 055 amended by 071 (`List[T = ?]` is `List` in an operation body, measured; `type_admits` is §7's anticipated reflect operation). Spec: kernel-language §5.4, §5.7, §8.7 (approved).

TWO /code-review ROUNDS. Round 1 (12 findings): fixed — a stand-in passing the install check, a raise at the depth cap's last frame lost to the question (measured: only where the raise stands at the deepest frame), dispatch repeated per raise, the raised type built per boundary, reify repairs, stale docs, a test that could not observe "before the thunk runs" (now a host counter), the 5G28A note; not reachable, measured — a rule-body function-value reify (a fix moved no verdict and was reverted); user's decision — the marker. Round 2 (10): fixed — a sort writing `provides TypeValuePattern[T = P]` passed a transitive "provides TypePattern" check (`RowCatcher` row), silent `None` in `ErrorLayer`, "this call pins no element" told to a fully pinned call, per-reify resolution, per-raise clones, docs; probed, verdict unchanged — an unjudged pair at the boundary; narrowed in the comment — evidence beneath the dictionary (a host stand-in for `TypeValue[T]`) read only when a raise asks.

ROWS: rustland/anthill-core/tests/include/wi_ym8hd_reify_type_pattern_test.rs (7); the reify rows of wi_9wvt7_error_reify, wi_9wvt7_reify_rule_body (a spec-payload shape added), wi_9wvt7_review5, wi_n31xx, wi_hxgxf, alias_written_name, wi869 re-pointed. BACK-OUTS, each alone, measured: the boundary's test answering true (11 rows, the narrowing ones) and false (34); the install check (the stand-in row's three host rows); the frame discard (the depth-cap row); the rule-body former and unprovided arms (the shapes row); `ErrorTag` put back (the unresolved-name row).

RUNS on the merged tree: rustland/scripts/test.sh 10606 passed, 0 failed; scripts/families.sh holds, no verdict moved; scaland sbt testFull 748 + 47 + 1 passed, 0 failed.

