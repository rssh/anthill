## Attributes

- id: WI-20260830-009H2-tooling-split-anthill-core-src
- created: 2026-08-30T12:27:54Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-30T15:43:59Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TOOLING: split `anthill-core/src/kb/typing.rs` (72451 lines / 3.7 MB) into modules — and state up front what that does NOT buy.

WHY NOW. `cargo fmt` over this crate is UNRUNNABLE: rustfmt reaches ~15.3 GB anon-RSS on
`typing.rs` and is OOM-killed, taking the whole 15.7 GB WSL VM with it. MEASURED 2026-08-30,
three times in a row (`journalctl -b -1 | grep "Killed process"`:
`Killed process 29945 (rustfmt) anon-rss:15209636kB`, and two more). `rustc`, `rust-lld` and
`cargo` were killed ZERO times across both crashed boots — the compiler is fine, the
formatter is not. So the crate is currently formatted by hand, and nothing can check it.

WHAT A MODULE SPLIT BUYS, precisely:
  * rustfmt becomes runnable again, IF the pieces land under the blow-up threshold — which
    is NOT KNOWN. `load.rs` is 1.6 MB and has never been measured; find the threshold FIRST
    (run rustfmt on a copy under `(ulimit -v 4000000; ...)` at several sizes) or the split
    ships without knowing whether it achieved its own goal.
  * navigability: 72451 lines is past what any editor, reviewer or search tool handles.

WHAT IT DOES NOT BUY, and this must not be discovered halfway:
  * NOT compile time and NOT link time. rustc compiles per CRATE. A module split leaves every
    edit invalidating `anthill-core` and relinking all 79 test targets exactly as today (the
    link storm `rustland/.cargo/config.toml`'s `jobs = 6` exists to cap). Only splitting into
    separate CRATES changes that, and that is a different, much larger ticket: the typer
    shares private state densely (`TypingEnv`, `check_apply_iter`, and several hundred free
    helpers), so crate boundaries need real design, not a file move.

COST / SEQUENCING. The change is mechanical but touches 72451 lines and every `fn` is
currently a private free function in ONE module — the split means choosing boundaries and
adding `pub(crate)` + `use` across all of them. The diff collides with EVERY in-flight ticket
against `typing.rs`, which is most typer work. So: land it when the typer queue is quiet, in
one commit, and do not mix it with any behaviour change.

SUGGESTED BOUNDARIES (a starting point, to be checked against the actual call graph, not
adopted on faith): the apply/dispatch path (`check_apply_iter` and its arm helpers), the
provision/carrier readers (`carrier_param_receiver`, `transitive_provision_view`,
`bind_spec_params_from_*`, `*_provision_bindings`), the requirement/dictionary machinery
(`op_requires_*`, `build_*_dicts`, `DictChain`), unification + rows, the diagnostics
(`TypeError` and its rendering), and the operation-body driver.

ACCEPTANCE: no behaviour change — full workspace cargo-test green with byte-identical
diagnostics; `wc -l` of the largest resulting file recorded in the delivery note; and the
rustfmt threshold MEASURED and stated, so the note says whether `cargo fmt` is usable on the
result or still is not. If it still is not, say so — a split that misses its own goal and
claims success is worse than none.

## Changes

### 2026-08-30T12:30:01Z — feedback — claude

SCOPE CORRECTED SAME DAY, and the ticket is much weaker than it was filed as. It was filed
on the premise that `cargo fmt` is unrunnable on this crate. That is now FIXED at the tool,
not by moving code: `rustland/rustfmt.toml` carries `ignore = ["src/kb/typing.rs"]`.

VERIFIED SAFELY (under `ulimit -v 4000000`, so a blow-up would kill rustfmt alone rather
than the VM): `cargo fmt -p anthill-core -- --check` now runs the WHOLE crate to completion
inside a 4 GB address-space cap, and `typing.rs` appears ZERO times in its output.

THE PROBLEM WAS RUSTFMT, NOT THE FILE SIZE — the user's point, and it is right. Splitting
would not fix rustfmt; it would only move the threshold, and it would do so at the cost of a
72451-line reshuffle colliding with every in-flight typer ticket. The ignore is the fix and
it is enforcement rather than a thing to remember.

WHAT THE MEASUREMENT ALSO SHOWED, since it bounds any future attempt: `load.rs` at 1.6 MB
formats fine INSIDE the same 4 GB cap. So the blow-up is not "big files" — it is specific to
`typing.rs`, and the threshold lies somewhere between 1.6 MB and 3.7 MB. A split aiming at
rustfmt would have to land every piece under a bound nobody has measured; this ticket said
to measure it first, and that advice is now the whole of what it would have bought.

WHAT REMAINS, and it is the only reason left to want this: NAVIGABILITY. 72451 lines in one
file is past what an editor, a reviewer, or a search handles well. That is a real cost and a
recurring one, but it is a comfort argument, not a correctness or tooling one, and it should
be judged as such — against a mechanical diff over the whole file that cannot be reviewed
meaningfully and that blocks concurrent typer work while it lands.

RE-READ THE "DOES NOT BUY" SECTION BEFORE CLAIMING THIS: a MODULE split still leaves every
edit invalidating `anthill-core` and relinking all 79 test targets, because rustc compiles
per crate. There is no build-time win in it at all.

RECOMMEND: keep OPEN but PRE-OPEN it (backlog) unless someone wants the navigability for its
own sake. Nothing is blocked on it any more.

### 2026-08-30T15:43:09Z — feedback — claude

DELIVERED, but this ticket was wrong on BOTH of its premises, and the corrections are the
substance of the delivery. Read them before reusing anything this ticket asserted.

=== 1. WHERE RUSTFMT ACTUALLY EXPLODES: `--check`, not formatting, and not file size ===

The blow-up is in the DIFF EMITTER, reached only by `--check`:

    memory allocation of 20121126480 bytes failed
      10: diff::lines
      11: rustfmt_nightly::rustfmt_diff::make_diff
      12: <DiffEmitter as Emitter>::emit_formatted_file

`--check` runs an LCS diff of input against formatted output and the `diff` crate builds a
dense O(n x m) table. typing.rs was 72451 lines in / 72564 out with ~641 differing lines
SCATTERED through the file, so the common prefix/suffix trim removed almost nothing:
~70924^2 x 4 bytes = 20,121,126,480 — the panic's own number, to the byte.

Same file, same rustfmt, three emitters:

    rustfmt --emit stdout    87 MB   0.60s    fine
    rustfmt --emit files     87 MB   0.60s    fine  <- this is what plain `cargo fmt` uses
    rustfmt --check          20 GB alloc      OOM

So "cargo fmt over this crate is UNRUNNABLE" was FALSE. Plain `cargo fmt` was never broken.
Only `cargo fmt -- --check` was.

TWO SPECIFIC CLAIMS IN THIS TICKET ARE REFUTED:

  * "it is superlinear in that size" (the rustfmt.toml comment this ticket quoted) — NO. A
    prefix ladder cut at item boundaries, 780 KB -> 3.65 MB, is dead LINEAR and fast:
    48 MB / 0.17s, 55/0.26, 61/0.32, 67/0.40, 75/0.39, 80/0.55, 84 MB / 0.57s. The whole
    3.87 MB file formats in 0.70s / 87 MB.

  * The 2026-08-30 feedback's "load.rs at 1.6 MB formats fine ... so the threshold lies
    somewhere between 1.6 MB and 3.7 MB" — NO. There is no size threshold. load.rs reaches
    2.6 GB on `--check`; it "formatted fine" only because 2.6 GB fits inside the 4 GB cap
    that measurement used. It is on the same curve, not off it.

THE IGNORE WAS LOAD-BEARING FOR THE BOMB, NOT AGAINST IT. The cost is quadratic in the
DIFFERING span, so an ignore that keeps a 72k-line file hand-formatted is precisely what
makes `--check` explode on it. Formatted, `--check` on that same file costs 92 MB / 0.45s.

=== 2. THERE IS NO NATURAL MODULE SPLIT. MEASURED, NOT ASSUMED. ===

Call graph over the 1001 free functions: 2558 undirected edges, average degree 5.1.

  * Label propagation puts 903 of 1001 functions — 93.7% of the lines — in ONE community.
    Only 3.3% of call edges cross community boundaries. The rest is a long tail of 2-7
    function satellites.

  * The six boundaries this ticket SUGGESTED overlap 79-100% in transitive reach:
        apply/dispatch      reaches 621 fns / 34900 lines
        provision/carrier   reaches 363 fns / 16560 lines
        requirements/dicts  reaches 391 fns / 18236 lines
        unify/rows          reaches 328 fns / 15164 lines
        op-body driver      reaches 761 fns / 45224 lines
        build_type          reaches 740 fns / 43469 lines
    273 functions / 12354 lines are reachable from EVERY ONE of them.

  * Strongly-connected components are small (largest 47 fns), so it IS a DAG and a
    MECHANICAL layered split is possible. But there is no semantic seam: the result would be
    a `common.rs` plus arbitrary layers, which is not what the ticket asked for and not worth
    the collision.

So the full split was NOT done, and should not be filed again on the navigability argument
without confronting these numbers.

=== 3. WHAT WAS ACTUALLY DONE ===

(a) Extracted the 26 `#[cfg(test)]` modules to `anthill-core/src/kb/typing/tests.rs` — the
    one genuinely clean cut. 5171 lines of content under a 21-line header, INCLUDING 179 lines
    of outer doc comment belonging to 14 of those modules. Moving the modules without their
    doc comments orphans the comments and the crate stops parsing; that was hit for real and
    fixed, and the extraction now asserts a blank line precedes every block it lifts.

    TWO things changed in the moved text: one extra `super::` hop (`super::super::`), because
    the modules are children of `typing::tests` rather than of `typing` — a descendant may
    still name its ancestors' private items, so nothing needed to be made public — and the
    `cargo fmt` pass that followed, which re-wrapped some of it. A diff of the moved text
    against the pre-split file therefore shows reflow as well as the hop.

(b) Removed `ignore = ["src/kb/typing.rs"]` from `rustland/rustfmt.toml` and replaced its
    comment with the diagnosis above. The file now sets NO options and exists for the comment.

(c) Formatted all of `anthill-core/src/` (21 files). This was chosen over formatting only
    typing.rs because that narrower fix leaves `--check` at 2.7 GB — load.rs is the culprit.

=== 4. NUMBERS ===

    typing.rs        72451 -> 67402 lines     <- largest resulting file, as acceptance asked
    typing/tests.rs                5192 lines
    98 `#[test]` fns moved; all 98 register under `kb::typing::tests::`

    cargo fmt -p anthill-core -- --check :  20 GB OOM  ->  266 MB / 2.7s

FULL WORKSPACE SUITE GREEN: 36 test binaries, 6172 passed, 0 failed (both tiers of
`rustland/scripts/test.sh`, log `target/test-run-20260830-151226.log`).

LOSSLESSNESS, verified rather than assumed: the non-blank line MULTISET of the original file
equals that of (new typing.rs + tests.rs) after undoing the super:: hop and the added header
— 70549 = 70549, ZERO lines lost, ZERO gained.

THE CONTROL THAT MAKES THE TEST RUN MEAN ANYTHING: `cargo test -p anthill-core --lib -- --list`
before and after the move, sorted, with the `tests::` infix normalised away — the two lists are
BYTE-IDENTICAL at 570 tests. A green suite alone would not have shown this: the failure mode of
a bad `mod tests;` is that the modules silently stop being compiled, and a suite that no longer
contains them still passes.

=== 5. WHAT IS NOT DONE, so silence is not read as success ===

  * NAVIGABILITY IS BARELY IMPROVED. typing.rs is still 67402 lines. The tests were 6.8% of
    it. If navigability is the goal, this delivery does not achieve it and section 2 says why
    the obvious next step does not either.

  * `cargo fmt -p anthill-core -- --check` STILL EXITS 1 at 266 MB / 2.2s. 118 files under
    `anthill-core/tests/` remain unformatted (115 in `tests/include/`, plus `wi_tests.rs`,
    `guardians_test.rs`, `common/mod.rs`), so it is safe to run and NOT yet a CI gate. Making it one was measured
    (139 files, net -3745 lines) and deliberately declined here to keep this change off every
    in-flight test branch.

  * NO BUILD-TIME WIN, exactly as this ticket's own "DOES NOT BUY" section said. rustc
    compiles per crate; every edit still invalidates anthill-core and relinks all test targets.

=== 6. CODE REVIEW (/code-review medium) ===

No correctness bugs. The reviewer did not take the diff on trust: it rebuilt HEAD's `src/`
into a temp tree, ran rustfmt over it, and proved every changed file EXCEPT typing.rs is
byte-identical to `rustfmt(HEAD)` — so no hand edit is hiding in the 5825-line deletion — then
checked typing.rs's own diff down to 6 added lines (the `mod tests;` stanza) and 5166 deleted
(the 26 module bodies), and confirmed all 26 bodies arrived faithfully.

It raised three documentation-accuracy defects, all introduced by me, all now FIXED:

  * `tests.rs` claimed the ONLY edit to the moved text was the `super::` hop. False: the
    `cargo fmt` that followed also re-wrapped it, visibly in four modules. The header now says
    so, because that claim's whole purpose is to let a future reviewer tell reflow from a real
    edit — and as written it would have made that harder, not easier.
  * `typing.rs:43094` pointed at `wi802_function_spec_owner_tests` "at the end of this file".
    It is no longer in that file.
  * The header's "5124 lines" was measured BEFORE the formatting pass and did not match the
    shipped file.

ONE MORE, FOUND BY RE-CENSUSING WHAT THE REVIEW REPORTED: the review named :43094 as the only
wrong locality claim. Grepping all 9 references to moved modules for locality phrasing found a
SECOND — line 62303's "ITS COVERAGE IS THE UNIT TEST BESIDE IT", which stopped being true for
the same reason. Fixed. The review's list was a lower bound, not the population.

