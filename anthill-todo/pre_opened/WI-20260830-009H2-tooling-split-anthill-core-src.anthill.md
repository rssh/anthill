## Attributes

- id: WI-20260830-009H2-tooling-split-anthill-core-src
- created: 2026-08-30T12:27:54Z

- status: PreOpened
- status_agent: claude
- status_at: 2026-08-30T12:30:11Z

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

