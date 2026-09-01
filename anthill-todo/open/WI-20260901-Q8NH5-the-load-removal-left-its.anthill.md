## Attributes

- id: WI-20260901-Q8NH5-the-load-removal-left-its
- created: 2026-09-01T14:11:01Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T14:11:01Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE `load` REMOVAL LEFT ITS PROSE BEHIND, AND THE RENAME THAT CAME WITH IT MADE SENTENCES
SELF-REFERENTIAL. Three doc sites describe an entry point that no longer exists and a gap
that no longer exists with it; 58 more carry a phrase a textual substitution broke.

FOUND BY /code-review on WI-20260821-P85Z7's diff, reviewing the unpushed commits behind
it. All are in commit 91aae403 (WI-20260901-Q68AK, "one loading pipeline with a named
option, not two entry points"), which is delivered, so none has an owner.

A. A DELETED ENTRY POINT IS STILL DOCUMENTED AS THE BOUNDARY, and readers are told it
   has a gap it cannot have:
    * `kb/load.rs:15336` -- `check_name_captures`: "which `load_all` / [`load_all` into
      a live KB] reach and the single-file [`load`] does not. So `load` sees no capture
      refusal". The boundary is now `LoadOptions { run_typer: false }`.
    * `kb/typing.rs:28080` -- and this one is LOAD-BEARING for the requires-index
      lifetime: "The single-file [`load`] entry point runs both of those and NO
      type-check, so it deliberately gets no build at all", closing with an explicit
      `(crate::kb::load::load)` intra-doc link that no longer resolves.
    * `kb/mod.rs:1253` -- the identical stale sentence for `requires_index`.

B. A SUBSTITUTION THAT ATE ITS OWN SENTENCE. `load_incremental` -> `load_all` was applied
   to comment prose textually, so a distinction between two names became a thing declared
   an alias of ITSELF:
    * `load.rs:1337`, `:4600`, `:4897` -- "`load_all` into a live KB is an alias of
      `load_all`"
    * `kb/mod.rs:1389` -- "a second `load_all` into a live KB into the same KB"
    * `intern.rs:566` -- "`load_all` into a live KB's second phase"
   58 sites carry the substituted phrase; not all are broken, so the work is to READ them,
   not to re-substitute.

WHY IT IS NOT COSMETIC. A doc naming an entry point is how the next ticket decides where
a check runs. WI-20260901-7ZZ1Z is already the case where a stale reading of `load`'s
stop point shipped a test asserting a refusal the real pipeline never makes.

ACCEPTANCE: no doc comment names `load` as an entry point or describes a gap keyed on it;
no sentence declares a name an alias of itself; every intra-doc link in the touched text
resolves (`cargo doc` clean for the crate, or the link removed). Say at each rewritten
site what the boundary IS now (`run_typer: false`), not merely that `load` is gone.
cargo-test green via rustland/scripts/test.sh.

