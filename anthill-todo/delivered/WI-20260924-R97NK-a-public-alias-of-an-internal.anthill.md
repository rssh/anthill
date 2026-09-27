## Attributes

- id: WI-20260924-R97NK-a-public-alias-of-an-internal
- created: 2026-09-24T14:36:26Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-27T23:00:55Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing, resolution, visibility

## Description

A PUBLIC ALIAS OF AN `internal` SORT REACHES IT FROM OUTSIDE. `namespace lib` with `internal sort Hidden` and `sort PubAlias = Hidden`: another namespace can `provides PubAlias[State = WIS]` and require it (since F8PYZ), and — before F8PYZ already — write `x: lib.PubAlias` in a type position, while `provides lib.Hidden[…]` / `x: lib.Hidden` are refused "'lib.Hidden' is internal to 'lib'". Measured by F8PYZ's review. DECIDE: is a public alias a legitimate RE-EXPORT of an internal sort (then say so in the spec and keep it), or a leak — refuse a public alias whose target is `internal` at the declaration (the "private type in public interface" rule), or refuse a use whose alias target the citing scope may not see? ACCEPTANCE: the decision driven by a test in each position (type, spec clause), with the direct spelling as the control.

## Changes

### 2026-09-27T23:00:42Z — feedback — user

DELIVERED. User decision (2026-09-27): refuse AT THE DECLARATION — an alias is no more visible than what it names. A public alias whose definition names an `internal` name hidden from outside (at any depth, by any leading part of a path, from any scope that can see it) is a load error, LoadError::PublicAliasOfInternal, raised once by Loader::refuse_public_alias_of_internal; the repair is `internal sort PubAlias = Hidden`, which works inside its scope and is refused outside like the sort it names. Spec: kernel-language §8.6 (and the §5.1 type-alias paragraph). Tests: wi_r97nk_public_alias_of_internal_test, 10 rows — type position and spec clause each driven inside the scope (go/go2 return 9/3), refused outside, with the direct spelling as control; back-out (check returns at once) fails exactly the four *_is_refused rows. cargo-test: full workspace via rustland/scripts/test.sh, 6176 passed, 1 failed — cmd_claim_test::claim_on_readonly_dir_raises_clean_error_not_panic, environmental (container runs as uid 0, chmod 0555 does not stop root). scaland-sbt-test: not run — scaland enforces no `internal` visibility; nothing under scaland/ changed. Measured gaps NOT closed: a path through an internal owner is ungated (`lib.Box2.Inner` under `internal sort Box2` loads outside); a public operation signature may name an internal sort.

