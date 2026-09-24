## Attributes

- id: WI-20260924-R97NK-a-public-alias-of-an-internal
- created: 2026-09-24T14:36:26Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T14:36:26Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing, resolution, visibility

## Description

A PUBLIC ALIAS OF AN `internal` SORT REACHES IT FROM OUTSIDE. `namespace lib` with `internal sort Hidden` and `sort PubAlias = Hidden`: another namespace can `provides PubAlias[State = WIS]` and require it (since F8PYZ), and — before F8PYZ already — write `x: lib.PubAlias` in a type position, while `provides lib.Hidden[…]` / `x: lib.Hidden` are refused "'lib.Hidden' is internal to 'lib'". Measured by F8PYZ's review. DECIDE: is a public alias a legitimate RE-EXPORT of an internal sort (then say so in the spec and keep it), or a leak — refuse a public alias whose target is `internal` at the declaration (the "private type in public interface" rule), or refuse a use whose alias target the citing scope may not see? ACCEPTANCE: the decision driven by a test in each position (type, spec clause), with the direct spelling as the control.

