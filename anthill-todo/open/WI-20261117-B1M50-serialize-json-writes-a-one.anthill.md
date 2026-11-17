## Attributes

- id: WI-20261117-B1M50-serialize-json-writes-a-one
- created: 2026-11-17T06:16:08Z

- status: Open
- status_agent: user
- status_at: 2026-11-17T06:16:08Z

- acceptance: cargo-test

## Description

SERIALIZE_JSON WRITES A ONE-FIELD ENTITY AS ITS BARE VALUE, AND LOAD_JSON REFUSES WHAT IT WROTE: `entity Acct(balance: BigInt)` with facts `Acct(balance: 5n)` and `Acct(balance: 123456789012345678901234567890n)` serializes to `{"data": [5, "123456789012345678901234567890"], "meta": {"entity": "…Acct"}}`, and term_ser::load_json of that text fails "data entry must be an object" for each entry (MEASURED 2026-11-16 while writing wi_5vm2g's JSON row, which uses a two-field entity to step around it). term_ser::facts_to_value unwraps the one-key object term_to_value makes of a fact (`{"Acct": fields}` → fields); for a one-field entity the value under the key is apparently the field's value rather than `{"balance": …}` — check term_to_value's single-field case, and whether TOML (serialize_toml / load_toml) has the same. ACCEPTANCE: a one-field entity round-trips through serialize_json → load_json and serialize_toml → load_toml (the facts back, field values with their declared types); a multi-field entity unchanged; full workspace green via rustland/scripts/test.sh.

