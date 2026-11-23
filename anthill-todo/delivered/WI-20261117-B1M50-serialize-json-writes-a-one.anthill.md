## Attributes

- id: WI-20261117-B1M50-serialize-json-writes-a-one
- created: 2026-11-17T06:16:08Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-23T16:27:35Z

- acceptance: cargo-test

## Description

SERIALIZE_JSON WRITES A ONE-FIELD ENTITY AS ITS BARE VALUE, AND LOAD_JSON REFUSES WHAT IT WROTE: `entity Acct(balance: BigInt)` with facts `Acct(balance: 5n)` and `Acct(balance: 123456789012345678901234567890n)` serializes to `{"data": [5, "123456789012345678901234567890"], "meta": {"entity": "…Acct"}}`, and term_ser::load_json of that text fails "data entry must be an object" for each entry (MEASURED 2026-11-16 while writing wi_5vm2g's JSON row, which uses a two-field entity to step around it). term_ser::facts_to_value unwraps the one-key object term_to_value makes of a fact (`{"Acct": fields}` → fields); for a one-field entity the value under the key is apparently the field's value rather than `{"balance": …}` — check term_to_value's single-field case, and whether TOML (serialize_toml / load_toml) has the same. ACCEPTANCE: a one-field entity round-trips through serialize_json → load_json and serialize_toml → load_toml (the facts back, field values with their declared types); a multi-field entity unchanged; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-23T16:27:33Z — feedback — claude

Delivered (closed with the user 2026-11-23): already fixed on HEAD, by WI-20261122-WC18Y (2ab7ca823). CAUSE, read off 2ab7ca823^: facts_to_value unwrapped every ONE-KEY object term_to_value made of a fact, taking it for the {"Acct": fields} wrapper; the object of a one-field entity's fields is one key too, so the row lost its field's name. WC18Y rebuilt the writer on Encoder::fields, which writes a row as the object of its fields whatever their number. MEASURED on 234cbe830: entity Acct(balance: BigInt) with 5n and 123456789012345678901234567890n round-trips through serialize_json -> load_json and serialize_toml -> load_toml, the facts back by hash-consed head identity and both balances BigInt; a single row (data written as the object itself), a one-field Option entity with the field omitted (none), and a two-field entity unchanged, likewise. GUARD: putting the old unwrap back in facts_to_value fails two existing rows whose fixtures write a one-key row, wi_wc18y_value_codec_test::a_data_file_is_one_use_of_the_pair (test.wc.H) and wi_jb6rs_type_face_test::a_type_in_the_json_store_reads_back_as_the_type ("data must be an array or object"); toml_ser_test passes either way. TOML goes through the same facts_to_value, so the JSON rows guard it. No new rows, by the user's decision: the measured rows were taken out, the two existing ones being the guard.

