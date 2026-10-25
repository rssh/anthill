# Who supplies a call — the readers of one question

## Status: measurement, 2026-10-25, on `d6a28558`, re-measured on `1373e04f` after WI-20261025-ZAWX9 (`3657c39d`) gave the defaulted path one answer. The first map of "one answer per question" (`docs/process/converging.md` §3.10, q18). What is left — D1, D3 and D5, all on the body-less path — is WI-20261025-7K84M; D2 was ZAWX9; guarded by the family `f-supplier-routes`. Nothing here is implemented.

## The question

*Which implementation runs a call of a spec operation at a carrier?*

`docs/kernel-language.md` §8.7 answers it in three paragraphs:

- **Operation override.** Three routes supply an implementation for a carrier: its own member, an
  instance claim's operation binding (`provides Desc[T = Leaf, describe = other]`, in the
  carrier's body or in a `namespace Leaf` entry), and a witness sort's member. A default fills a
  gap and never shadows a written implementation. Two suppliers are a tie, refused at load where
  the carrier is static and at the call where only a value names it. The rule holds wherever the
  call names the operation.
- **Backing is executable.** A provision whose operation nothing can run is a load error, "rather
  than certify a program whose call fails only at run time".
- **One carrier declaring one spec twice.** Provisions that agree are merged into one view, "so a
  parameter bound by a later provision and omitted by an earlier one is still read".

## The matrix

One program per cell, 112 in all (`supplier-question-map/gen.py`). A spec `Desc` declares one
operation, either with a default body (`= 1`) or without; a carrier `Leaf` is supplied by one of
seven configurations; the call is reached by one of five routes. Within a row every route should
give the same answer.

| supplied by | what the program writes |
|---|---|
| default-only | `Leaf provides Desc[T = Leaf]` |
| own | the same, and `Leaf`'s own member `= 2` |
| binding-in-body | `Leaf provides Desc[T = Leaf, op = other]`, `other = 3` |
| binding-in-entry | the same provision, written in `namespace Leaf … end` |
| binding-both | `Leaf provides Desc[T = Leaf]` and the entry's binding provision |
| witness-only | `sort W provides Desc[T = Leaf]` with a member `= 4` |
| own+binding | `Leaf`'s own member and the entry's binding |

| route | the call |
|---|---|
| by-name | `Desc.describe(leaf())`, `Desc.name[T = Leaf]()` |
| dot | `leaf().describe()` |
| dictionary | `gen(leaf())` over `gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)` |
| abstract-receiver | `viaShape(leaf())` over `viaShape(s: Shape) -> Int64 = Desc.describe(s)` |
| rule-body | `rule rq(?r) :- ?r <=> Desc.describe(leaf())`, asked as a query |

A bold cell contradicts §8.7.

**`describe(x: T)` — the call hands the carrier a value**

| spec op | supplied by | §8.7 says | by-name | dot | dictionary | abstract-receiver | rule-body |
|---|---|---|---|---|---|---|---|
| defaulted | default-only | 1 | 1 | 1 | 1 | 1 | 1 |
| defaulted | own | 2 | 2 | 2 | 2 | 2 | 2 |
| defaulted | binding-in-body | 3 | 3 | 3 | 3 | 3 | 3 |
| defaulted | binding-in-entry | 3 | 3 | 3 | 3 | 3 | 3 |
| defaulted | binding-both | 3 | 3 | 3 | 3 | 3 | 3 |
| defaulted | witness-only | 4 | 4 | 4 | 4 | 4 | 4 |
| defaulted | own+binding | tie refused | tie refused | tie refused | tie refused | tie refused | tie refused |
| body-less | default-only | refused at load | refused at load ¹ | refused at load ¹ | refused at load | refused at load | refused at load |
| body-less | own | 2 | 2 | 2 | 2 | 2 | 2 |
| body-less | binding-in-body | 3 | 3 | 3 | 3 | 3 | 3 |
| body-less | binding-in-entry | 3 | 3 | 3 | 3 | 3 | 3 |
| body-less | binding-both | 3 | **refused at load** | **refused at load** | **refused at load** | **refused at load** | **refused at load** |
| body-less | witness-only | 4 | 4 | 4 | 4 | 4 | 4 |
| body-less | own+binding | tie refused | tie refused | tie refused | **2** | tie refused | tie refused |

**`name()` — only a bracket names the carrier**

| spec op | supplied by | §8.7 says | by-name | dictionary | rule-body |
|---|---|---|---|---|---|
| defaulted | default-only | 1 | 1 | 1 | — ² |
| defaulted | own | 2 | 2 | 2 | — ² |
| defaulted | binding-in-body | 3 | 3 | 3 | — ² |
| defaulted | binding-in-entry | 3 | 3 | 3 | — ² |
| defaulted | binding-both | 3 | 3 | 3 | — ² |
| defaulted | witness-only | 4 | 4 | 4 | — ² |
| defaulted | own+binding | tie refused | tie refused | tie refused | — ² |
| body-less | default-only | refused at load | refused at load | refused at load | refused at load |
| body-less | own | 2 | 2 | 2 | — ² |
| body-less | binding-in-body | 3 | **loads, dies at run** | 3 | — ² |
| body-less | binding-in-entry | 3 | **loads, dies at run** | 3 | — ² |
| body-less | binding-both | 3 | **refused at load** | **refused at load** | **refused at load** |
| body-less | witness-only | 4 | 4 | 4 | — ² |
| body-less | own+binding | tie refused | **2** | **2** | — ² |

¹ Refused twice: the call ("expected an operation a call can run") beside the provision ("backs no
operation"). The other routes give the second alone.
² A bracket on a call in a rule body is refused ("call-site type arguments … are not supported"),
WI-20261024-TC54R, proposal 068's ground. Not a supplier answer.

Of 112 cells, 13 contradict §8.7, every one for a body-less operation. On `d6a28558`, before
ZAWX9's delivery, 18 did: the five more were the defaulted `own+binding` through a dictionary in
both shapes (it ran the own member) and the defaulted `name()` through a dictionary with a binding
in any position (it ran the default).

## The divergences

**D1 — a tie of a body-less operation through a dictionary runs the carrier's own member.** Every
other route refuses own+binding as a tie; the dictionary answers 2, in both shapes. With no
receiver, the call by name answers 2 as well. Until ZAWX9 the defaulted operation did the same
through a dictionary; it is refused there now.

**D2 — through a dictionary a defaulted operation ran its default over a binding** — delivered by
ZAWX9 (`3657c39d`). `name()`, defaulted, binding in any position: by name 3, through `gen[A =
Leaf]()` 1 on `d6a28558`, 3 now. With a receiver it never showed: eval re-dispatches by the value.

**D3 — a body-less operation with no receiver, supplied by a binding alone, loads and dies when
called by name.**

```anthill
sort Desc
  sort T = ?
  operation name() -> Int64
end
sort Leaf
  entity leaf
  provides Desc[T = Leaf, name = other]
end
operation other() -> Int64 = 3
-- main: println(console(), to_string(Desc.name[T = Leaf]()))
```

`anthill load` is clean; `anthill run` exits 1 with `operation has no body: Desc.name — nothing
this runtime can run is registered for it`. The same call through a dictionary answers 3. With an
own member beside the binding, the call by name answers 2 where the tie is due. It is D2 turned
round: by name the body-less path does not read the binding, and with no receiver eval has no value
to re-dispatch on.

**D5 — a binding written in the entry does not back the provision written in the body.**
binding-both, body-less: every route is refused, `Leaf provides Desc but backs no operation`. The
defaulted twin answers 3 on every route, so dispatch reads the two provisions as one view, as
§8.7's merge rule says, and the backing check does not.

(D4 was the double refusal of footnote 1; it is a message, not an answer, and is left out.)

D1, D3 and D5 are WI-20261025-7K84M; D2 was ZAWX9.

## The readers

Each row answers the question for some route, by its own rule.

| reader | where | routes it sees | default | tie | can-it-run filter | used by |
|---|---|---|---|---|---|---|
| `spec_op_suppliers_for_carrier` | `kb/typing/provision.rs:1267` | own, binding, witness | caller's | returns all; caller refuses | no | `check_apply_iter` (apply.rs:3799), `arbitrate_unarbitrated_supplier_tie`, `carrier_override_suppliers`, eval's value-directed dispatch (`resolve_spec_op_target_by_value`, eval.rs:1614, which hands it to `spec_op_dispatch_by_value`) |
| `carrier_override_suppliers` | `kb/typing/call_class.rs:1281` | the owner's three | fills the gap | refused at load | `op_is_interpretable` | defaulted call by name (apply.rs:2609), the dot (`dot_member_dispatch_decision`) |
| `resolve_op_target_at` | `kb/typing/call_class.rs:1024` | defaulted: the provider's suppliers over every route (`provider_override_suppliers`, call_class.rs:1298, since ZAWX9); body-less: own (unfiltered), else binding, else the spec op | fills the gap | defaulted: refused; **body-less: none, first match** | defaulted: yes; body-less: none | eval's dictionary dispatch (`dispatch_via_sort_ops_table`, eval.rs:1569, through `resolve_op_target_checked`), the resolver's `dictionary_dispatch_target`, reflect `Dictionary.resolveOp` / `Dictionary.ops`, the `TypePattern` boundary (eval/mod.rs:443), `defaulted_call_target`, `classify_pin_or_apply_within` (build.rs:2090, 2130), `check_apply_iter` (apply.rs:2933, 4355) |
| `dispatch_spec_op_cached` | `kb/typing/carrier.rs:4512` | provisions by SLD; no binding ("does not read instance-fact op-bindings", its comment at apply.rs:3284) | — | — | — | body-less call by name (`check_apply_iter`, from apply.rs:3183) |
| `instance_fact_op_binding`, read directly | `kb/typing/provision.rs:904` | binding | — | — | — | apply.rs:3284, a result-only carrier, to recover what the line above misses |
| `carrier_own_op` / `carrier_override_op` | `kb/typing/call_class.rs:1174`, `:1224` | own only | — | — | `op_is_interpretable` (second) | `concrete_self_receiver_override` (build.rs:2340), the dot (dispatch.rs:1216), `check_provider_operations`, and six more in `kb/load.rs` (builtin tags, `neq`) and `rule_requirements.rs` (equality) |
| `op_backed` + the row's own bindings | `kb/typing/provision.rs:1567`, `coherence.rs:1434` | own, the spec's default, **this provision row's** binding | counts | — | executable | the backing check, `check_provider_operations` |

Two gates sit in front of the readers and fork every route by whether the spec operation has a
body: `lookup_spec_op_dispatch` (`call_class.rs:264`, 18 callers) answers for a body-less operation
only, and `defaulted_spec_op_parent` (`call_class.rs:175`) for a defaulted one. A route that asks the
first takes the body-less path, one that asks the second the defaulted path, and the two paths read
different rows of the table above. §8.7's rule does not depend on the default, except to fill a gap.

How each divergence follows, as read from the code and its comments (not traced):

- **D1** — the dictionary route reads `resolve_op_target_at`, whose body-less branch is first
  match, so no tie. (D2 was its other half: the binding leg was behind `lookup_spec_op_dispatch`,
  so a defaulted operation never reached it; ZAWX9 gave the defaulted branch the provider's
  suppliers.)
- **D3** — the body-less call by name is pinned by `dispatch_spec_op_cached`, which reads no
  binding; with a receiver, eval's value-directed dispatch reads the owner and recovers it.
- **D5** — `op_backed` and the binding leg beside it read one provision row; dispatch reads the
  merged view.

`spec_op_suppliers_for_carrier` was made the owner by WI-842, whose doc records that eval's
first-match chain was deleted "so the first-match … read cannot come back", and
`carrier_override_suppliers` records that it avoids "a FOURTH enumeration of the three routes".
The first-match reader still standing on a route is the body-less branch of
`resolve_op_target_at`, and the fork between its two branches is the default.

## What one answer would take

One function, asked by every route: the suppliers of an operation for a carrier, read from the
merged provision view over all three routes, filtered to what can run, then arbitrated — the one
supplier runs, a default fills an empty set, two suppliers are a tie, an empty set with no default
is "nothing runs". The routes keep only the choice of *when* to ask: at load where the typer has
the carrier (the call by name, the dot, a pinned bracket), at the call where only a value or a
dictionary has it (eval by value, eval through a dictionary, reflect), and the backing check asks
it of every provision at load and refuses "nothing runs". The rule-body route is proposal 068's,
which already types a rule-body call as an operation body's (§3, WI-20260926-7D48J,
WI-20261015-ZPETZ).

That removes the body-less branch of `resolve_op_target_at`, `dispatch_spec_op_cached`'s supplier role and the
backing check's row-local read, and makes `lookup_spec_op_dispatch`'s body-less gate a question
about what the default does rather than which path a call takes. It is measured by this matrix:
every bold cell turns to what §8.7 says, and every plain cell stays.

## Reproduce

From the repository root, with `rustland/target/debug/anthill` built:

```bash
python3 docs/design/supplier-question-map/gen.py /tmp/supplier/progs
cut -f1,7 /tmp/supplier/progs/manifest.tsv | xargs -P 12 -n 2 sh -c 'docs/design/supplier-question-map/judge.sh /tmp/supplier/progs $0 $1' > /tmp/supplier/verdicts.tsv
python3 docs/design/supplier-question-map/table.py /tmp/supplier
```

About fifteen seconds on 24 cores, over the CLI. The same matrix, less the rule-body route, is the
generated family `f-supplier-routes` (`rustland/anthill-core/tests/families/supplier_routes.rs`,
84 programs, `scripts/families.sh f`): D1 and D3 are its listed exceptions, under
WI-20261025-7K84M — D2's, under ZAWX9, came off when ZAWX9 landed, the family naming the five
verdicts it moved — and D5 — a refusal the rule does not make, which no property sees — is in
its verdict file. Its judge reads a tie refused at load and one refused when the call runs as one
verdict, since §8.7 lets the route choose.
