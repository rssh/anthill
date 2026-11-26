## Attributes

- id: WI-20261126-DHB0C-a-witness-s-eq-written-for-the
- created: 2026-11-26T17:11:07Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-26T19:15:35Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A WITNESS'S `eq` WRITTEN FOR THE SORT IT WITNESSES COUNTS AS ITS OWN EQUALITY: a sort with values that witnesses another's equality through `operation eq(a: Other, b: Other)` is read as supplying its OWN `eq`, so its equality is not derived and a comparison of two of its values is refused at load. The reverse of WI-20261126-Q1WE9 (user, 2026-11-26: file it).

THE PROGRAM, MEASURED (one `load_all`; the same verdict on 2c1ef430f, before WI-20261102-YX17K, and on a21d3e229, after Q1WE9):

    namespace test.rev
      import anthill.prelude.{Eq, PartialEq, Int64, Bool}
      sort Other
        entity o(n: Int64)
      end
      sort W
        entity w(n: Int64)
        provides PartialEq[T = Other]
        provides Eq[T = Other]
        operation eq(a: Other, b: Other) -> Bool = true
      end
      sort Check
        import anthill.prelude.PartialEq.{eq}
        operation ws() -> Bool = eq(W.w(n: 1), W.w(n: 2))
      end
    end

Refused at the call in `ws`: `type mismatch in anthill.prelude.PartialEq.eq.dispatch: … no impl matches — unresolved: anthill.prelude.PartialEq[T = test.rev.W]`. `W` provides no `PartialEq` of its own.

THE CONTROL, MEASURED: the same `W` with its member named `oeq` and bound by the provision (`provides PartialEq[T = Other, eq = W.oeq]`) loads, and `W`'s equality is derived — `eq(w(n: 1), w(n: 2))` is `false`, `eq(w(n: 1), w(n: 1))` is `true` — while `Other`'s is `oeq` (`eq(o(n: 1), o(n: 2))` is `true`). So it is the member's NAME that takes `W`'s equality away, not the witness.

WHAT IS GOING ON, READ AND NOT YET MEASURED. `typing::member_fits_spec_op` judges `W.eq` "at one of" the provisions that dispatch to `W` — its witness provisions among them — and it fits at `PartialEq[T = Other]`. So the NNQ1S verdict says `W`'s own member supplies `PartialEq.eq`, `carrier_own_op(W, eq)` returns it, the eq-dispatch index keys `W` to it, and `eq_derive::is_eq_boundary` makes `W` a boundary: its `eq` is "the author's", and nothing is derived for it. Q1WE9 made the witness route judge the member at the witness's provision for the witnessed sort; this is the same verdict for the provider's OWN carrier, still reached at any provision.

DIRECTION, not decided: the provider's own route judges its member at the provisions about the provider itself (and at the carrier where there are none), not at its witness provisions — those are the per-carrier witness verdict's since Q1WE9. Then `W.eq(a: Other, b: Other)` supplies `W` nothing, `W` is no boundary, its equality is derived as the control's is, and `Other`'s `eq` is `W.eq`. Whether a sort whose only `eq` is for another sort should instead be refused at load (as NNQ1S refuses an `eq` that does not fit beside the carrier's own provision) is the decision to make first: kernel-language §8.4, *A member that does not fit is no supplier*, states the "at one of" reading for a carrier's member and would change.

ACCEPTANCE: the program above loads and `ws()` answers `false` (or is refused by a stated rule, if that is the decision); `Other`'s `eq` is `W.eq`; the control's verdicts unchanged; backing the fix out fails the new rows; §8.4 says which provisions a carrier's own member is judged at; full workspace green via rustland/scripts/test.sh, families green.

REFERENCE: kb/typing/signature.rs `record_members_that_supply_nothing`, `member_fits_spec_op`, `member_fits_at`; kb/typing/call_class.rs `carrier_own_op`, `witness_own_op`; kb/eq_derive.rs `is_eq_boundary`; WI-20261126-Q1WE9, WI-NNQ1S, WI-837.

## Changes

### 2026-11-26T19:15:07Z — feedback — user

DECIDED WITH THE USER (2026-11-26): refused at load, and the refusal says how to write it. A carrier's own member is judged at the provisions about its OWN values (its own that witness no other sort, and a witness's that names it), or at the carrier where there are none; its own witness provisions are judged per carrier witnessed (Q1WE9's verdict). `W.eq(a: Other, b: Other)` supplies `W` nothing, `W` derives its equality, and its written `eq` holds the name the derived member is declared under: NNQ1S's refused `eq`, refused in the comparison's words with a clause naming the witness provision it fits and the repair ("Give the member another name and bind it in that provision (`eq = W.<name>`)"). kernel-language §8.7, *A member that does not fit is no supplier* (the ticket's "§8.4" is §8.7). MEASURED: the ticket's program refused so; the control (`oeq` bound) unchanged, `ws()` false, `wsame()` true, `other()` true; a valueless witness still answers `Other` through `W.eq`, by name and through `requires PartialEq`.

DONE: `typing::member_fits_spec_op` reads the carrier's own non-witness provisions; `witness_own_op` reads the member the witness declares (`member_declared_under`) and the per-carrier verdict alone, not `carrier_own_op`; `provision_own_op` picks the verdict per provision for the readers that walk a provider's provisions (`spec_op_backed_by`, the `@[simp]`-alone check, a dictionary's suppliers); `equality_reaching_no_eq`'s passed-over member and the `neq` witness leg read the member by name. The NNQ1S refusal is asked at the carrier's own provisions only (asked at a witness provision, the comparison refused nothing and the once-per-carrier mark silenced it at the derived row).

Q1WE9's written-member row (decided with the user, P3's rule): `Point` with a written `eq(a: Point, b: Point)` and no provision of its own loaded only because the provider's verdict was reached at its witness provision first, where the member does not fit; it is now held to writing `provides PartialEq[T = Point]`, as `sort P3 { entity p3(x: Int64)  operation eq(a: P3, b: P3) }` is on main. The row writes it; `a_written_eq_with_no_provision_of_its_own_is_held_to_one` is the refusal.

FOLDED IN (decided with the user), the same mix-up in three more readers — a witness's provision read as its provider's own:
1. THE DERIVATION read "`W` provides `PartialEq`/`Eq`" off `W`'s witness rows (`sort_provides`, provider-keyed): with `provides PartialEq[T = Other, eq = W.oeq]` alone `W`'s values got no equality (refused "unresolved: PartialEq[T = W]"), and with `Eq[T = Other]` beside it they got one only through `derive_hash` reading the witness's `Eq` as `W`'s, deriving `Hash[T = W]`, and the forwarding from it. Now `typing::sort_provides_for_itself`, whose "own" is `typing::provision_is_own` — factored out of `provision_carrier`, one owner; `witness_dispatch_carrier` finds no carrier on `Eq` (no operation receives `T`), so every `Eq` row read as its provider's own there.
2. AN OPERATION BINDING ON `Eq` (`provides Eq[T = Other, eq = W.oeq]`) was dropped by the forwarding to `PartialEq` ("no `eq` answers it: none is written") and read by the eq-dispatch index as `W`'s own. The forwarding carries an operation binding to the floor that declares it (kernel-language §5.1; a separate `ForwardedRow.operations`, so only a checked name reaches the derived view); the index sweeps `PartialEq`'s rows alone (the `Eq` sweep was for the retired `fact Eq[…]`). One provider's rows at one application are one dictionary: the binding on `Eq` beside an unbound `PartialEq` line answers, the same `eq` on both is one binding, two are the tie. MEASURED on main too: `W provides Eq[T = W, eq = W.weq]` loaded and died at the call, `EqualityWithNoMember`.
   A binding that names no type parameter and no operation of the spec or a spec it provides is refused where it is written (`typing::check_provision_binding_names`, §8.7): `foo = W.oeq` loaded and failed downstream. MEASURED: it catches nothing in the workspace.
3. THE `Eq`/`NonEq` EXCLUSION keyed rows by provider: a `W` with a `Float` field witnessing `Other`'s `Eq` was refused as providing both once it derived its own `NonEq`, and a witness's `Eq[T = C]` beside `C`'s own `NonEq` was judged at no carrier. Each row is now keyed at the carrier it is about.

ROWS: `tests/include/wi_dhb0c_witness_own_equality_test.rs`, 16; Q1WE9's file: the written-member row writes its provision, one row added. BACK-OUTS, MEASURED (each run over this file, Q1WE9's, NNQ1S's, SZKV7's later-equality and Y6ZCD's): the verdict counting witness provisions fails the ticket's row and Q1WE9's new one; `witness_own_op` through `carrier_own_op` fails the valueless-witness row, Q1WE9's control and five more (SZKV7, Y6ZCD); the refusal asked at witness provisions, or the clause left off, fails the ticket's row; the derivation on `sort_provides` fails the PartialEq-alone row; the carry off fails six; the `Eq` sweep back fails three; the binding-name check off fails one; "own" via `witness_dispatch_carrier`, or the exclusion by provider, fails the partial-witness row; the exclusion skipping witness rows fails the witness-at-`NonEq` row. On the tree before, nine rows fail and nine pass (controls by design, the valueless witness kept by the reader move, Q1WE9's).

/code-review (xhigh): fixed — the exclusion's silent skip of witness rows (now judged at their carrier), the forwarded view admitting any non-parameter name (operations a field of their own), the refusal clause at a provision that binds `eq` itself, the §8.4 citations, Q1WE9's header; measured not a bug — a carried `eq` beside a carrier's own unbound `PartialEq` (the binding answers; the row is kept). LEFT, read not measured: dispatch's witness classifier (`witness_dispatch_carrier`, the per-call readers, CXR5B's stage 2) and `provision_is_own` disagree for a spec no operation of which receives its type-var, so for such a spec a witness provision still counts toward its provider's own verdict; `provision_is_conditional` is still provider-keyed in `derive_hash` and the exclusion's conditional reading.

### 2026-11-26T19:15:21Z — feedback — user

Delivered in eea88ed51 — the change, rows and measurements are the feedback above. Gate 12890 / 0; families green; scaland testFull 811+51+1 / 0. Left, not ticketed: dispatch's witness classifier (witness_dispatch_carrier) and provision_is_own disagree for a spec no operation of which receives its type-var; provision_is_conditional is still provider-keyed in derive_hash and the Eq/NonEq exclusion.

