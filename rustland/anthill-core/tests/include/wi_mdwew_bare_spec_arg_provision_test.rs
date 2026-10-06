//! WI-20260828-MDWEW — typer: project a BARE SPEC-TYPED argument's PROVISION into a
//! constructor field typed on a DIFFERENT spec.
//!
//! The third face of the threading question WI-594 and WI-599 answer two faces of. A
//! value typed as a bare spec (`s: Stream`) flows into an entity field typed on a spec it
//! merely PROVIDES (`source: Iterable[C = Source, Element = Src, E = ES]`). Neither
//! delivered reader fires: `bare_spec_arg_self_projection` wants the field to apply the
//! argument's OWN spec, and `carrier_arg_provision_projection` reads its provision off
//! the ENCLOSING SORT, which a free operation does not have. So the field's params stay
//! unbound, the constructed carrier's provided row leaks `??_`, and the declared return
//! is rejected.
//!
//! The fact that relates the two specs is the argument sort's own
//! `provides Iterable[C = Stream, Element = T, E = E]`, written in the ARGUMENT SORT's
//! parameters — so the projection member must come from THERE, not from the field's key.
//! `transposed_provision_*` below is the fixture that separates those two readings.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT (measured, by making
//! `bare_spec_arg_provision_projection` return `None` at entry):
//!   * `bare_spec_arg_threads_provided_specs_params` — RED
//!     (`got Mapped[T = ?Dst, ES = ??_, EF = …, Src = s.Elem, Source = ??_]`)
//!   * `transposed_provision_threads_by_provision_not_by_name` — RED
//!     (`expected Slot[Left = x.Left, Right = x.Right], got Hold`)
//!   * `transposed_provision_name_keyed_direction_is_refused` — GREEN, by design: with
//!     nothing threaded, BOTH directions are refused, so this control cannot distinguish.
//!     It exists for the OTHER back-out, below.
//!
//! WHAT FAILS UNDER THE NAME-KEYED ALTERNATIVE (measured, by taking the projection member
//! from the FIELD's binding key — the WI-594 spelling — instead of from the provision):
//! ALL THREE. The main fixture reports `expected s.Element -> ?_, got s.Elem -> ?Dst` (the
//! member built off the field's key `Element` rather than the argument sort's `Elem`), the
//! transposed positive builds `Hold[HL = x.Left, HR = x.Right]` — the swap dropped — and
//! the refusal control ACCEPTS the transposed return. That pair of back-outs is why the
//! provision, and not a name, is the join.
//!
//! The ticket's own named repro is `wi594_finite_map_effect_threading_test::
//! bare_receiver_map_threads_source_effect` under WI-590's stdlib consolidation (where
//! `mapped`'s source field becomes `Iterable`-typed). VERIFIED against that patch: RED
//! without this change, GREEN with it. It is not the shipped fixture because the
//! consolidation is not on main — the fixtures here are, and they need no stdlib change.
//!
//! The ticket's SECOND half — the ambient-`requires` face — is at the bottom of this file,
//! with its own back-outs.
//!
//! THE REST OF THE FILE IS `/code-review`'s. Three defects it found and the fixtures that pin
//! them: a compound `requires`-clause value bound verbatim, a provision binding used with no
//! groundness gate, and — the same root at both call sites — a FOREIGN sort's parameter
//! silently claimed when its short name collides, because `substitute_carrier_params` joins
//! its leaves by LOCAL NAME. Each has its own back-out named at its test.

// WI-20261005-KSSA4 — THE FIELD IS TYPED BY THE SORT'S PARAMETER NOW. `mk(source: Walk[C =
// Source, Element = Src, E = ES], …)` held a value of a sort that PROVIDES `Walk`, read as a
// `Walk`; a provider's value is not one, and the readers this file's header describes —
// which rebuilt the argument's type as the field's spec — are deleted for a spec over a
// parameter. `Mapped` is written `entity mk(source: Source, …)` under `requires Walk[C =
// Source, Element = Src, E = ES]`: the field says which sort the source is, and the clause
// says what `Walk` is there, read at a construction off the source's provision or off the
// clause in scope that is about its parameter
// (`bind_sort_params_from_sort_requires_at_construction`). The rows are unchanged in what
// they ask. Their refusals moved from "the field's parameters stayed unbound" to "the
// requirement `Mapped` owes cannot be supplied at the instance built": the clause binds a
// parameter no field fixed, a parameter a field fixed to another type stays as fixed, and
// the instance is then asked for the sort's requirement where the value is built
// (`construction_meets_sort_requires`) — the same disagreement, found by the one judge of
// it. The back-outs named at each row are the ones measured on the deleted readers;
// `wi_kssa4_spec_typed_value_test`'s ledger has these rows' own. The `transposed_*` rows
// keep a field typed at a spec, `Slot`, which receives on itself: an `Xchg` IS a `Slot`,
// and `bare_spec_arg_provision_projection` still reads its provision.

/// Each refusal control below names the token that DISTINGUISHES the right refusal from the
/// wrong acceptance — the string the corresponding back-out makes disappear. The assertion
/// itself moved to `common` under WI-20260829-70XVH, whose free-op rows are its second user.
use crate::common::assert_refused_naming;

/// The shape the ticket names, in miniature and self-contained. `Seq` is the
/// self-receiver spec (the `Stream` analogue) and `Walk` the carrier-param spec the field
/// is typed on (the `Iterable` analogue); `Seq provides Walk[C = Seq, Element = Elem,
/// E = Row]` is the only place the relationship lives.
///
/// DRIVES: `Mapped`'s `Source` and `ES` appear in no other field, so nothing else can
/// bind them — the sibling `fn` arrow pins only `Src`. The declared return cannot pin
/// them either: unwritten constructor params rigidify (`??_`), which is what the
/// backed-out error above shows. So the load succeeds only if the provision threaded.
///
/// The param names are deliberately UNALIGNED across the two sorts (`Seq.Elem` vs
/// `Walk.Element`, `Seq.Row` vs `Walk.E`) so no short-name coincidence can stand in for
/// reading the provision.
#[test]
fn bare_spec_arg_threads_provided_specs_params() {
    let src = r#"
namespace test.mdwew
  import anthill.prelude.{Option, Modify}

  sort Seq
    import anthill.prelude.Option
    sort Elem = ?
    effects Row = ?
    operation firstOf(s: Self) -> Option[T = s.Elem] effects s.Row
    provides Walk[C = Self, Element = Elem, E = Row]
    operation walk(s: Self) -> Seq[Elem = s.Elem, Row = s.Row] = s
  end

  sort Walk
    sort C = ?
    sort Element = ?
    effects E = ?
    operation walk(c: C) -> Seq[Elem = Element, Row = E]
  end

  sort Mapped
    import anthill.prelude.{Option, Function}
    import anthill.prelude.Option.{none}
    sort Source = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    requires Walk[C = Source, Element = Src, E = ES]
    entity mk(source: Source, fn: (Src) -> T @ {EF})
    provides Seq[Elem = T, Row = {ES, EF}]
    operation firstOf(m: Self) -> Option[T = T] effects {ES, EF} = none
  end

  -- the free op: a BARE `Seq` receiver into a `Walk`-typed field.
  operation bare_map[Dst, EffP](s: Seq, f: (x: s.Elem) -> Dst @ {EffP, -Modify[x]})
    -> Seq[Elem = Dst, Row = {s.Row, EffP}] =
    mk(s, f)
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.is_empty(),
        "a bare spec-typed argument flowing into a field typed on a spec its sort \
         PROVIDES should thread that provision's params and load clean:\n{}",
        errs.join("\n")
    );
}

/// CONTROL — a provision binding that names a FOREIGN sort's parameter is not threaded.
/// Found by `/code-review`.
///
/// `Seq provides Walk[…, Element = Foreign.X, …]`: nothing in this receiver's substitution
/// replaces `Foreign.X` (it is not one of `Seq`'s parameters), so it survives the rebuild as
/// a bare parameter reference. Threaded, it would UNIFY with whatever the sibling `fn` field
/// supplies — silently agreeing with `s.Elem` instead of contradicting it. The concrete twin
/// below shows refusal is the intended verdict; the two must agree.
///
/// This is exactly the caller-side groundness check `substitute_carrier_params`' own doc
/// requires ("a leaf absent from `recv_bindings` is left intact, so the caller's groundness
/// check rejects a partially-substituted result"), and which this reader initially omitted.
///
/// MEASURED: drop the `type_value_is_ground_g(kb, val, true)` gate and the `Foreign.X` row
/// loads clean while the `Int64` row still refuses — the two rows disagreeing IS the defect.
fn foreign_provision_binding(element: &str) -> Vec<String> {
    let src = format!(
        r#"
namespace test.mdwew.foreign
  import anthill.prelude.{{Option, Int64, Modify}}

  sort Foreign
    sort X = ?
    sort Elem = ?
  end

  sort Seq
    import anthill.prelude.Option
    import test.mdwew.foreign.Foreign
    sort Elem = ?
    effects Row = ?
    operation firstOf(s: Self) -> Option[T = s.Elem] effects s.Row
    provides Walk[C = Self, Element = {element}, E = Row]
    operation walk(s: Self) -> Seq[Elem = s.Elem, Row = s.Row] = s
  end

  sort Walk
    sort C = ?
    sort Element = ?
    effects E = ?
    operation walk(c: C) -> Seq[Elem = Element, Row = E]
  end

  sort Mapped
    import anthill.prelude.{{Option, Function}}
    import anthill.prelude.Option.{{none}}
    sort Source = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    requires Walk[C = Source, Element = Src, E = ES]
    entity mk(source: Source, fn: (Src) -> T @ {{EF}})
    provides Seq[Elem = T, Row = {{ES, EF}}]
    operation firstOf(m: Self) -> Option[T = T] effects {{ES, EF}} = none
  end

  operation bare_map[Dst, EffP](s: Seq, f: (x: s.Elem) -> Dst @ {{EffP, -Modify[x]}})
    -> Seq[Elem = Dst, Row = {{s.Row, EffP}}] =
    mk(s, f)
end
"#
    );
    crate::common::try_load_kb_with(&src)
        .err()
        .unwrap_or_default()
}

#[test]
fn foreign_provision_binding_is_refused_like_its_concrete_twin() {
    let concrete = foreign_provision_binding("Int64");
    let foreign = foreign_provision_binding("Foreign.X");
    // The CONCRETE twin fixes the intended verdict: the provision says the source walks
    // `Int64`s, the callback takes the source's own `s.Elem`, and a `Mapped` over that pair
    // owes `Walk` of the source at an element no row of `Seq` answers at. Refused where the
    // value is built, naming the requirement at the instance.
    assert_refused_naming(
        &concrete,
        &[
            "Element = s.Elem, E = {s.Row}]` of `test.mdwew.foreign.Mapped` cannot be \
             supplied for the construction `test.mdwew.foreign.Mapped.mk`",
            "`test.mdwew.foreign.Seq` does provide `test.mdwew.foreign.Walk`, but no row of \
             it answers at these bindings",
        ],
        "the concrete control must refuse, or the foreign row proves nothing",
    );
    // The FOREIGN one says a type this call does not determine, so it is neither bound to
    // nor held against — the construction is not what refuses it. The provision is: a
    // member returning `Seq[Elem = s.Elem, …]` is not what `Walk.walk` promises at an
    // element that is another sort's parameter. Same verdict, and that is what the two
    // rows must agree on.
    assert_refused_naming(
        &foreign,
        &["its own member 'walk' does not fit 'test.mdwew.foreign.Walk.walk'"],
        "a provision binding naming a FOREIGN sort's parameter must be refused, not \
         threaded as though the receiver determined it",
    );
    assert!(
        !foreign.iter().any(|e| e.contains("mk.")),
        "nothing of the foreign binding reaches the construction: {foreign:#?}"
    );
}

/// The TRANSPOSING fixture, and the reason it is built this way. `Slot` and `Xchg`
/// declare parameters with the SAME short names (`Left` / `Right`), and `Xchg`'s
/// provision SWAPS them (`provides Slot[Left = Right, Right = Left]`). So the two
/// candidate readings — take the projection member from the provision, or from the field's
/// binding key — produce DIFFERENT, both well-formed types, and a fixture whose names
/// lined up could not tell them apart.
///
/// `Hold` re-flips in its own provision, so the two readings differ in the type `grab`
/// returns. `ret` is the declared return under test.
fn transposed_provision(ret: &str) -> Vec<String> {
    let src = format!(
        r#"
namespace test.mdwew.transposed
  import anthill.prelude.Bool

  sort Slot
    import anthill.prelude.Bool
    sort Left = ?
    sort Right = ?
    operation flipped(s: Self) -> Bool
  end

  sort Xchg
    import anthill.prelude.Bool
    sort Left = ?
    sort Right = ?
    -- the SWAP: Slot's Left is Xchg's Right, and Xchg names its own params the same
    -- way Slot does, so only reading THIS clause gets the direction right.
    provides Slot[Left = Right, Right = Left]
    operation flipped(s: Self) -> Bool = true
  end

  sort Hold
    import anthill.prelude.Bool
    sort HL = ?
    sort HR = ?
    entity hold(inner: Slot[Left = HL, Right = HR])
    provides Slot[Left = HR, Right = HL]
    operation flipped(h: Self) -> Bool = false
  end

  operation grab(x: Xchg) -> {ret} = hold(x)
end
"#
    );
    crate::common::try_load_kb_with(&src)
        .err()
        .unwrap_or_default()
}

/// Threading through the provision gives `hold(x) : Hold[HL = x.Right, HR = x.Left]`,
/// which `Hold`'s own re-flipping provision hands back as `Slot[Left = x.Left,
/// Right = x.Right]`. Taking the member from the field's key instead gives the
/// transposed `Hold[HL = x.Left, HR = x.Right]` and this is refused.
#[test]
fn transposed_provision_threads_by_provision_not_by_name() {
    let errs = transposed_provision("Slot[Left = x.Left, Right = x.Right]");
    assert!(
        errs.is_empty(),
        "the projection member must come from the ARGUMENT SORT's parameter named by the \
         provision, not from the field's binding key:\n{}",
        errs.join("\n")
    );
}

/// CONTROL for the direction: the transposed return — what a name-keyed reading would
/// build — must be REFUSED. Green with the change backed out too (nothing threads, so
/// both directions are refused); it is the name-keyed back-out this one catches, where it
/// goes RED by accepting a load.
#[test]
fn transposed_provision_name_keyed_direction_is_refused() {
    let errs = transposed_provision("Slot[Left = x.Right, Right = x.Left]");
    // `HL = x.Right` is the construction THREADED THROUGH THE PROVISION — the swap applied.
    // The name-keyed alternative builds `HL = x.Left` and ACCEPTS this return, so the token
    // and the refusal together pin the direction.
    assert_refused_naming(
        &errs,
        &["HL = x.Right"],
        "the transposed return is the NAME-KEYED answer and must not type-check",
    );
}

// ── WI-20260828-MDWEW, the ticket's second half: the AMBIENT-`requires` face ──────────
//
// The ticket lists this as "RELATED, and worth landing together", and records that WI-590
// implemented it, verified it worked, and REMOVED it before commit because "the only
// fixture that drove it also type-checked with the change backed out — its declared return
// pinned exactly the params the construction left free".
//
// That is true of the shape WI-590 tried and is a property of the RETURN, not of the face:
// a return spelled as the constructed carrier itself (`-> Mapped[Source = C, …]`) seeds
// every still-free param from `expected` after the field loops, so the construction can
// thread nothing and still load. MEASURED both ways below — `ambient_requires_carrier_-
// return_is_pinned_by_expected` is that unmeasurable fixture, kept as the reason the
// driving one is spelled the way it is.
//
// Route the return through the carrier's PROVISION instead and `expected` has nothing to
// pin: the constructed `Mapped`'s unwritten params rigidify to `??_` and the provided
// `Seq[Row = {ES, EF}]` cannot conform. That is `ambient_requires_clause_threads_the_-
// field_specs_params`, and it is RED with the face backed out.

/// Common fixture. `Coll` is a spec that does NOT own `Walk` — it merely
/// `requires Walk[C = C, Element = Element, E = E]` — and its `cmap` puts its bare carrier
/// param `c : C` into `Mapped`'s `Walk`-typed field. Neither the spec-METHOD face of
/// `carrier_provision_short_bindings` (which needs `enclosing_sort() == field_base`) nor
/// WI-594's self-projection (the argument is a type param, not a spec) answers here.
///
/// `clause_carrier` is the parameter the `requires` clause is written ABOUT and `ret` the
/// declared return, so one fixture serves the driving case and both controls.
fn ambient_requires(clause_carrier: &str, ret: &str) -> Vec<String> {
    ambient_requires_with(clause_carrier, "Element", ret, "Element")
}

fn ambient_requires_with(
    clause_carrier: &str,
    clause_element: &str,
    ret: &str,
    cb_arg: &str,
) -> Vec<String> {
    let src = format!(
        r#"
namespace test.mdwew.ambient
  import anthill.prelude.{{Option, Modify}}

  sort Foreign
    sort X = ?
    sort Element = ?
  end

  sort Seq
    import anthill.prelude.Option
    sort Elem = ?
    effects Row = ?
    operation firstOf(s: Self) -> Option[T = s.Elem] effects s.Row
    provides Walk[C = Self, Element = Elem, E = Row]
    operation walk(s: Self) -> Seq[Elem = s.Elem, Row = s.Row] = s
  end

  sort Walk
    sort C = ?
    sort Element = ?
    effects E = ?
    operation walk(c: C) -> Seq[Elem = Element, Row = E]
  end

  sort Mapped
    import anthill.prelude.{{Option, Function}}
    import anthill.prelude.Option.{{none}}
    sort Source = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    requires Walk[C = Source, Element = Src, E = ES]
    entity mk(source: Source, fn: (Src) -> T @ {{EF}})
    provides Seq[Elem = T, Row = {{ES, EF}}]
    operation firstOf(m: Self) -> Option[T = T] effects {{ES, EF}} = none
  end

  sort Coll
    import anthill.prelude.{{Function, Modify, Option}}
    import test.mdwew.ambient.{{Mapped, Seq}}
    import test.mdwew.ambient.Mapped.{{mk}}
    import test.mdwew.ambient.Foreign
    sort C = ?
    sort Other = ?
    sort Element = ?
    effects E = ?
    requires Walk[C = {clause_carrier}, Element = {clause_element}, E = E]
    operation cmap[Dst, EffP](c: C, f: (x: {cb_arg}) -> Dst @ {{EffP, -Modify[x]}})
      -> {ret} =
      mk(c, f)
  end
end
"#
    );
    crate::common::try_load_kb_with(&src)
        .err()
        .unwrap_or_default()
}

/// DRIVES the ambient face. The return goes through `Mapped`'s provision, so `expected`
/// pins nothing and only the `requires Walk[C = C, …]` clause can supply `Source` and `ES`.
/// MEASURED on the reader this row was written for: with `enclosing_requires_provision_
/// bindings` returning `None` at entry, this test ALONE went red. That reader is deleted;
/// the clause is read at the construction now, and with the scope's clause not read there
/// the standard library's own `FiniteCollection.map` is refused, so this row is not
/// separable from it (`wi_kssa4_spec_typed_value_test`'s ledger, part 7).
#[test]
fn ambient_requires_clause_threads_the_field_specs_params() {
    let errs = ambient_requires("C", "Seq[Elem = Dst, Row = {E, EffP}]");
    assert!(
        errs.is_empty(),
        "a bare carrier param put into a field typed on a spec the ENCLOSING SORT requires \
         should thread that clause's params:\n{}",
        errs.join("\n")
    );
}

/// CONTROL — the clause must be ABOUT THIS ARGUMENT. Here it is written about a different
/// parameter (`Other`), so nothing licenses `c : C`: `Mapped` requires `Walk` of its source,
/// the source is a `C`, and the enclosing sort holds `Walk` of another parameter. Refused
/// where the value is built, naming the clause that does not cover (WI-20261005-KSSA4);
/// before a construction owed its sort's requirement the same program was refused one step
/// later, by a return type whose `ES` nothing had said. A clause about any parameter
/// licensing it would load the program clean, with no message at all.
#[test]
fn ambient_requires_clause_about_another_param_does_not_license() {
    let errs = ambient_requires("Other", "Seq[Elem = Dst, Row = {E, EffP}]");
    assert_refused_naming(
        &errs,
        &[
            "`test.mdwew.ambient.Walk[C = test.mdwew.ambient.Mapped.Source,",
            "cannot be supplied for the construction `test.mdwew.ambient.Mapped.mk`",
            "the enclosing scope's `requires test.mdwew.ambient.Walk[C = \
             test.mdwew.ambient.Coll.Other,",
            "covers only as a wildcard and is not forwarded",
        ],
        "a `requires` clause about a DIFFERENT parameter must not license this argument",
    );
}

/// CONTROL, and the record of why the driving fixture returns through a provision: with the
/// return spelled as the constructed carrier, `expected` seeds every param the field loops
/// left free, so this loads whether or not anything threaded. It is the fixture WI-590
/// built, and it measures nothing — GREEN both with the face and with it backed out.
#[test]
fn ambient_requires_carrier_return_is_pinned_by_expected() {
    let errs = ambient_requires(
        "C",
        "Mapped[Source = C, Src = Element, T = Dst, ES = E, EF = EffP]",
    );
    assert!(errs.is_empty(), "{}", errs.join("\n"));
}

/// CONTROL — a COMPOUND clause value must not be bound verbatim. Found by `/code-review`.
///
/// The clause says `Element = Option[T = Other]` while the callback takes an
/// `Option[T = Element]`; `Other` and `Element` are INDEPENDENT parameters of the enclosing
/// sort, so the two disagree and the load must be refused — the shallow spelling of the same
/// disagreement (`Element = Other` against a callback on `Element`) already is, by
/// `ambient_requires_clause_about_another_param_does_not_license`.
///
/// The defect this pins: a `requires` clause is stored against the PRE-RIGIDIFY parameter
/// forms, and resolving only a bare `Ref`/`Var` left every parameter INSIDE a compound as a
/// free unification variable. The sibling `fn` field then bound that free `Other` to
/// `Element`'s rigid and the program loaded — "grant a licence and bind a wrong rigid
/// together", which is what the dispatch-side twin's doc says must not happen.
///
/// MEASURED: restore the `.unwrap_or(v)` fallback in place of the substitute-then-require-
/// ground step and this test ALONE goes red, by loading clean.
#[test]
fn ambient_requires_compound_clause_value_is_not_bound_verbatim() {
    let errs = ambient_requires_with(
        "C",
        "Option[T = Other]",
        "Seq[Elem = Dst, Row = {E, EffP}]",
        "Option[T = Element]",
    );
    // The clause's OWN value, `Option[T = Other]`, is another type than the callback's
    // `Option[T = Element]`, so the clause does not cover the requirement the construction
    // owes at that element, and is named as the one that does not. Read with `Other` left
    // free, the two unify, and the program loads clean.
    assert_refused_naming(
        &errs,
        &[
            "Element = anthill.prelude.Option[T = ?Element]",
            "cannot be supplied for the construction `test.mdwew.ambient.Mapped.mk`",
            "Element = anthill.prelude.Option[T = test.mdwew.ambient.Coll.Other], E = \
             test.mdwew.ambient.Coll.E]` covers only as a wildcard and is not forwarded",
        ],
        "a compound clause value must resolve its parameters to the body rigids, so a \
         disagreement inside it is still a disagreement",
    );
}

/// CONTROL — a FOREIGN sort's parameter whose SHORT NAME COLLIDES is still foreign. Found by
/// `/code-review`, and it is the same defect as the two rows above seen through the one join
/// that was still a name.
///
/// `substitute_carrier_params` resolves a leaf through `type_param_vid_in_sort`, which asks
/// the anchor sort for a parameter of that LOCAL NAME. `Foreign.Element` against an enclosing
/// `Coll.Element` is therefore rewritten to `Coll`'s own rigid, and the groundness gate then
/// sees a rigid and passes it — so the clause licenses a binding it never made. Short names
/// like `T`, `E`, `C`, `Element` collide routinely across the prelude, so this is not exotic.
///
/// The two foreign rows must AGREE. They differ only in the foreign parameter's spelling.
///
/// MEASURED on the reader these rows were written for: with `param_leaves_belong_to_sort`
/// neutralized this test and its provision-side twin — and only those two — went red, by
/// loading the colliding row clean. RE-MEASURED since the field is typed by the sort's
/// parameter: neutralized, no row of this file moves. The clause's element is compared by
/// the variable its symbol names, where a name was never joined, so the two spellings are
/// one case there; both halves fail with a construction owing nothing
/// (`wi_kssa4_spec_typed_value_test`'s ledger, part 22).
#[test]
fn ambient_requires_colliding_foreign_param_is_still_foreign() {
    let non_colliding = ambient_requires_with(
        "C",
        "Foreign.X",
        "Seq[Elem = Dst, Row = {E, EffP}]",
        "Element",
    );
    assert_refused_naming(
        &non_colliding,
        &[
            "cannot be supplied for the construction `test.mdwew.ambient.Mapped.mk`",
            "Element = test.mdwew.ambient.Foreign.X, E = test.mdwew.ambient.Coll.E]` covers \
             only as a wildcard and is not forwarded",
        ],
        "a clause value naming a foreign sort's parameter must not license this argument",
    );
    let colliding = ambient_requires_with(
        "C",
        "Foreign.Element",
        "Seq[Elem = Dst, Row = {E, EffP}]",
        "Element",
    );
    assert_refused_naming(
        &colliding,
        &[
            "cannot be supplied for the construction `test.mdwew.ambient.Mapped.mk`",
            "Element = test.mdwew.ambient.Foreign.Element, E = test.mdwew.ambient.Coll.E]` \
             covers only as a wildcard and is not forwarded",
        ],
        "a foreign parameter that happens to SHARE a short name with an enclosing one is \
         still foreign; it must be refused exactly as `Foreign.X` is",
    );
}

/// CONTROL — the same collision on the PROVISION side. `provides Walk[Element = Foreign.Elem]`
/// against a receiver sort declaring `Elem`: the name-anchored leaf join rewrites it to the
/// receiver's own `s.Elem` projection, so the provision threads a parameter it never named.
/// The shipped `Foreign.X` row passes only because `X` does not collide.
///
/// ON THIS FIXTURE THE TWO SPELLINGS GIVE ONE VERDICT WITH THE JOIN OR WITHOUT IT
/// (re-measured): the callback fixes the element before the provision is read, and the
/// mis-joined value is the callback's own. The row that fails under the join by name is
/// `wi_kssa4_spec_typed_value_test …a_foreign_parameter_of_the_same_name_is_not_the_
/// receivers`, where nothing but the provision says the element.
#[test]
fn provision_colliding_foreign_param_is_still_foreign() {
    let non_colliding = foreign_provision_binding("Foreign.X");
    assert_refused_naming(
        &non_colliding,
        &["its own member 'walk' does not fit 'test.mdwew.foreign.Walk.walk'"],
        "a provision binding naming a foreign sort's parameter must not be threaded",
    );
    let colliding = foreign_provision_binding("Foreign.Elem");
    assert!(
        !non_colliding.iter().chain(colliding.iter()).any(|e| e.contains("mk.")),
        "neither spelling of the foreign binding reaches the construction: \
         {non_colliding:#?} / {colliding:#?}"
    );
    assert_refused_naming(
        &colliding,
        &["its own member 'walk' does not fit 'test.mdwew.foreign.Walk.walk'"],
        "a foreign parameter that happens to SHARE a short name with one of the receiver \
         sort's is still foreign; it must be refused exactly as `Foreign.X` is",
    );
}
