//! WI-20260930-GJW9Z — A SPEC-OPERATION CALL IS CHARGED THE ROW ITS CALLER HOLDS ABSTRACTLY, as
//! its qualified twin is.
//!
//! `Sp2.touch(s: Self) effects {s.E}` is provided by `Car2`, whose `E` is `{EC}`. Called on `x:
//! Car2[V = Int64, EC = R]` from `use[R]`, the call incurs `R` — a row parameter of `use`, which
//! its body holds as a RIGID. `Car2.touch(x)` charged it; `Sp2.touch(x)` did not, so `use`
//! loaded declaring `effects {}`. The spec op's effect reached the call through the WI-357 /
//! WI-365 close, which drops the spec op's OWN still-unbound row variable at a concrete carrier,
//! and that close asked `effect_is_unresolved_var` (typing/carrier.rs) — which answered `true`
//! for every variable, a rigid too. The predicate now answers for a flexible variable alone.
//!
//! Inside the carrier the same: a member of `Car` calling `Sp.pick(s, x)` at another instance
//! (`x: Car[V = W, EC = R]`) was charged nothing, and at its own instance (`Sp.pick(x, s)`) not
//! its own `EC`; `Car.pick` charged both.
//!
//! AND WHERE THE CALL IS PINNED TO AN OVERRIDE, it is charged what the override declares, read at
//! the call (`dispatched_impl_effects_of`), in place of the spec op's own row
//! (`effects_of_pinned_call`, user decision 2026-10-20). Two things made that wrong:
//!
//!  * the override's effects were read with ITS OWN type parameters bound and its carrier's free
//!    (`override_at_call`): `Car2.touch(c: Self) effects {EC}` walked to an unbound `?EC` and was
//!    dropped as one, so over a spec op declaring no effect `Sp2.touch(x)` was charged nothing.
//!    The parameters of the override's declaring sort that its effects name are now kept from the
//!    arguments too, each met with the override's parameter at its position — so the receiver is
//!    the one at the spec's receiver position, and a callback is read at its slot — and from the
//!    expected type, for a result carrier no argument reaches;
//!  * a sibling call is placed at the caller's instance when nothing fixed a parameter (§8.1),
//!    so `peek(m)` in a member of `Box` over a `MutBox` providing `Box` without `Effect` read
//!    the spec op's `Effect` as the CALLER's — a rigid the narrowed predicate keeps. A pin drops
//!    every row variable of the spec op's own effects, flexible or rigid, and the override's say
//!    what the call incurs (`Modify[m]`, as `MutBox.peek(m)` is charged). Only an override row
//!    read WHOLE replaces anything: one left open at the call keeps the row the call held beside
//!    it. Where no override runs — the default body — the placement's row is charged.
//!
//! THE TICKET AS FILED was about the TYPE such a sibling call threads — the carrier's canonical
//! `?V` through the WI-606 fallback where the qualified call threaded the enclosing rigid, the
//! WI-424 fill reaching the one and not the other. WI-20261001-80ZV8 removed that fill, and the
//! two calls thread one type: [`a_sibling_call_threads_the_type_its_qualified_twin_does`] pins
//! it, and passes either way by design — its back-out is that ticket's, not this one's.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED by backing each part out, present but wrong, over this file's rows and the 1 566 rows
//! of the 79 suites that judge a dispatched or spec-op call's effects (each naming WI-357, WI-365,
//! WI-453 or WI-606, or asserting an `undeclared effect`, and the suites they import), and part
//! 0h — which the workspace run found — over `wi728` and `wi_2qz3f` as well. No row outside this
//! file moved under any part but 0h.
//!
//!  0. THE PREDICATE, WHOLE — a rigid read as unresolved again (`effect_is_unresolved_var`). 12
//!     FAIL: every row here but the controls, the ground row, the type row and the two whose pin
//!     has a filter of its own ([`a_call_pinned_to_an_override_is_charged_the_overrides_row`],
//!     [`a_call_pinned_by_an_instance_binding_is_charged_the_bound_impls_row`]).
//!     0h. A RIGID THE BODY DOES NOT HOLD — read as held. 5 FAIL, outside this file: the three
//!     `wi728_membership_operand_test` rows that consume `once(r) -> Relation`'s opened row
//!     (`r.isEmpty`), and `wi_2qz3f_const_receiver_test::a_relation_a_const_holds_is_drained_by_a_dot_on_it`
//!     and `wi_2qz3f_const_value_equation_test::a_value_a_macro_spliced_is_admitted`, which drain
//!     a const's — each refused "undeclared effect: ?E", a row no caller can name.
//!     0c. Its CARRIER — the `Value::Term` spelling alone. 0 FAIL, and 0 under
//!     `ANTHILL_TEST_NODE_CARRIER=1` beside the six rows of `wi4gbqv` / `wi9pgcm` that fail there
//!     at the parent commit as well: no program here carries such a variable to a close on
//!     another carrier. It reads through the view as every reader owes (rustland/CLAUDE.md).
//!
//!  Parts 1, 2, 4 and 5 back it out at ONE of its readers, the others answering as now:
//!
//!  1. The WI-365 call-side close of a DEFAULTED spec op. 2 FAIL:
//!     [`a_defaulted_spec_op_is_charged_the_callers_row`] and
//!     [`a_default_body_at_the_callers_instance_is_charged_the_callers_row`].
//!  2. The WI-357 close at a concrete carrier, before dispatch. 1 FAILS:
//!     [`a_call_deferred_to_the_callers_requirement_is_charged_its_row`] — the one path that
//!     returns with what this close left; a pin reads the override instead.
//!  4. `dispatched_impl_effects_of`' guard on a reduced projection. 1 FAILS:
//!     [`a_projected_override_row_is_charged_the_callers_row`].
//!  5. `dispatched_impl_effects_of`' filter of what it walked. 3 FAIL: the rows a pin charges
//!     through the override alone, its spec declaring nothing the caller holds —
//!     [`an_overrides_row_is_charged_where_the_spec_declares_none`],
//!     [`the_overrides_receiver_is_the_one_at_the_specs_receiver_position`] and
//!     [`a_result_carriers_row_is_read_off_the_expected_type`]. Where the spec's row holds the
//!     caller's rigid too, the dropped effect leaves the reading partial and the pin keeps the
//!     spec's row (part 7b), so the call is charged either way.
//!
//!  6. THE DECLARING SORT'S PARAMETERS KEPT (`override_at_call`) — its own only. The 3 of part 5,
//!     for the same reason.
//!     6b. … FROM THE EXPECTED TYPE (its step 4) — its own only. 1 FAILS:
//!     [`a_result_carriers_row_is_read_off_the_expected_type`].
//!  7. THE PIN DROPS A RIGID TOO (`effects_of_pinned_call`) — flexible only. 2 FAIL:
//!     [`a_call_pinned_to_an_override_is_charged_the_overrides_row`] (the placement's
//!     `Effect`) and [`a_call_pinned_by_an_instance_binding_is_charged_the_bound_impls_row`] (the
//!     bracket's `R`).
//!     7b. … ONLY WITH A ROW READ WHOLE — always. 1 FAILS:
//!     [`an_override_row_left_open_keeps_the_spec_row`].
//!  8. THE PIN AT EACH OF ITS SIX SITES — the override's row merged into what the call held, as
//!     before. The UNIQUE dispatch (`peek`) and the defaulted op's SUPPLIER (`peek2`) fail
//!     [`a_call_pinned_to_an_override_is_charged_the_overrides_row`]; the INSTANCE BINDING fails
//!     [`a_call_pinned_by_an_instance_binding_is_charged_the_bound_impls_row`]. Three fail no
//!     row: the two defaulted-call targets (a provision reached through the subtype relation,
//!     another sort's provision) run at a GROUND goal only, every spec parameter the row's too
//!     bound, so the spec op's own row holds no variable there for the pin to replace; and the
//!     no-candidate pin is reached by a spec whose requirement does not discharge at the
//!     carrier's row, which no call here reaches with a variable in the spec's row. They read the
//!     one rule so that no pin is charged by another.
//!
//! [`a_spec_call_is_charged_the_callers_row`], both sibling rows and
//! [`a_call_pinned_after_no_candidate_is_charged_its_row`] fail under part 0 and under no single
//! part: each call is charged its row by the override and by the spec's row it keeps. The
//! controls, [`a_ground_row_is_charged_both_ways`] and
//! [`a_sibling_call_threads_the_type_its_qualified_twin_does`] pass under every part, by design.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// The row `use` holds its argument at: its own row parameter `R`, or a ground row.
enum Row {
    Param,
    Ground,
}

/// What `Sp2.touch` declares and how `Car2` overrides it.
struct Touch {
    /// The spec operation's effect clause, `""` for none.
    spec_effects: &'static str,
    /// The override's signature.
    member: &'static str,
}

/// The spec op incurs the receiver's row, and so does its override.
const PROJECTED: Touch = Touch {
    spec_effects: " effects {s.E}",
    member: "touch(c: Self) -> Option[T = V] effects {EC}",
};

/// The spec op declares no effect; its override incurs its carrier's row — a widening the
/// override check leaves undecided for a parametric atom (`check_override_refinement`'s
/// fail-open), so the program loads and the call must charge what the override incurs.
const PURE_SPEC_CARRIER_ROW: Touch = Touch {
    spec_effects: "",
    member: "touch(c: Self) -> Option[T = V] effects {EC}",
};

/// … the same, its override's row a type parameter of its OWN, which its receiver binds.
const PURE_SPEC_OWN_ROW: Touch = Touch {
    spec_effects: "",
    member: "touch[Q](c: Car2[V = V, EC = Q]) -> Option[T = V] effects {Q}",
};

/// `Sp2.touch` over `Car2` shaped by `touch`, called as `call` from `use`, which declares
/// `declared` and takes `x` at `row`. `go` runs `use` on a `Car2` holding 7, which `touch`
/// answers.
fn outside_program(ns: &str, touch: &Touch, row: Row, declared: &str, call: &str) -> String {
    let Touch {
        spec_effects,
        member,
    } = touch;
    let (head, x_row, c_row) = match row {
        Row::Param => ("use[R]", "R", "{}"),
        Row::Ground => ("use", "{Error[DivisionByZero]}", "{Error[DivisionByZero]}"),
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Option, Error, DivisionByZero}}
  import anthill.prelude.Option.{{some, none}}

  sort Sp2
    sort T = ?
    effects E = ?
    operation touch(s: Self) -> Option[T = s.T]{spec_effects}
  end

  sort Car2
    sort V = ?
    effects EC = ?
    entity car2(v: V)
    provides Sp2[T = V, E = {{EC}}]
    operation {member} = some(c.v)
  end

  operation {head}(x: Car2[V = Int64, EC = {x_row}]) -> Int64 effects {declared} =
    match {call}
      case some(v) -> v
      case none() -> 0

  operation go() -> Int64 =
    let c: Car2[V = Int64, EC = {c_row}] = car2(v: 7)
    use(c)
end
"#
    )
}

/// THE SPEC CALL IS CHARGED THE CALLER'S ROW: `Sp2.touch(x)` over `x: Car2[…, EC = R]` incurs
/// `R`, and `use` declaring `{}` is refused naming it — as `Car2.touch(x)` is. The spec spelling
/// LOADED. The qualified twin passes either way by design: it takes no close.
#[test]
fn a_spec_call_is_charged_the_callers_row() {
    for call in ["Sp2.touch(x)", "Car2.touch(x)"] {
        assert_refused_naming(
            &load_errors(&outside_program(
                "wigjw9z.out_pure",
                &PROJECTED,
                Row::Param,
                "{}",
                call,
            )),
            &["use.effects", "undeclared effect: ?R"],
            &format!("`{call}` incurs `use`'s own `R`"),
        );
    }
}

/// … AND ITS CONTROL: `use` declaring `{R}` loads and runs, both ways — the row charged is `R`
/// and nothing else. Passes either way by design: it guards the row above against a fix that
/// charges more than the call incurs.
#[test]
fn a_spec_call_is_charged_the_callers_row_control() {
    for call in ["Sp2.touch(x)", "Car2.touch(x)"] {
        let ns = "wigjw9z.out_row";
        assert_eq!(
            run_src(
                &outside_program(ns, &PROJECTED, Row::Param, "{R}", call),
                &format!("{ns}.go")
            ),
            Ok(7),
            "`{call}`"
        );
    }
}

/// A GROUND ROW IS CHARGED AS BEFORE: over a `Car2` whose `EC` is `{Error[DivisionByZero]}` the
/// spec op's `s.E` eliminates, takes no close, and is charged both ways. Passes either way by
/// design.
#[test]
fn a_ground_row_is_charged_both_ways() {
    for call in ["Sp2.touch(x)", "Car2.touch(x)"] {
        assert_refused_naming(
            &load_errors(&outside_program(
                "wigjw9z.out_ground",
                &PROJECTED,
                Row::Ground,
                "{}",
                call,
            )),
            &[
                "use.effects",
                "undeclared effect: Error[T = DivisionByZero]",
            ],
            &format!("`{call}` over a ground row"),
        );
    }
}

/// AN OVERRIDE'S ROW IS CHARGED WHERE THE SPEC OP DECLARES NONE: the call is charged what the
/// override it dispatches to incurs — its carrier's row, which the receiver binds to `R`
/// ([`PURE_SPEC_CARRIER_ROW`]), or a row parameter of its own the receiver binds
/// ([`PURE_SPEC_OWN_ROW`]). The spec spelling LOADED under `effects {}`: the override's effects
/// were read with its own type parameters bound and its carrier's free, so `EC` walked to an
/// unbound variable and was dropped as one, and `Q` walked to the rigid `R` and was dropped as
/// unresolved. The qualified twin passes either way by design.
#[test]
fn an_overrides_row_is_charged_where_the_spec_declares_none() {
    for (shape, touch) in [
        ("carrier", &PURE_SPEC_CARRIER_ROW),
        ("own", &PURE_SPEC_OWN_ROW),
    ] {
        for call in ["Sp2.touch(x)", "Car2.touch(x)"] {
            assert_refused_naming(
                &load_errors(&outside_program(
                    "wigjw9z.pure_spec",
                    touch,
                    Row::Param,
                    "{}",
                    call,
                )),
                &["use.effects", "undeclared effect: ?R"],
                &format!("`{call}` over the override's {shape} row"),
            );
        }
    }
}

/// … AND ITS CONTROL: declaring `{R}`, each loads and runs. Passes either way by design.
#[test]
fn an_overrides_row_is_charged_where_the_spec_declares_none_control() {
    for touch in [&PURE_SPEC_CARRIER_ROW, &PURE_SPEC_OWN_ROW] {
        for call in ["Sp2.touch(x)", "Car2.touch(x)"] {
            let ns = "wigjw9z.pure_spec_ok";
            assert_eq!(
                run_src(
                    &outside_program(ns, touch, Row::Param, "{R}", call),
                    &format!("{ns}.go")
                ),
                Ok(7),
                "`{call}`"
            );
        }
    }
}

/// A CALL DEFERRED TO THE CALLER'S REQUIREMENT IS CHARGED ITS ROW: under `requires Sp2[T =
/// Int64, E = {R}]` — or with the row left unwritten — `Sp2.touch(x)` is read from the caller's
/// frame (WI-239) and returns before any dispatch re-derives its effects, so what the WI-357
/// close left of them is what it is charged. It LOADED declaring `{}`. The qualified twin
/// passes either way by design.
#[test]
fn a_call_deferred_to_the_callers_requirement_is_charged_its_row() {
    for req in ["Sp2[T = Int64, E = {R}]", "Sp2[T = Int64]"] {
        for call in ["Sp2.touch(x)", "Car2.touch(x)"] {
            let declared = format!("{{}} requires {req}");
            assert_refused_naming(
                &load_errors(&outside_program(
                    "wigjw9z.deferred",
                    &PROJECTED,
                    Row::Param,
                    &declared,
                    call,
                )),
                &["use.effects", "undeclared effect: ?R"],
                &format!("`{call}` under `requires {req}`"),
            );
        }
    }
}

/// … AND ITS CONTROL: declaring `{R}`, it loads and runs both ways — `go`'s `Car2` supplies the
/// requirement. Passes either way by design.
#[test]
fn a_call_deferred_to_the_callers_requirement_is_charged_its_row_control() {
    for call in ["Sp2.touch(x)", "Car2.touch(x)"] {
        let ns = "wigjw9z.deferred_ok";
        let src = outside_program(
            ns,
            &PROJECTED,
            Row::Param,
            "{R} requires Sp2[T = Int64, E = {R}]",
            call,
        );
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(7), "`{call}`");
    }
}

/// `Sp.pick(x: T, s: Self)` declaring no effect, over `Car.pick[W, R](x: Car[V = W, EC = R],
/// s: Self) effects {EC}`: the override's row is its RECEIVER's, the SECOND parameter, and the
/// first is a `Car` too. `use` declares `declared`; `go` runs it on two `Car`s.
fn second_receiver_program(ns: &str, declared: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Sp
    sort T = ?
    effects E = ?
    operation pick(x: T, s: Self) -> Int64
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car[V = ?, EC = ?], E = {{EC}}]
    operation pick[W, R](x: Car[V = W, EC = R], s: Self) -> Int64 effects {{EC}} = 1
  end

  operation use[R1, R2](a: Car[V = Int64, EC = R1], b: Car[V = Int64, EC = R2]) -> Int64 effects {declared} =
    {call}

  operation go() -> Int64 =
    let a: Car[V = Int64, EC = {{}}] = car(v: 1)
    let b: Car[V = Int64, EC = {{}}] = car(v: 2)
    use(a, b)
end
"#
    )
}

/// THE RECEIVER IS THE PARAMETER AT THE SPEC'S RECEIVER POSITION, not the first one the carrier
/// types: `Sp.pick(a, b)` incurs `b`'s `R2`, and declaring `{R1}` is refused naming it — both
/// ways. Read off the first `Car`-typed parameter, the override's `EC` stayed free and the spec
/// spelling LOADED declaring nothing. The qualified twin passes either way by design.
#[test]
fn the_overrides_receiver_is_the_one_at_the_specs_receiver_position() {
    for call in ["Sp.pick(a, b)", "Car.pick(a, b)"] {
        assert_refused_naming(
            &load_errors(&second_receiver_program("wigjw9z.recv2", "{R1}", call)),
            &["use.effects", "undeclared effect: ?R2"],
            &format!("`{call}` incurs the receiver's row"),
        );
    }
}

/// … AND ITS CONTROL: declaring `{R2}`, both load and run. Passes either way by design.
#[test]
fn the_overrides_receiver_is_the_one_at_the_specs_receiver_position_control() {
    for call in ["Sp.pick(a, b)", "Car.pick(a, b)"] {
        let ns = "wigjw9z.recv2_ok";
        assert_eq!(
            run_src(
                &second_receiver_program(ns, "{R2}", call),
                &format!("{ns}.go")
            ),
            Ok(1),
            "`{call}`"
        );
    }
}

/// A member of `Box` calling its own spec operation on a `MutBox` — which provides `Box` without
/// writing `Effect`, so nothing fixes it and the call is placed at the caller's instance (§8.1):
/// `viaMut` declares `declared` and answers `call`. `member` is `MutBox`'s, and `spec_op` the
/// spec operation's declaration. A LOAD VERDICT: `viaMut` writes `m`, a place only its caller
/// names.
fn box_program(ns: &str, spec_op: &str, member: &str, declared: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Modify, Modifiable}}

  sort Box
    effects Effect = ?
    {spec_op}
    operation viaMut(m: MutBox) -> Int64 effects {declared} = {call}
  end

  sort MutBox
    provides Modifiable[T = Self]
    entity mb(fd: Int64)
    provides Box
    {member}
  end
end
"#
    )
}

const BOX_PEEK: &str = "operation peek(b: Self) -> Int64 effects Effect";
const BOX_PEEK2: &str = "operation peek2(b: Self) -> Int64 effects Effect = 0";
const MUTBOX_PEEK: &str = "operation peek(b: MutBox) -> Int64 effects Modify[b] =\n      match b\n        case mb(x) -> x";
const MUTBOX_PEEK2: &str = "operation peek2(b: MutBox) -> Int64 effects Modify[b] =\n      match b\n        case mb(x) -> x";

/// A CALL PINNED TO AN OVERRIDE IS CHARGED THE OVERRIDE'S ROW, NOT ITS PLACEMENT'S: `peek(m)`
/// dispatches to `MutBox.peek`, which incurs `Modify[m]`, and `viaMut` declaring that loads —
/// spelled bare, through the spec, and qualified; and so does a DEFAULTED spec operation the
/// carrier backs with a member (`peek2`). Read through the placement, the spec op's `Effect` was
/// the caller's, charged beside `Modify[m]`: refused, where `MutBox.peek(m)` loaded. The
/// qualified spellings pass either way by design.
#[test]
fn a_call_pinned_to_an_override_is_charged_the_overrides_row() {
    for (spec_op, member, calls) in [
        (
            BOX_PEEK,
            MUTBOX_PEEK,
            ["peek(m)", "Box.peek(m)", "MutBox.peek(m)"],
        ),
        (
            BOX_PEEK2,
            MUTBOX_PEEK2,
            ["peek2(m)", "Box.peek2(m)", "MutBox.peek2(m)"],
        ),
    ] {
        for call in calls {
            let errs = load_errors(&box_program(
                "wigjw9z.box",
                spec_op,
                member,
                "Modify[m]",
                call,
            ));
            assert!(errs.is_empty(), "`{call}` declaring `Modify[m]`: {errs:#?}");
        }
    }
}

/// … AND ITS CONTROL: declaring nothing, every one of them is refused naming `Modify[m]` — the pin
/// charges the override's row; it does not drop the call's. Passes either way by design.
#[test]
fn a_call_pinned_to_an_override_is_charged_the_overrides_row_control() {
    for (spec_op, member, call) in [
        (BOX_PEEK, MUTBOX_PEEK, "peek(m)"),
        (BOX_PEEK, MUTBOX_PEEK, "MutBox.peek(m)"),
        (BOX_PEEK2, MUTBOX_PEEK2, "peek2(m)"),
    ] {
        assert_refused_naming(
            &load_errors(&box_program(
                "wigjw9z.box_pure",
                spec_op,
                member,
                "{}",
                call,
            )),
            &["viaMut.effects", "undeclared effect: Modify[T = m]"],
            &format!("`{call}` declaring nothing"),
        );
    }
}

/// WHERE NO OVERRIDE RUNS, THE PLACEMENT'S ROW IS CHARGED (user decision, 2026-10-20): `peek2(m)`
/// over a `MutBox` that writes no `peek2` runs the DEFAULT body, declared `effects Effect`, and the
/// call is at the caller's instance (§8.1) — so `viaMut` declaring only `Modify[m]` is refused
/// naming `Effect`, and declaring it loads. It LOADED before this ticket, the close dropping the
/// caller's rigid as if it were the spec op's unbound row.
#[test]
fn a_default_body_at_the_callers_instance_is_charged_the_callers_row() {
    assert_refused_naming(
        &load_errors(&box_program(
            "wigjw9z.box_dflt",
            BOX_PEEK2,
            "",
            "Modify[m]",
            "peek2(m)",
        )),
        &["viaMut.effects", "undeclared effect: ?Effect"],
        "the default body's `Effect`, at the caller's instance",
    );
    let errs = load_errors(&box_program(
        "wigjw9z.box_dflt_ok",
        BOX_PEEK2,
        "",
        "{Effect}",
        "peek2(m)",
    ));
    assert!(errs.is_empty(), "declaring `Effect`: {errs:#?}");
}

/// A result-carrier spec operation `CpsM.unit` whose instance for `Option` binds it to
/// `optionUnit`, declared `impl_effects`; `use[R]` declares nothing and answers `call`. A LOAD
/// VERDICT: `use`'s `R` is fixed by no argument, so nothing can call it.
fn instance_bound_program(ns: &str, impl_effects: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.Option.{{some}}
  import anthill.prelude.{{Option, Int64, Error}}
  import {ns}.CpsM.{{unit}}
  sort CpsM[F[T]]
    effects E = ?
    operation unit[A](a: A) -> F[T = A] effects E
  end
  operation optionUnit[A](a: A) -> Option[T = A]{impl_effects} = some(a)
  operation use[R]() -> Option[T = Int64] effects {{}} = {call}
end

namespace anthill.prelude.Option
  import {ns}.CpsM
  provides CpsM[F = Self, unit = {ns}.optionUnit]
end
"#
    )
}

/// A CALL PINNED BY AN INSTANCE'S BINDING IS CHARGED THE BOUND IMPL'S ROW: `unit(42)` at
/// `Option` runs `optionUnit`, which incurs nothing, so a `use` declaring nothing loads — bare,
/// through the spec, with the spec's row written at the caller's `R` by a bracket, and as the
/// qualified `optionUnit(42)`. The spec spellings were REFUSED: the spec op's unbound row as
/// "undeclared effect: ?_", the bracket's as `?R`, beside an impl that incurs neither. The
/// qualified twin passes either way by design.
#[test]
fn a_call_pinned_by_an_instance_binding_is_charged_the_bound_impls_row() {
    for call in [
        "unit(42)",
        "CpsM.unit(42)",
        "unit[E = R](42)",
        "optionUnit(42)",
    ] {
        let errs = load_errors(&instance_bound_program("wigjw9z.inst", "", call));
        assert!(
            errs.is_empty(),
            "`{call}` over a pure bound impl: {errs:#?}"
        );
    }
}

/// … AND ITS CONTROL: the bound impl declaring `effects Error`, every spelling is refused naming
/// it — the pin charges the impl's row; it does not drop the call's. Passes either way by design.
#[test]
fn a_call_pinned_by_an_instance_binding_is_charged_the_bound_impls_row_control() {
    for call in ["unit(42)", "unit[E = R](42)", "optionUnit(42)"] {
        assert_refused_naming(
            &load_errors(&instance_bound_program(
                "wigjw9z.inst_err",
                " effects Error",
                call,
            )),
            &["use.effects", "undeclared effect: Error"],
            &format!("`{call}` over an impl incurring `Error`"),
        );
    }
}

/// A result-carrier spec operation `Mk.make() -> C effects E`, provided by `Car` with `E = {EC}`
/// and a member `make() -> Self effects {EC}`, which no argument binds: `use[R]` declares
/// `declared` and binds `let c: {annot} = {call}`. A LOAD VERDICT: `use`'s `R` is fixed by no
/// argument, so nothing can call it.
fn result_carrier_program(ns: &str, annot: &str, call: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Mk
    sort C = ?
    effects E = ?
    operation make() -> C effects E
  end
  sort Car
    effects EC = ?
    entity car(n: Int64)
    provides Mk[C = Self, E = {{EC}}]
    operation make() -> Self effects {{EC}} = car(n: 1)
  end
  operation use[R]() -> Int64 effects {declared} =
    let c: {annot} = {call}
    1
end
"#
    )
}

/// A RESULT CARRIER'S ROW IS READ OFF THE EXPECTED TYPE: `let c: Car[EC = R] = Mk.make()` runs
/// `Car.make`, whose `EC` only the annotation fixes, and is charged `R` — refused declaring
/// `{}`, as `Car.make()` is, and loads declaring `{R}`. The spec spelling LOADED declaring `{}`:
/// the override's `EC` was read with its own type parameters only, so it walked to an unbound
/// variable. The qualified twin passes either way by design.
#[test]
fn a_result_carriers_row_is_read_off_the_expected_type() {
    for call in ["Mk.make()", "Car.make()"] {
        assert_refused_naming(
            &load_errors(&result_carrier_program(
                "wigjw9z.mk",
                "Car[EC = R]",
                call,
                "{}",
            )),
            &["use.effects", "undeclared effect: ?R"],
            &format!("`{call}` at `Car[EC = R]`"),
        );
        let errs = load_errors(&result_carrier_program(
            "wigjw9z.mk_ok",
            "Car[EC = R]",
            call,
            "{R}",
        ));
        assert!(errs.is_empty(), "`{call}` declaring `R`: {errs:#?}");
    }
}

/// AN OVERRIDE'S ROW LEFT OPEN AT THE CALL DOES NOT REPLACE THE SPEC'S: at `Car[EC = ?]` nothing
/// fixes `Car.make`'s `EC`, so its row is not read whole, and `Mk.make[E = R]()` keeps the row
/// its bracket wrote — refused declaring `{}`, loads declaring `{R}`. Replaced by an override
/// row that resolved to nothing, the call was charged nothing; it LOADED declaring `{}` before
/// this ticket as well, the close dropping the bracket's rigid. `Car[EC = ?]` is `Car`
/// (WI-20261024-DK83Q): FAILS with the `let` annotation handed to the value as written, its
/// slot left out unbound — "missing `requires Mk[E = …]`" declaring `{R}`.
#[test]
fn an_override_row_left_open_keeps_the_spec_row() {
    assert_refused_naming(
        &load_errors(&result_carrier_program(
            "wigjw9z.mk_open",
            "Car[EC = ?]",
            "Mk.make[E = R]()",
            "{}",
        )),
        &["use.effects", "undeclared effect: ?R"],
        "the bracket's `R`, beside an override row nothing fixes",
    );
    let errs = load_errors(&result_carrier_program(
        "wigjw9z.mk_open_ok",
        "Car[EC = ?]",
        "Mk.make[E = R]()",
        "{R}",
    ));
    assert!(errs.is_empty(), "declaring `R`: {errs:#?}");
}

/// `Sp3.touch` with a DEFAULT body, provided by `Car3` with `member` (`""` for none, so the
/// default runs), called from `use[R]`, which declares `declared`. `go` runs `use` on a `Car3`
/// holding 7: the override answers it, the default answers 0.
fn defaulted_program(ns: &str, member: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Option}}
  import anthill.prelude.Option.{{some, none}}

  sort Sp3
    sort T = ?
    effects E = ?
    operation touch(s: Self) -> Option[T = s.T] effects E = none
  end

  sort Car3
    sort V = ?
    effects EC = ?
    entity car3(v: V)
    provides Sp3[T = V, E = {{EC}}]
    {member}
  end

  operation use[R](x: Car3[V = Int64, EC = R]) -> Int64 effects {declared} =
    match Sp3.touch(x)
      case some(v) -> v
      case none() -> 0

  operation go() -> Int64 =
    let c: Car3[V = Int64, EC = {{}}] = car3(v: 7)
    use(c)
end
"#
    )
}

const CAR3_TOUCH: &str = "operation touch(c: Self) -> Option[T = V] effects {EC} = some(c.v)";

/// A DEFAULTED SPEC OP IS CHARGED THE CALLER'S ROW, whether the carrier overrides it or its
/// default runs: `Sp3.touch(x)` incurs `R`. It LOADED under `effects {}`, the row closed by the
/// WI-365 call-side close a defaulted spec op takes.
#[test]
fn a_defaulted_spec_op_is_charged_the_callers_row() {
    for (shape, member) in [("overridden", CAR3_TOUCH), ("default", "")] {
        assert_refused_naming(
            &load_errors(&defaulted_program("wigjw9z.dflt", member, "{}")),
            &["use.effects", "undeclared effect: ?R"],
            &format!("the {shape} `Sp3.touch(x)`"),
        );
    }
}

/// … AND ITS CONTROL: declaring `{R}`, both run — the override answering 7, the default 0.
/// Passes either way by design.
#[test]
fn a_defaulted_spec_op_is_charged_the_callers_row_control() {
    for (member, answer) in [(CAR3_TOUCH, 7), ("", 0)] {
        let ns = "wigjw9z.dflt_ok";
        assert_eq!(
            run_src(&defaulted_program(ns, member, "{R}"), &format!("{ns}.go")),
            Ok(answer),
            "`{member}`"
        );
    }
}

/// `Sp2.touch` over a stream argument as well, whose row it incurs: the override's `st.E` is a
/// PROJECTION, eliminated against the caller's `y: Strm[…, E = Q]`. `use` declares `declared`.
/// A LOAD VERDICT: `Strm` has no constructor.
fn stream_program(ns: &str, declared: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option}}
  import anthill.prelude.Option.{{some, none}}

  sort Strm
    sort T = ?
    effects E = ?
    operation obs(s: Self) -> Bool effects s.E = true
  end

  sort Sp2
    sort T = ?
    effects E = ?
    operation touch(s: Self, st: Strm[T = Int64]) -> Option[T = s.T] effects {{s.E, st.E}}
  end

  sort Car2
    sort V = ?
    effects EC = ?
    entity car2(v: V)
    provides Sp2[T = V, E = {{EC}}]
    operation touch(c: Self, st: Strm[T = Int64]) -> Option[T = V] effects {{EC, st.E}} = some(c.v)
  end

  operation use[R, Q](x: Car2[V = Int64, EC = R], y: Strm[T = Int64, E = Q]) -> Int64 effects {declared} =
    match {call}
      case some(v) -> v
      case none() -> 0
end
"#
    )
}

/// TWO CALLER ROWS, ONE THROUGH A PROJECTION: `touch(x, y)` incurs `x`'s `R` and `y`'s `Q`, and
/// declaring either alone is refused naming the other — both ways; declaring both loads. The
/// spec spelling LOADED declaring either.
#[test]
fn a_projected_override_row_is_charged_the_callers_row() {
    for call in ["Sp2.touch(x, y)", "Car2.touch(x, y)"] {
        for (declared, missing) in [("{R}", "?Q"), ("{Q}", "?R")] {
            assert_refused_naming(
                &load_errors(&stream_program("wigjw9z.strm", declared, call)),
                &["use.effects", &format!("undeclared effect: {missing}")],
                &format!("`{call}` declaring `{declared}`"),
            );
        }
        let errs = load_errors(&stream_program("wigjw9z.strm_ok", "{R, Q}", call));
        assert!(errs.is_empty(), "`{call}` declaring both: {errs:#?}");
    }
}

/// WI-606's witness: `MappedFinite.collect` drains a `Mapped` by the UNQUALIFIED
/// `splitFirst(m)`, whose dispatch finds no candidate (the spec's `requires EffectsRuntime[E]`
/// does not discharge at the witness's own abstract rows) and is pinned to the override. Its row
/// is `{ES, EF}`, the witness's own — and declaring `ES` alone, or `EF` alone, is refused naming
/// the other, as the qualified `Mapped.splitFirst(m)` is. The unqualified call LOADED declaring
/// either. A LOAD VERDICT, as the WI-606 row is.
#[test]
fn a_call_pinned_after_no_candidate_is_charged_its_row() {
    use crate::wi606_unqualified_dispatch_return_threading_test::SRC;
    let declared_at = "-> List[T = T] effects {ES, EF} =\n      match splitFirst(m)";
    assert_eq!(
        SRC.matches(declared_at).count(),
        1,
        "the WI-606 fixture moved"
    );
    for call in ["splitFirst(m)", "Mapped.splitFirst(m)"] {
        for (declared, missing) in [("{ES}", "?EF"), ("{EF}", "?ES")] {
            let src = SRC.replace(
                declared_at,
                &format!("-> List[T = T] effects {declared} =\n      match {call}"),
            );
            assert_refused_naming(
                &load_errors(&src),
                &["collect.effects", &format!("undeclared effect: {missing}")],
                &format!("`{call}` declaring `{declared}`"),
            );
        }
    }
}

/// `Sp.pick(x: T, s: Self)` — the receiver SECOND — provided by `Car`, whose `pick` takes `x` at
/// an instance of its own (`W`, `R`) and the receiver at this one. `probe`, a SIBLING member of
/// `Car`, declares `declared` and calls `call`; `go` runs `probe` on two `Car`s, and `probe`
/// answers 1 for the `some` that `pick` returns.
fn sibling_program(ns: &str, declared: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Option, Pair}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Sp
    sort T = ?
    effects E = ?
    operation pick(x: T, s: Self) -> Option[T = Pair[A = s.T, B = Sp[T = s.T, E = s.E]]] effects s.E
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car[V = ?, EC = ?], E = {{EC}}]
    operation pick[W, R](x: Car[V = W, EC = R], s: Self) -> Option[T = Pair[A = Car[V = W, EC = R], B = Car[V = V, EC = EC]]] effects {{EC}} =
      some(pair(x, s))
    operation probe[W, R](x: Car[V = W, EC = R], s: Self) -> Int64 effects {declared} =
      match {call}
        case some(_) -> 1
        case none() -> 0
  end

  operation go() -> Int64 =
    let a: Car[V = Int64, EC = {{}}] = car(v: 1)
    let b: Car[V = Int64, EC = {{}}] = car(v: 2)
    Car.probe(a, b)
end
"#
    )
}

/// A SIBLING CALL AT ANOTHER INSTANCE IS CHARGED THAT INSTANCE'S ROW: `pick(s, x)` dispatches on
/// `x`, whose `EC` is `probe`'s own `R`, and `probe` declaring only its `EC` is refused naming
/// `R` — both ways. The spec spelling LOADED. The qualified twin passes either way by design.
#[test]
fn a_sibling_call_at_another_instance_is_charged_its_row() {
    for call in ["Sp.pick(s, x)", "Car.pick(s, x)"] {
        assert_refused_naming(
            &load_errors(&sibling_program("wigjw9z.sib_other", "{EC}", call)),
            &["probe.effects", "undeclared effect: ?R"],
            &format!("`{call}` incurs the row of `x`'s instance"),
        );
    }
}

/// … AT ITS OWN INSTANCE, ITS OWN ROW: `pick(x, s)` dispatches on `s`, and `probe` declaring
/// `{}` is refused naming its `EC` — both ways. The spec spelling LOADED. The qualified twin
/// passes either way by design.
#[test]
fn a_sibling_call_at_the_callers_instance_is_charged_its_row() {
    for call in ["Sp.pick(x, s)", "Car.pick(x, s)"] {
        assert_refused_naming(
            &load_errors(&sibling_program("wigjw9z.sib_here", "{}", call)),
            &["probe.effects", "undeclared effect: ?EC"],
            &format!("`{call}` incurs this instance's row"),
        );
    }
}

/// … AND THEIR CONTROL: declaring the row each call incurs, every one loads and runs. Passes
/// either way by design: it guards the two rows above against a charge of more than the call
/// incurs.
#[test]
fn a_sibling_call_is_charged_its_row_control() {
    for (declared, call) in [
        ("{R}", "Sp.pick(s, x)"),
        ("{R}", "Car.pick(s, x)"),
        ("{EC}", "Sp.pick(x, s)"),
        ("{EC}", "Car.pick(x, s)"),
    ] {
        let ns = "wigjw9z.sib_ok";
        assert_eq!(
            run_src(&sibling_program(ns, declared, call), &format!("{ns}.go")),
            Ok(1),
            "`{call}` declaring `{declared}`"
        );
    }
}

/// THE TICKET AS FILED: a sibling call through the spec op threads the type its qualified twin
/// does, at this instance and at another. The annotation each call meets is the type it has —
/// in the caller's rigids, `V`/`EC` and `W`/`R` — and the same annotation with `V = Int64` where
/// a rigid stands is refused: a call that threaded a flexible variable (the carrier's canonical
/// `?V`, as the WI-606 fallback once did) would bind it and load. Passes either way by design;
/// the type half was WI-20261001-80ZV8's.
#[test]
fn a_sibling_call_threads_the_type_its_qualified_twin_does() {
    let here = "Option[T = Pair[A = Car[V = W, EC = R], B = Car[V = V, EC = EC]]]";
    let other = "Option[T = Pair[A = Car[V = V, EC = EC], B = Car[V = W, EC = R]]]";
    // `probe`'s body: the call `let` at an annotation, then `probe`'s answer.
    let at = |annot: &str, call: &str| {
        sibling_program("wigjw9z.ty", "{EC, R}", "none").replace(
            "match none\n        case some(_) -> 1\n        case none() -> 0",
            &format!("let r: {annot} = {call}\n      1"),
        )
    };
    for (annot, args, rigid) in [
        (here, "x, s", "B = Car[V = V,"),
        (other, "s, x", "B = Car[V = W,"),
    ] {
        let wrong = annot.replace(rigid, "B = Car[V = Int64,");
        assert_ne!(wrong, annot, "the wrong annotation rewrote nothing");
        for q in ["Sp", "Car"] {
            let call = format!("{q}.pick({args})");
            assert_eq!(
                run_src(&at(annot, &call), "wigjw9z.ty.go"),
                Ok(1),
                "`{call}` at `{annot}`"
            );
            assert_refused_naming(
                &load_errors(&at(&wrong, &call)),
                &["r.annotation", "B = Car[V = Int64"],
                &format!("`{call}` at a wrong `V`"),
            );
        }
    }
}
