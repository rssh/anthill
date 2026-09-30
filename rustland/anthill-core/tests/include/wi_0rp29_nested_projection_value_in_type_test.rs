//! WI-20260929-0RP29 — a type projection NESTED in a type grounds to a type holding a value
//! and is eliminated, as its `N = Bool` twin is; and WI-606's fallback eliminates the
//! overriding operation's own projections instead of threading them.
//!
//! With `xs: List[T = Buf[T = Int64, N = 3]]` the projection `xs.T` is the occurrence-carried
//! `Buf[…, N = 3]` (a type holding a VALUE, WI-477). The elimination had one walk per
//! carrier, and the term walk answered a `TermId`, so wherever that projection sat INSIDE a
//! term-carried type it was refused "type projection resolved to a non-term carrier, which is
//! not yet supported": `List.splitFirst(xs)` and `xs.splitFirst()` (`Option[Pair[A = xs.T,
//! …]]`), a user's `unboxOpt(b: Box) -> Option[T = b.T]`, a requirement written at a
//! projection (`requires Desc[T = x.E]`), and every other form holding one — a named tuple,
//! an arrow, an effect row. The top-level `-> xs.T` ran, and so did every `N = Bool` twin.
//! `Stream.splitFirst(xs)` failed differently: the refusal sent the call to WI-606's
//! fallback, which threaded `List.splitFirst`'s return with ITS `xs.T` in it, so the caller
//! was told "expected Buf[T = Int64, N = 3], got xs.T" — `xs` being the override's own
//! parameter. The elimination is now ONE walk over `extract_type` on any carrier; the
//! fallback eliminates the override's projections against the call.
//!
//! Every row that can RUNS: an operation answers a number that names what was reached (the
//! element's `v`, a provider's tag), on the value-in-type element AND on its `N = Bool` twin
//! where the row has one, so a row says the two now agree. The rows that assert a LOAD
//! verdict say at their site why nothing can run.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED by applying each part's back-out, present but wrong, and running this file's 21
//! rows with `wi_s8cbv_projection_requirement_test` and
//! `wi_ekwdc_carrier_requires_instantiation_test`:
//!
//! 1. THE WALK — `projection.rs` / `result.rs` at the parent commit (a walk per carrier). 16
//!    FAIL: every row here but the five that key and re-key the fallback's override, each
//!    refused because the projection did not eliminate ("resolved to a non-term carrier", or
//!    for a requirement the WI-20260909-S8CBV refusal of the projection that survived). The
//!    four controls fail with them — [`another_value_is_refused`],
//!    [`a_wrong_value_through_the_fallback_is_refused`],
//!    [`an_effect_row_holding_a_value_still_counts_it`],
//!    [`a_requirement_no_provider_covers_is_refused`] — refused, but for that reason, before any
//!    value or label is compared, so none names what it must.
//! 2. THE SPEC-VIEW ARM — a `SortView` rebuilt as an application again, its `sort` slot
//!    dropped. 7 FAIL: the three requirement rows here and four `wi_s8cbv` rows, whose
//!    requirement then names no spec (eval dies `__req_desc not bound`).
//! 3. THE SPEC VIEW LOWERED — rebuilt on the loader's carrier instead (an entity once a
//!    binding holds a value). 3 FAIL: the three requirement rows. The `wi_s8cbv` rows' bindings
//!    are terms, and pass.
//! 4. δ BEFORE σ IN THE FALLBACK — σ first. 1 FAILS:
//!    [`the_fallback_over_a_carrier_written_with_its_parameters`].
//! 5. THE FALLBACK KEYED BY POSITION ONLY — the receiver's type also keyed to the first
//!    carrier-typed override parameter. 2 FAIL: [`the_fallback_keys_the_override_by_position`],
//!    [`the_fallback_refuses_the_first_arguments_wrong_element`].
//! 6. THE FALLBACK'S RE-KEY of an override parameter — dropped. 2 FAIL:
//!    [`an_overrides_own_parameter_is_rekeyed`] and its control.
//! 7. THE FALLBACK'S ELIMINATION — the override's return threaded as written. 5 FAIL: the four
//!    fallback rows that reach an override's projection, and
//!    `wi_ekwdc…::a_receiver_projection_across_a_hop_is_eliminated`.
//! 8. THE GUARD'S VALUE-LIST SPINE — the term list kept on the rebuilt occurrence. 1 FAILS:
//!    [`a_guard_survives_the_rebuild`], its goal no longer printed.
//! 9. THE CARRIER-NEUTRAL `denoted` RE-KEY — occurrences only, as before. 0 FAIL, by design:
//!    no program found puts a term-carried `denoted` naming a parameter into an eliminated type
//!    (a signature's rides the occurrence). The arm is carrier-neutral so that such a one would
//!    not keep the callee's parameter where its occurrence twin is re-keyed.
//!
//! Every row fails under at least one part.

use crate::common::{assert_refused_naming, try_load_kb_with};
use anthill_core::eval::{builtins, Interpreter, Value};

/// `Buf[T, N]` (`N` the value-in-type argument), `val` over the element at `N = {n}`, and
/// `Box[T]`. `body` follows.
fn program(ns: &str, n: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List, Option, Pair, Stream}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Box
    sort T = ?
    entity box(item: T)
  end

  operation val(b: Buf[T = Int64, N = {n}]) -> Int64 = b.v
{body}
end
"#
    )
}

fn load_errors(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// Load `src` and call `entry`: its `Int64`, or why it did not load or run.
fn run_src(src: &str, entry: &str) -> Result<i64, String> {
    let kb = try_load_kb_with(src).map_err(|errs| errs.join("\n"))?;
    let mut interp = Interpreter::new(kb);
    builtins::register_standard_builtins(&mut interp).expect("register standard eval builtins");
    match interp.call(entry, &[]) {
        Ok(Value::Int(v)) => Ok(v),
        other => Err(format!("`{entry}` did not run to an Int64: {other:?}")),
    }
}

/// `program(ns, n, body(n))`, `ns.go()` run.
fn run(ns: &str, n: &str, body: &dyn Fn(&str) -> String) -> Result<i64, String> {
    run_src(&program(ns, n, &body(n)), &format!("{ns}.go"))
}

/// The value-in-type element (`N = 3`) and its `N = Bool` twin both run to `expected`.
fn runs_as_its_twin(ns: &str, expected: i64, body: impl Fn(&str) -> String) {
    assert_eq!(
        run(&format!("{ns}_bool"), "Bool", &body),
        Ok(expected),
        "{ns}: the N = Bool twin"
    );
    assert_eq!(
        run(&format!("{ns}_value"), "3", &body),
        Ok(expected),
        "{ns}: the element holding a value, N = 3"
    );
}

/// `first` peels a `List` of `Buf`s at `N = {n}` with `peel` and hands the head to `val`.
fn first_op(peel: &str, n: &str) -> String {
    format!(
        "  operation first(xs: List[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
         match {peel}\n      \
         case some(pair(b, _)) -> val(b)\n      \
         case none() -> 0\n"
    )
}

/// [`first_op`], run on a one-element list.
fn list_first(peel: &str, n: &str) -> String {
    format!(
        "{}  operation go() -> Int64 = first(cons(buf(v: 7), nil))",
        first_op(peel, n)
    )
}

// ── the ticket's spellings ────────────────────────────────────────────────────────────

/// `List.splitFirst -> Option[Pair[A = xs.T, B = List[xs.T]]]`, called qualified.
#[test]
fn the_qualified_list_call() {
    runs_as_its_twin("wi0rp29.list_q", 7, |n| list_first("List.splitFirst(xs)", n));
}

/// … and as a dot call.
#[test]
fn the_dot_call() {
    runs_as_its_twin("wi0rp29.list_dot", 7, |n| list_first("xs.splitFirst()", n));
}

/// `Stream.splitFirst -> Option[Pair[A = s.T, B = Stream[T = s.T, E = s.E]]]`, dispatched to
/// `List`'s — the spelling the fallback's leak reached on the parent commit.
#[test]
fn the_stream_spec_call() {
    runs_as_its_twin("wi0rp29.stream", 7, |n| list_first("Stream.splitFirst(xs)", n));
}

/// The TAIL keeps the element too — `B = List[xs.T]`, the return's second projection: handed
/// on to `first`, which takes the value-in-type list, and peeled again.
#[test]
fn the_tail_keeps_the_element() {
    runs_as_its_twin("wi0rp29.tail", 7, |n| {
        format!(
            "{}  operation second(xs: List[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
             match List.splitFirst(xs)\n      \
             case some(pair(_, t)) -> first(t)\n      \
             case none() -> 0\n  \
             operation go() -> Int64 = second(cons(buf(v: 1), cons(buf(v: 7), nil)))",
            first_op("List.splitFirst(xs)", n)
        )
    });
}

/// Not the stdlib's: a user's projection nested in a return, beside the top-level
/// `unbox(b: Box) -> b.T` that always ran.
#[test]
fn a_users_projection_nested_in_a_return() {
    runs_as_its_twin("wi0rp29.box", 7, |n| {
        format!(
            "  operation unboxOpt(b: Box) -> Option[T = b.T] = some(b.item)\n  \
             operation first(x: Box[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
             match unboxOpt(x)\n      \
             case some(b) -> val(b)\n      \
             case none() -> 0\n  \
             operation go() -> Int64 = first(box(buf(v: 7)))"
        )
    });
}

/// THE CONTROL: the element is the type the list holds, value and all — a list at `N = 4`
/// handed to `val` at `N = 3` is refused naming both. A projection that grounded to a
/// wildcard would let it through.
#[test]
fn another_value_is_refused() {
    let body = "  operation first(xs: List[T = Buf[T = Int64, N = 4]]) -> Int64 =\n    \
                match List.splitFirst(xs)\n      \
                case some(pair(b, _)) -> val(b)\n      \
                case none() -> 0";
    assert_refused_naming(
        &load_errors(&program("wi0rp29.other", "3", body)),
        &["Buf[T = Int64, N = 3]", "Buf[T = Int64, N = 4]"],
        "an element at N = 4 where val takes N = 3",
    );
}

// ── the other forms a projection can sit in ───────────────────────────────────────────

/// In a named tuple: `(e: b.T, n: Int64)`, answering `v + n`.
#[test]
fn a_named_tuple_holding_the_projection() {
    runs_as_its_twin("wi0rp29.tuple", 8, |n| {
        format!(
            "  operation tag(b: Box) -> Option[T = (e: b.T, n: Int64)] = some((e: b.item, n: 1))\n  \
             operation first(x: Box[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
             match tag(x)\n      \
             case some((e, k)) -> val(e) + k\n      \
             case none() -> 0\n  \
             operation go() -> Int64 = first(box(buf(v: 7)))"
        )
    });
}

/// In an arrow's result: `(u: Int64) -> b.T`, applied.
#[test]
fn an_arrow_holding_the_projection() {
    runs_as_its_twin("wi0rp29.arrow", 7, |n| {
        format!(
            "  operation getter(b: Box) -> Option[T = (u: Int64) -> b.T] = \
             some(lambda (u: Int64) -> b.item)\n  \
             operation first(x: Box[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
             match getter(x)\n      \
             case some(f) -> val(f(0))\n      \
             case none() -> 0\n  \
             operation go() -> Int64 = first(box(buf(v: 7)))"
        )
    });
}

/// In an effect row nested in a type: `relay`'s `E = {s.E, Error[EmptyStream]}`, where `s.E`
/// grounds to `{Modify[p]}` — a row holding a value. `use` declares `declared`.
///
/// A LOAD VERDICT, not a run: `Strm` has no constructor and `Producer` no instance, so
/// nothing here CAN run — what is measured is the typer's verdict on the row, the thing the
/// refusal got wrong.
fn effect_row_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Modify, EffectsRuntime, Int64, Error, EmptyStream}}
  sort Strm
    sort T = ?
    effects E = ?
    operation obs(s: Strm) -> Bool effects s.E = true
  end
  sort Producer
    operation eff_stream(p: Producer) -> Strm[T = Int64, E = {{Modify[p]}}]
    operation relay(s: Strm) -> Strm[T = s.T, E = {{s.E, Error[EmptyStream]}}]
  end
  operation use(p: Producer) -> Bool effects {{{declared}}} =
    Strm.obs(Producer.relay(Producer.eff_stream(p)))
end
"#
    )
}

/// Declaring the whole row loads. Refused before the walk, as the non-term carrier.
#[test]
fn an_effect_row_holding_a_value_loads() {
    let errs = load_errors(&effect_row_program(
        "wi0rp29.row",
        "Modify[p], Error[EmptyStream]",
    ));
    assert!(errs.is_empty(), "the declared row covers the call: {errs:#?}");
}

/// THE CONTROL: the row still carries `Modify[p]` after the rebuild — leaving it undeclared
/// is refused naming it. A rebuild that dropped the label would load this.
#[test]
fn an_effect_row_holding_a_value_still_counts_it() {
    assert_refused_naming(
        &load_errors(&effect_row_program("wi0rp29.row_short", "Error[EmptyStream]")),
        &["undeclared effect", "Modify[T = p]"],
        "a row holding Modify[p], declared without it",
    );
}

/// A GUARDED effect keeps its guard through the rebuild: `Error[b.T] :- eq(b, b)`, the label
/// grounding to the value-in-type element. The stamped type is PRINTED by a compile-time
/// macro that raises it as its message — the reader is the `TermPrinter` every query and
/// reflect answer goes through.
///
/// A LOAD VERDICT BY CONSTRUCTION: the macro's raise is how the type reaches a string, so the
/// "refusal" IS the measurement. Asserted on both twins, for the guard's goal.
#[test]
fn a_guard_survives_the_rebuild() {
    for (ns, n) in [("wi0rp29.guard_bool", "Bool"), ("wi0rp29.guard_value", "3")] {
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Bool, Error, Option}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.reflect.{{NodeOccurrence, occurrence_type, term_to_string}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Box
    sort T = ?
    entity box(item: T)
  end

  operation mk(b: Box) -> Option[T = (u: Int64) -> Bool @ {{Error[b.T] :- eq(b, b)}}] = none

  operation chk(x: NodeOccurrence) -> NodeOccurrence effects {{Error[String]}} =
    match occurrence_type(x)
      case some(t) -> Error.raise(term_to_string(t))
      case none() -> x

  operation trig[A](x: A) -> Int64 = 0
  rule trig(?x) <=> chk(?x) @[simp]

  operation go(x: Box[T = Buf[T = Int64, N = {n}]]) -> Int64 = trig(mk(x))
end
"#
        );
        assert_refused_naming(
            &load_errors(&src),
            &["Error[T = Buf[T = Int64, N = ", ":- eq(b, b)"],
            &format!("the printed type of `mk(x)` at N = {n}, guard and all"),
        );
    }
}

// ── a requirement written at a projection ─────────────────────────────────────────────

/// `pick`'s requirement is `Desc[T = x.E]`, and `x.E` is the element `outer` holds — the
/// provider at `N = {n}` answers 7, the one at `N = {other}` answers 9. `extra` is added
/// verbatim (another provider, a caller-side requirement).
fn requirement_program(ns: &str, n: &str, other: &str, outer_requires: &str, extra: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String}}

  sort Desc
    sort T = ?
    operation tag() -> Int64
  end

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Box
    sort E = ?
    entity box(v: E)
  end

  sort Here
    import anthill.prelude.Int64
    entity here
    provides Desc[T = Buf[T = Int64, N = {n}]]
    operation tag() -> Int64 = 7
  end

  sort There
    import anthill.prelude.Int64
    entity there
    provides Desc[T = Buf[T = Int64, N = {other}]]
    operation tag() -> Int64 = 9
  end
{extra}
  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()
  operation outer(b: Box[E = Buf[T = Int64, N = {n}]]) -> Int64{outer_requires} = pick(b)
  operation go() -> Int64 = outer(box(v: buf(v: 1)))
end
"#
    )
}

/// THE PROVIDER AT THE ELEMENT'S OWN VALUE answers, of two that differ only in `N`. The
/// requirement's spec is a `SortView(Desc)[T = …]`, whose `Desc` slot the rebuild keeps.
#[test]
fn a_requirement_at_a_projection_holding_a_value() {
    for (ns, n, other) in [
        ("wi0rp29.req_bool", "Bool", "String"),
        ("wi0rp29.req_value", "3", "4"),
    ] {
        assert_eq!(
            run_src(&requirement_program(ns, n, other, "", ""), &format!("{ns}.go")),
            Ok(7),
            "{ns}: the provider at N = {n}, not the one at N = {other}"
        );
    }
}

/// A CALLER'S REQUIREMENT AT ANOTHER BINDING IS NO COVER: `outer` holds `requires Desc[T =
/// Red]`, and `pick`'s demand at the `Buf` must not be served by it (Red answers 5) — a spec
/// that lost its binding would demand nothing and be covered by it.
#[test]
fn a_requirement_elsewhere_is_no_cover() {
    let red = "\n  sort Red\n    import anthill.prelude.Int64\n    entity red\n    \
               provides Desc[T = Red]\n    operation tag() -> Int64 = 5\n  end\n";
    let ns = "wi0rp29.req_red";
    assert_eq!(
        run_src(
            &requirement_program(ns, "3", "4", " requires Desc[T = Red]", red),
            &format!("{ns}.go")
        ),
        Ok(7)
    );
}

/// … and a requirement at a value NO provider covers is refused, naming it.
#[test]
fn a_requirement_no_provider_covers_is_refused() {
    let src = requirement_program("wi0rp29.req_none", "3", "4", "", "")
        .replace("provides Desc[T = Buf[T = Int64, N = 3]]", "provides Desc[T = Buf[T = Int64, N = 5]]");
    assert_refused_naming(
        &load_errors(&src),
        &["Desc[T = wi0rp29.req_none.Buf[T = anthill.prelude.Int64, N = 3]]"],
        "a requirement at N = 3 with providers at N = 5 and N = 4 only",
    );
}

// ── the WI-606 fallback ───────────────────────────────────────────────────────────────

/// A carrier whose `splitFirst` writes its return with projections on ITS OWN parameter
/// (`c.T`), and whose `E` is a row over its own `EC`. With `EC` left to an operation's
/// parameter `R`, `Stream.splitFirst`'s `s.E` does not ground (a non-ground row, WI-484), so
/// the call takes the fallback and threads THIS return — which carried `c.T` through as
/// written.
const CNT: &str = r#"
  sort Cnt
    sort T = ?
    effects EC = ?
    entity cnt(items: List[T])
    provides Stream[T = T, E = {EC}]
    operation splitFirst(c: Cnt) -> Option[Pair[A = c.T, B = Cnt[T = c.T]]] =
      match List.splitFirst(c.items)
        case none() -> none
        case some(pair(h, t)) -> some(pair(h, cnt(t)))
  end
"#;

/// `first` peels a `Cnt` of `Buf`s at `N = {elem}` through `Stream.splitFirst`.
fn cnt_first(elem: &str) -> String {
    format!(
        "{CNT}\n  operation first[R](x: Cnt[T = Buf[T = Int64, N = {elem}], EC = R]) -> Int64 \
         effects R =\n    \
         match Stream.splitFirst(x)\n      \
         case some(pair(b, _)) -> val(b)\n      \
         case none() -> 0\n"
    )
}

/// Refused on BOTH twins before ("expected Buf[T = Int64, N = Bool], got c.T").
#[test]
fn the_fallback_eliminates_the_overrides_projection() {
    runs_as_its_twin("wi0rp29.fallback", 7, |n| {
        format!(
            "{}  operation go() -> Int64 =\n    \
             let c: Cnt[T = Buf[T = Int64, N = {n}], EC = {{}}] = cnt(cons(buf(v: 7), nil))\n    \
             first(c)",
            cnt_first(n)
        )
    });
}

/// THE FALLBACK'S CONTROL: `c.T` grounds to the element the receiver holds — at `N = 4`,
/// handed to `val` at `N = 3`, it is refused naming both.
#[test]
fn a_wrong_value_through_the_fallback_is_refused() {
    assert_refused_naming(
        &load_errors(&program("wi0rp29.fallback_other", "3", &cnt_first("4"))),
        &["Buf[T = Int64, N = 3]", "Buf[T = Int64, N = 4]"],
        "an element at N = 4 through the fallback, where val takes N = 3",
    );
}

/// THE STDLIB'S OWN FALLBACK over a carrier written with its SORT PARAMETERS
/// (`MappedStream.splitFirst -> Option[Pair[A = T, …]]`), on a receiver whose `E` is left to
/// its slot: the override's `T` is tied to the receiver, whose own `T` is the caller's. Refused
/// "MappedStream has no member 'E'" when the fallback eliminated after σ had put the caller's
/// projection into the type.
#[test]
fn the_fallback_over_a_carrier_written_with_its_parameters() {
    let src = r#"
namespace wi0rp29.mapped
  import anthill.prelude.{Int64, List, Option, Pair, Stream, MappedStream}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  operation g[EP](s: Stream[T = Int64], f: (x: Int64) -> Int64 @ {EP}) -> Int64 effects {s.E, EP} =
    match Stream.splitFirst(MappedStream.map(s, f))
      case some(pair(h, _)) -> h
      case none() -> 0

  operation go() -> Int64 =
    let xs: List[T = Int64] = cons(3, nil)
    g(xs, lambda (x: Int64) -> x + 4)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.mapped.go"), Ok(7));
}

/// `Sp.pick(x: T, s: Sp)` — the receiver SECOND — reached through the fallback at `Car.pick(x:
/// Car, s: Car)`, whose FIRST parameter is typed by the carrier. `A = x.V` is the FIRST
/// argument's element, as the call binds it: `a` holds `first` (its element type and value),
/// `b` holds `second`.
fn positional_program(ns: &str, first: (&str, &str), second: (&str, &str)) -> String {
    let ((first, first_v), (second, second_v)) = (first, second);
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, String, List}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Sp
    sort T = ?
    effects E = ?
    operation pick(x: T, s: Sp) -> Option[T = Pair[A = s.T, B = Sp[T = s.T, E = s.E]]] effects s.E
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car, E = {{EC}}]
    operation pick(x: Car, s: Car) -> Option[T = Pair[A = x.V, B = Car[V = x.V, EC = EC]]] effects {{EC}} =
      some(pair(x.v, x))
  end

  operation use[R](a: Car[V = {first}, EC = R], b: Car[V = {second}, EC = R]) -> Int64 effects {{R}} =
    match Sp.pick(a, b)
      case some(pair(v, _)) -> v + 1
      case none() -> 0

  operation go() -> Int64 =
    let a: Car[V = {first}, EC = {{}}] = car(v: {first_v})
    let b: Car[V = {second}, EC = {{}}] = car(v: {second_v})
    use(a, b)
end
"#
    )
}

/// THE OVERRIDE'S PARAMETERS ARE KEYED BY POSITION: the first argument holds the `Int64`, and
/// the call runs. Keying the receiver's type to the first carrier-typed parameter as well took
/// `x.V` off the SECOND argument (`String`) and refused this program.
#[test]
fn the_fallback_keys_the_override_by_position() {
    let ns = "wi0rp29.positional";
    assert_eq!(
        run_src(
            &positional_program(ns, ("Int64", "41"), ("String", "\"str\"")),
            &format!("{ns}.go")
        ),
        Ok(42)
    );
}

/// … AND ITS CONTROL: the first argument holds the `String`, so `v + 1` is refused at load.
/// Keyed by the receiver, it LOADED and failed at run time adding 1 to a `String`.
#[test]
fn the_fallback_refuses_the_first_arguments_wrong_element() {
    let src = positional_program(
        "wi0rp29.positional_wrong",
        ("String", "\"str\""),
        ("Int64", "41"),
    );
    assert_refused_naming(
        &load_errors(&src),
        &["expected String, got Int64"],
        "`v` is the first argument's String",
    );
}

/// An override's `Modify[c]` names ITS OWN parameter; the call incurs it on the caller's
/// argument `x`. `first` declares `declared`.
///
/// A LOAD VERDICT: the question is which parameter the incurred `Modify` names, and it is
/// decided at load; a run would need a place for `x` to modify.
fn rekey_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List, Option, Pair, Stream, Modify}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Cnt
    sort T = ?
    effects EC = ?
    entity cnt(items: List[T])
    provides Stream[T = T, E = {{EC}}]
    operation splitFirst(c: Cnt) -> Option[Pair[A = T, B = Cnt[T = T, EC = {{Modify[c]}}]]] effects {{EC}} =
      match List.splitFirst(c.items)
        case none() -> none
        case some(pair(h, t)) -> some(pair(h, cnt(t)))
  end

  operation first[R](x: Cnt[T = Int64, EC = R]) -> Int64 effects {{{declared}}} =
    match Stream.splitFirst(x)
      case none() -> 0
      case some(pair(_, rest)) ->
        match Stream.splitFirst(rest)
          case some(pair(b, _)) -> b
          case none() -> 0
end
"#
    )
}

/// Declaring `Modify[x]` loads: the override's `c` is re-keyed to the caller's `x`. It was
/// refused "undeclared effect: Modify[T = c]" — the override's own parameter — wherever no
/// projection shared its type.
#[test]
fn an_overrides_own_parameter_is_rekeyed() {
    let errs = load_errors(&rekey_program("wi0rp29.rekey", "R, Modify[x]"));
    assert!(errs.is_empty(), "the caller declares the Modify it incurs: {errs:#?}");
}

/// … AND ITS CONTROL: without `Modify[x]` it is refused, naming `x`.
#[test]
fn an_overrides_own_parameter_is_rekeyed_control() {
    assert_refused_naming(
        &load_errors(&rekey_program("wi0rp29.rekey_short", "R")),
        &["undeclared effect", "Modify[T = x]"],
        "the incurred Modify names the caller's x",
    );
}
