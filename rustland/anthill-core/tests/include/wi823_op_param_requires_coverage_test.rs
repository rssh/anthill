//! WI-823 — an op-scoped `requires` over the operation's OWN bracket type
//! parameter (proposal 042; kernel spec §5.4) licenses the abstract spec-op calls
//! in that operation's body, exactly as the same clause over a SORT parameter does.
//!
//! THE GAP THIS FILE CLOSES IS NOT A FIX, IT IS THE MISSING DEFENCE. WI-823 was
//! filed against a load rejection and named two suspected mechanisms; the actual
//! fix arrived under WI-943, which gave a bracket parameter a canonical variable of
//! its own (`record_type_param_var` at the op-bracket site in `load.rs`) so that a
//! WRITTEN `PT` resolves to the variable its operation declares instead of to an
//! unrelated same-named sort's. `op_requires_covers` compares those two variables,
//! so before that publication existed no clause could cover anything.
//!
//! What WI-943 left behind is a licence defended by two fixtures
//! (`wi817_polyrec_requirement_test`'s two `(b)` pins) that share one shape:
//! ONE bracket parameter, an EXPLICIT type argument at the call site, and no
//! negative control anywhere. Every test in this file was measured against the
//! back-out described below; the shapes are the ones that fixture pair does not
//! reach.
//!
//! THE BACK-OUT, for every "fails on back-out" claim below. In
//! `kb/load.rs`'s operation-conversion loop (the `for tp in &o.type_params`
//! pre-allocation), drop the publication:
//!
//! ```ignore
//! if let (Some(declared), Some(vid)) = (declared, vid) {
//!     self.kb.record_type_param_var(declared, vid);   // <- remove this line
//! }
//! ```
//!
//! That is the WI-943 channel in its post-WI-954 form (WI-954 folded the two
//! publication channels into one map, so the `SortAlias` half is untouched by it
//! and the sort-parameter spelling stays green throughout — which is what makes
//! this a back-out of the op-param fix specifically, not of type parameters).
//! RUN, not predicted: with that line removed every positive assertion below fails
//! at LOAD, and the two refusals stay refused.
use anthill_core::eval::Value;

/// Spec `Desc` + base instance at `Leaf` (describe → 1) + CONDITIONAL instance at
/// `Wrap[E]` given `Desc[E]` (describe → 10·describe(inner) + 2). Values are
/// therefore depth-coded — 1, 12, 122 — so a licence granted to the WRONG
/// dictionary produces a detectably different number rather than passing as "some
/// Int". Shared with the WI-817 / WI-822 / WI-855 files.
const INSTANCES: &str = crate::common::DESC_INSTANCES;

fn with_instances(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Function}}
{INSTANCES}
{body}
end
"#
    )
}

/// Load and call `entry(0)` on a FRESH interpreter. `interp_for` prints every load
/// error and panics on a dirty load, so the "loads clean" half of each pin needs no
/// separate load call; fresh per program because a trapped call poisons later calls
/// on one interpreter.
fn eval_fresh(src: &str, entry: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

fn assert_int(src: &str, entry: &str, want: i64, why: &str) {
    let got = eval_fresh(src, entry);
    assert!(
        matches!(got, Ok(Value::Int(v)) if v == want),
        "{entry}: expected the depth-coded Ok(Int({want})) — {why}; got {got:?}"
    );
}

/// The WI-325 ladder's refusal for this spec — what an UNCOVERED abstract spec-op
/// call is answered with, and what every positive test here reverts to on back-out.
const MISSING_REQUIRES: &str = crate::common::MISSING_DESC_REQUIRES;

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but the source loaded clean"))
}

/// Assert the refusal is the WI-325 ladder AT THE EXPECTED SITE, not merely
/// somewhere in the program. The text alone is not enough here: the shared
/// `DESC_INSTANCES` block contains its own abstract `Desc.describe(w.inner)` call
/// (in `WrapDesc.describe`, licensed by a SORT-level `requires`), so a regression
/// in that unrelated licence would raise the same wording and keep both refusal
/// tests below green while witnessing nothing about op-param keying.
fn assert_refused_at(errs: &[String], site: &str) {
    assert!(
        errs.iter()
            .any(|e| e.contains(site) && e.contains(MISSING_REQUIRES)),
        "expected the WI-325 ladder at `{site}`; got {errs:?}"
    );
}

// ── The licence's breadth ────────────────────────────────────────────────

/// THE CALL SITE'S TYPE ARGUMENT IS NOT WHERE THE IDENTITY COMES FROM. Both
/// `(b)` pins in the WI-817 file write the type argument explicitly
/// (`probe[Leaf](leaf())`), which leaves open whether the licence rides that
/// bracket. It does not: the clause is checked against the operation's own
/// declared parameter when the body is typed, before any call site is consulted,
/// so an INFERRED call is covered identically. Driven on both providers so the
/// answer distinguishes which dictionary was reached — the base describer (1) and
/// the CONDITIONAL one (12), whose own `requires Desc[T = E]` must resolve on top
/// of the licence.
///
/// Fails on back-out: all four, at load, with the WI-325 ladder.
#[test]
fn an_op_param_call_is_covered_with_and_without_an_explicit_type_argument() {
    for (label, call, want) in [
        ("explicit, base", "probe[Leaf](leaf())", 1),
        ("inferred, base", "probe(leaf())", 1),
        (
            "explicit, conditional",
            "probe[Wrap[A = Leaf]](wrap(leaf()))",
            12,
        ),
        ("inferred, conditional", "probe(wrap(leaf()))", 12),
    ] {
        let src = with_instances(
            "wi823.infer",
            &format!(
                "  sort Holder\n    operation probe[PT](x: PT) -> Int64 requires Desc[PT] = Desc.describe(x)\n    operation drive(n: Int64) -> Int64 = {call}\n  end"
            ),
        );
        assert_int(
            &src,
            "wi823.infer.Holder.drive",
            want,
            &format!(
                "({label}) the operation's own `requires Desc[PT]` licenses its own \
                      describe call, and the type argument's presence at the call site is \
                      not what supplies the parameter's identity"
            ),
        );
    }
}

/// TWO BRACKET PARAMETERS ARE TWO PARAMETERS. This is the shape WI-943 named as
/// the one the old short-name reader collapsed: `pair[A, B]` answered with two
/// unrelated sorts' variables. Each clause must cover its own parameter's call and
/// only that one. The two arguments are given DIFFERENT depth codes (1 and 12) and
/// combined positionally (100·first + second = 112), so a licence that crossed the
/// two dictionaries — or granted one clause to both calls — lands on 1212, 112's
/// digits in the wrong slots, or a dispatch failure, never on 112 by accident.
///
/// Fails on back-out: at load, with TWO WI-325 ladder errors, one per call.
#[test]
fn two_op_params_take_their_own_clauses() {
    let src = with_instances(
        "wi823.two",
        r#"  sort Holder
    operation pair[A, B](x: A, y: B) -> Int64 requires Desc[A], Desc[B] =
      add(mul(100, Desc.describe(x)), Desc.describe(y))
    operation drive(n: Int64) -> Int64 = pair[Leaf, Wrap[A = Leaf]](leaf(), wrap(leaf()))
  end"#,
    );
    assert_int(
        &src,
        "wi823.two.Holder.drive",
        112,
        "each of `pair`'s two clauses covers its own parameter's call: 100·1 (Leaf) + 12 (Wrap)",
    );
}

/// THE LICENCE IS KEYED ON WHICH PARAMETER THE CLAUSE NAMES — the pair that says
/// the coverage check discriminates rather than merely permitting. One program
/// shape, two spellings: the clause over the parameter the call actually carries
/// LOADS and reaches the right describer; the clause over the operation's OTHER
/// parameter is REFUSED, because `QT` does not cover a call on `PT`.
///
/// Measured asymmetry, and it is the point of pairing them: the POSITIVE half
/// fails on back-out (it reverts to the same refusal), the REFUSAL half is refused
/// either way BY DESIGN — pre-fix because no parameter had an identity at all,
/// post-fix because the two identities differ. The refusal alone would therefore
/// measure nothing; it earns its place as the neighbour that stops the positive
/// half from being satisfied by a blanket licence.
#[test]
fn the_clause_is_keyed_on_the_param_it_names() {
    let covering = with_instances(
        "wi823.right",
        r#"  sort Holder
    operation probe[PT, QT](x: PT, y: QT) -> Int64 requires Desc[PT] = Desc.describe(x)
    operation drive(n: Int64) -> Int64 = probe[Leaf, Leaf](leaf(), leaf())
  end"#,
    );
    assert_int(
        &covering,
        "wi823.right.Holder.drive",
        1,
        "`requires Desc[PT]` covers the call on `PT`",
    );

    let other_param = with_instances(
        "wi823.wrong",
        r#"  sort Holder
    operation probe[PT, QT](x: PT, y: QT) -> Int64 requires Desc[QT] = Desc.describe(x)
    operation drive(n: Int64) -> Int64 = probe[Leaf, Leaf](leaf(), leaf())
  end"#,
    );
    // `requires Desc[QT]` must NOT cover a call on `PT` — the two are different
    // parameters, and covering here would reintroduce the pre-WI-943 collapse in
    // which both names answered with one variable.
    assert_refused_at(
        &load_errs(&other_param),
        "wi823.wrong.Desc.describe.requires",
    );
}

/// AN OPERATION'S CLAUSE COMPOSES WITH ITS SORT'S, it does not replace it. The
/// body makes TWO abstract calls — one on the sort parameter `HT`, licensed by the
/// sort-level `requires`, one on the bracket parameter `PT`, licensed by the
/// operation's own — and both must be covered from the same body.
///
/// THE TWO ARGUMENTS CARRY DIFFERENT DEPTH CODES ON PURPOSE, and an earlier draft
/// of this test got that wrong in a way worth recording: it passed `leaf()` for
/// BOTH, so both calls coded 1 and the expected 100·1 + 1 = 101 was produced just
/// as well by a body that served the `HT` call from the op clause and the `PT`
/// call from the sort clause. The value measured nothing; only the load did.
/// `Leaf` (1) against `Wrap[A = Leaf]` (12) makes the slots tell apart: correct is
/// 112, and the crossing lands on 100·12 + 1 = 1201.
///
/// Fails on back-out: at load, with the WI-325 ladder — the sort half survives
/// (the `SortAlias` channel is untouched), the op half does not, which is what
/// makes this a composition test and not a second copy of the first one.
#[test]
fn an_op_param_clause_composes_with_its_sorts_own() {
    let src = with_instances(
        "wi823.compose",
        r#"  sort Holder
    sort HT = ?
    requires Desc[T = HT]
    operation probe[PT](x: PT, y: HT) -> Int64 requires Desc[PT] =
      add(mul(100, Desc.describe(x)), Desc.describe(y))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe[Leaf](leaf(), wrap(leaf()))
  end"#,
    );
    assert_int(
        &src,
        "wi823.compose.Driver.drive",
        112,
        "the operation's own clause covers the `PT` call and the sort-level one covers \
         the `HT` call, from one body: 100·1 (Leaf, via the op clause) + 12 (Wrap, via \
         the sort clause) — a crossed pair of licences would give 1201",
    );
}

/// THE REQUIREMENT RIDES A HOP BETWEEN TWO OP-PARAM OPERATIONS. `outer[OT]` does
/// not call the spec itself — it calls `inner[OT]`, whose own clause is what the
/// abstract call needs; the instantiation must reach `inner` as `OT`'s binding at
/// the call, not as `outer`'s abstract parameter. Driven through the CONDITIONAL
/// provider (12) so the relayed instantiation is one whose dictionary has to be
/// resolved rather than looked up directly.
///
/// Fails on back-out: at load, with the WI-325 ladder.
#[test]
fn an_op_param_requirement_rides_a_relay_hop() {
    let src = with_instances(
        "wi823.relay",
        r#"  sort Holder
    operation inner[IT](x: IT) -> Int64 requires Desc[IT] = Desc.describe(x)
    operation outer[OT](x: OT) -> Int64 requires Desc[OT] = inner[OT](x)
    operation drive(n: Int64) -> Int64 = outer[Wrap[A = Leaf]](wrap(leaf()))
  end"#,
    );
    assert_int(
        &src,
        "wi823.relay.Holder.drive",
        12,
        "`outer`'s clause carries the instantiation across the hop into `inner`'s own",
    );
}

/// THE CLAUSE'S ELEMENT NEED NOT BE THE BARE PARAMETER. `requires Desc[T = Wrap[A
/// = PT]]` covers a call whose carrier is the STRUCTURED `Wrap[A = PT]`, so the
/// coverage check is a comparison of elements and not a test for "the clause names
/// this variable".
///
/// Fails on back-out, and with a DIFFERENT error from every other test here — the
/// dispatch ladder (`Desc.describe.dispatch: no impl matches — unresolved:
/// Desc[T = <term#…>]`) rather than the WI-325 requires ladder, because an
/// unidentified `PT` leaves the structured element itself unresolved before the
/// requires question is reached. Recorded because it is the one row where "fails
/// on back-out" does not mean "reverts to `MISSING_REQUIRES`".
#[test]
fn a_structured_op_param_element_covers_its_call() {
    let src = with_instances(
        "wi823.structured",
        r#"  sort Holder
    operation probe[PT](x: Wrap[A = PT]) -> Int64 requires Desc[T = Wrap[A = PT]] =
      Desc.describe(x)
    operation drive(n: Int64) -> Int64 = probe[Leaf](wrap(leaf()))
  end"#,
    );
    assert_int(
        &src,
        "wi823.structured.Holder.drive",
        12,
        "the structured element `Wrap[A = PT]` covers the call on that same carrier",
    );
}

/// THE LICENCE IS NOT BLANKET. The same program with the `requires` clause simply
/// DELETED must still be refused — the operation's parameter is abstract and
/// nothing licenses the spec-op call on it.
///
/// Refused both with and without the back-out, BY DESIGN, and said here rather
/// than left for a reader to discover: this measures nothing about WI-943 and is
/// not meant to. It is the guard on the direction WI-943 widened — the publication
/// it added is what makes a written parameter resolvable at all, and a coverage
/// check that answered from the parameter's mere existence rather than from a
/// written clause would take every test above with it and leave this one as the
/// only witness.
#[test]
fn an_op_param_call_with_no_clause_is_still_refused() {
    let src = with_instances(
        "wi823.none",
        r#"  sort Holder
    operation probe[PT](x: PT) -> Int64 = Desc.describe(x)
    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())
  end"#,
    );
    // An abstract spec-op call under NO clause must stay refused, and at `probe`'s
    // own call — not merely somewhere in the program.
    assert_refused_at(&load_errs(&src), "wi823.none.Desc.describe.requires");
}
