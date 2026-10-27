//! WI-20260909-M8QWJ — AN OPERATION NOTHING CAN RUN IS REFUSED AT LOAD, at the site that
//! holds the information (kernel-language.md §5.4, *A body-less operation must have
//! something that can run it*).
//!
//! Every shape below loaded clean and failed only when it ran — `OperationBodyMissing` from
//! a body, and from a rule body a comparison decided as though the unreduced call were data.
//! Three checks, three sites:
//!
//!   * THE DECLARATION (`check_operations_have_a_definition`, kb/load.rs) — a body-less
//!     operation of a namespace or of a sort with constructors, with no body, no
//!     `@[host_implemented]` claim, no builtin, no `@[simp]` equation and no clause. Rows
//!     (a), (c), (d), (g) and the untagged-equation hint.
//!   * THE PROVISION (`provider_owes_operations`, kb/typing/coherence.rs) — a witness
//!     provision or a host-realized carrier that backs none of a spec's operations. Rows
//!     (e), its composite variant and the host carrier.
//!   * THE CALL (`unselectable_spec_operation_call`, kb/typing/call_class.rs) — a call of a
//!     body-less member of a sort that may be provided, in an operation body, when no
//!     provider can be selected and the sort's own operation runs nothing. Rows (b), (b)
//!     beside a provider, and (f).
//!
//! BACKED OUT, MEASURED (2026-10-17), one check at a time, every other row green each time:
//! the declaration check disabled reds the six declaration rows (and
//! `guardians_test::a_candidate_may_not_declare_its_own_trusted_producer`); the provision gate
//! restored to "constructors only" reds the four provision rows; the call check disabled reds
//! the six call rows. The three stdlib rows red with the stdlib's repairs reverted — measured
//! with all three checks disabled, since with them on the reverted stdlib's own load is
//! refused and nothing runs at all.
//!
//! PASS EITHER WAY, BY DESIGN — the controls, each a program that must keep loading AND
//! running: a host-mapped namespace operation, a self-receiver call a provider answers by
//! value, a no-carrier call a `requires` licenses, a forwarding provision, a witness that
//! does back its operation, a `@[simp]`-defined operation, a sort used as a module of bodied
//! operations, a default body entered under a `requires`, a bracket riding a type-value
//! receiver, and a requirement reached through another.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// No refusal at all: the row's control half.
#[track_caller]
fn assert_loads(src: &str, why: &str) {
    let errs = load_errors_of(src);
    assert!(errs.is_empty(), "{why}: expected a clean load, got {errs:#?}");
}

// ── the declaration ──────────────────────────────────────────────────────────────────

/// (a) A namespace-level operation with nothing behind it, CALLED: refused at the
/// declaration, naming the namespace. It used to load and die `OperationBodyMissing` at
/// the call.
#[test]
fn a_called_namespace_operation_with_no_definition_is_refused_at_its_declaration() {
    let errs = load_errors_of(
        "namespace m8a\n  import anthill.prelude.{Int64}\n  \
         operation ping() -> Int64\n  \
         operation drive() -> Int64 = ping()\nend\n",
    );
    assert_refused_naming(
        &errs,
        &[
            "operation `m8a.ping` has no definition",
            "declared in namespace `m8a`",
        ],
        "a namespace operation nothing defines",
    );
}

/// (c) The same declaration with no caller is refused too: the answer is one for every use,
/// and a declaration nothing uses yet is one of them.
#[test]
fn an_uncalled_namespace_operation_with_no_definition_is_refused() {
    let errs = load_errors_of(
        "namespace m8c\n  import anthill.prelude.{Int64}\n  operation ping() -> Int64\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["operation `m8c.ping` has no definition"],
        "an uncalled namespace operation nothing defines",
    );
}

/// (d) A member of a sort with constructors: nothing provides a data sort (§5.1), so its
/// operation is its own, and with nothing behind it nothing ever runs it.
#[test]
fn a_member_of_a_sort_with_constructors_with_no_definition_is_refused() {
    let errs = load_errors_of(
        "namespace m8d\n  import anthill.prelude.{Int64}\n  \
         sort H\n    entity h(n: Int64)\n    operation ping(x: H) -> Int64\n  end\n  \
         operation drive() -> Int64 = h(n: 1).ping()\nend\n",
    );
    assert_refused_naming(
        &errs,
        &[
            "operation `m8d.H.ping` has no definition",
            "a sort with constructors",
        ],
        "a data sort's operation nothing defines",
    );
}

/// (g) THE RULE-BODY FACE. `undef(1) = 1` answered `no solutions` — DECIDED false over a
/// call that never ran, so `not(undef(1) = 1)` answered 1 DEFINITE — and through a body it
/// delayed with no warning. The declaration is refused, so neither can be asked.
#[test]
fn a_rule_body_comparison_over_such_an_operation_is_refused_with_its_declaration() {
    let errs = load_errors_of(
        "namespace m8g\n  import anthill.prelude.{Int64}\n  \
         operation undef(n: Int64) -> Int64\n  \
         operation wrap(n: Int64) -> Int64 = undef(n)\n  \
         rule r(1) :- undef(1) = 1\n  \
         rule rn(1) :- not(undef(1) = 1)\n  \
         rule w(1) :- wrap(1) = 1\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["operation `m8g.undef` has no definition"],
        "the rule-body face",
    );
}

/// A top-level operation, in no namespace, is told so rather than named after the global
/// scope.
#[test]
fn a_top_level_operation_is_refused_naming_no_namespace() {
    let errs = load_errors_of("operation m8solo() -> anthill.prelude.Int64\n");
    assert_refused_naming(
        &errs,
        &["operation `m8solo` has no definition", "declared at the top level"],
        "a top-level operation nothing defines",
    );
    assert!(!errs.join(" ").contains("<global>"), "{errs:?}");
}

/// An UNTAGGED equation is inert (§5.3): the refusal names it as the likely definition and
/// the tag that would make it one. CONTROL: tagged, the same equation defines the operation
/// and the call runs.
#[test]
fn an_untagged_equation_is_named_and_a_tagged_one_defines_the_operation() {
    let errs = load_errors_of(
        "namespace m8eq\n  import anthill.prelude.{Int64}\n  \
         operation twice(x: Int64) -> Int64\n  \
         rule twice(?x) <=> ?x + ?x\nend\n",
    );
    assert_refused_naming(
        &errs,
        &[
            "operation `m8eq.twice` has no definition",
            "1 equation with `m8eq.twice` as its subject carries no `@[simp]` tag",
        ],
        "an operation defined only by an untagged equation",
    );
    assert_eq!(
        run_int64(
            "namespace m8eqok\n  import anthill.prelude.{Int64}\n  \
             operation twice(x: Int64) -> Int64\n  \
             rule twice(?x) <=> ?x + ?x @[simp]\n  \
             operation drive() -> Int64 = twice(21)\nend\n",
            "m8eqok.drive",
        ),
        Ok(42),
    );
}

/// CONTROL: a body-less namespace operation a binding block maps is defined, and runs.
#[test]
fn a_host_mapped_namespace_operation_loads_and_runs() {
    assert_eq!(
        run_int64(
            "namespace m8host\n  import anthill.prelude.{Int64}\n  \
             operation myadd(a: Int64, b: Int64) -> Int64 @[host_implemented]\n  \
             operation drive() -> Int64 = myadd(40, 2)\n  \
             provides m8host language rust\n    \
             operation_map { myadd: \"int_add\" }\n  end\nend\n",
            "m8host.drive",
        ),
        Ok(42),
    );
}

// ── the call ─────────────────────────────────────────────────────────────────────────

const MYSPEC: &str = "  sort MySpec\n    sort T = ?\n    operation ping() -> Int64\n  end\n";

/// (b) A body-less member of a sort that may be provided, called with no carrier and no
/// `requires`: nothing can select a provider, so the call reaches `MySpec.ping` itself. With
/// nothing providing `MySpec` the refusal says so, and no bracket is advised.
#[test]
fn a_spec_call_no_provider_can_be_selected_for_is_refused_at_the_call() {
    let errs = load_errors_of(&format!(
        "namespace m8b\n  import anthill.prelude.{{Int64}}\n{MYSPEC}  \
         operation drive() -> Int64 = MySpec.ping()\nend\n"
    ));
    assert_refused_naming(
        &errs,
        &[
            "a call of `m8b.MySpec.ping` that nothing can run",
            "nothing provides `m8b.MySpec`",
        ],
        "an unselectable spec call",
    );
}

/// (b) BESIDE A PROVIDER that implements the operation: still nothing selects it — MEASURED,
/// this program loaded and died `OperationBodyMissing` — so still refused. CONTROL: under a
/// `requires` the same call is licensed, and its caller's dictionary answers the provider's
/// value (WI-325's licence, the case the call check must not touch).
#[test]
fn a_provider_does_not_make_the_call_selectable_and_a_requires_does() {
    let provider = "  sort W\n    provides MySpec[T = Int64]\n    \
                    operation ping() -> Int64 = 42\n  end\n";
    let errs = load_errors_of(&format!(
        "namespace m8bw\n  import anthill.prelude.{{Int64}}\n{MYSPEC}{provider}  \
         operation drive() -> Int64 = MySpec.ping()\nend\n"
    ));
    assert_refused_naming(
        &errs,
        &["a call of `m8bw.MySpec.ping` that nothing can run"],
        "an unselectable spec call beside a provider",
    );
    assert_eq!(
        run_int64(
            &format!(
                "namespace m8br\n  import anthill.prelude.{{Int64}}\n{MYSPEC}{provider}  \
                 operation g[A](x: A) -> Int64 requires MySpec[T = A] = MySpec.ping[T = A]()\n  \
                 operation drive() -> Int64 = g(1)\nend\n"
            ),
            "m8br.drive",
        ),
        Ok(42),
    );
}

/// (f) The clause-defined twin: a parametric sort's operation defined by clauses alone,
/// called with no carrier. `clause_defined_own_operation` (WI-20261003-4DYR6) leaves it to
/// the dispatch because the parameter could name a provider through a requirement — and with
/// none in scope the call is refused here, naming the clauses.
#[test]
fn a_clause_defined_member_of_a_parametric_sort_called_with_no_carrier_is_refused() {
    let errs = load_errors_of(
        "namespace m8f\n  import anthill.prelude.{Int64}\n  \
         sort Util\n    sort T = ?\n    operation open(b: Int64) -> Int64\n    \
         rule open(?v, ?v) :- true\n  end\n  \
         operation drive() -> Int64 = Util.open(42)\nend\n",
    );
    assert_refused_naming(
        &errs,
        &[
            "a call of `m8f.Util.open` that nothing can run",
            "defined by clauses alone",
        ],
        "a clause-defined call with no carrier",
    );
}

/// CONTROL: a call that brings its carrier — a self-receiver — is answered by value. The
/// higher-kinded twin (`Monad.map` over a `Result`'s `M[A]`, a carrier no first-order reader
/// sees) is `wi_9wvt7_error_reify_test::the_reified_result_is_a_monad`'s, which the call
/// check refused before it asked that the signature be ground.
#[test]
fn a_call_that_brings_its_carrier_loads_and_runs() {
    assert_eq!(
        run_int64(
            "namespace m8recv\n  import anthill.prelude.{Int64}\n  \
             sort Sp\n    operation size(s: Sp) -> Int64\n  end\n  \
             sort Car\n    entity car(n: Int64)\n    provides Sp\n    \
             operation size(c: Car) -> Int64 = 42\n  end\n  \
             operation drive() -> Int64 = Sp.size(car(n: 1))\nend\n",
            "m8recv.drive",
        ),
        Ok(42),
    );
}

/// A `@[simp]` equation the build frame did NOT fire is no definition at the call: the
/// rewrite is tried before the call is typed, so a call that reaches the check is one no
/// equation rewrote. Here the sort's parameter and its provider block the rewrite.
/// (Found by review: this loaded and died at eval.)
#[test]
fn an_equation_that_did_not_fire_does_not_license_the_call() {
    let errs = load_errors_of(
        "namespace m8simp\n  import anthill.prelude.{Int64}\n  \
         sort MySpec\n    sort T = ?\n    operation ping() -> Int64\n    \
         rule ping() <=> 3 @[simp]\n  end\n  \
         sort W\n    provides MySpec[T = W]\n    operation ping() -> Int64 = 4\n  end\n  \
         operation drive() -> Int64 = MySpec.ping()\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["a call of `m8simp.MySpec.ping` that nothing can run"],
        "a spec call no equation rewrote",
    );
}

/// The BARE spelling of a nullary member — its zero-arg-call reading — is the same call.
/// (Found by review: `import MySpec.{ping}` and a bare `ping` loaded and died at eval.)
#[test]
fn the_bare_spelling_of_a_nullary_spec_call_is_refused_too() {
    let errs = load_errors_of(&format!(
        "namespace m8bare\n  import anthill.prelude.{{Int64}}\n  \
         import m8bare.MySpec.{{ping}}\n{MYSPEC}  operation drive() -> Int64 = ping\nend\n"
    ));
    assert_refused_naming(
        &errs,
        &["a call of `m8bare.MySpec.ping` that nothing can run"],
        "a bare nullary spec call",
    );
}

/// A DEFAULT BODY run at the sort itself dispatches its sibling calls to the sort's own
/// members: an unselected call of `other` reaches `helper`, which runs nothing, and is
/// refused naming it. (Found by review: loaded, died at eval.) CONTROLS: a sort used as a
/// module of bodied operations calling each other runs; and the same default body entered
/// under a `requires` — at a provider's instance — answers the provider's member.
#[test]
fn a_default_body_reaching_a_member_that_runs_nothing_is_refused_at_its_call() {
    let errs = load_errors_of(
        "namespace m8sib\n  import anthill.prelude.{Int64}\n  \
         sort Util\n    operation helper(x: Int64) -> Int64\n    \
         operation other(x: Int64) -> Int64 = helper(x)\n  end\n  \
         operation drive() -> Int64 = Util.other(1)\nend\n",
    );
    assert_refused_naming(
        &errs,
        &[
            "a call of `m8sib.Util.other` that nothing can run",
            "its body calls `m8sib.Util.helper` at that same sort",
            "give `helper` a body",
        ],
        "an unselected call reaching an unrunnable sibling",
    );
    assert_eq!(
        run_int64(
            "namespace m8mod\n  import anthill.prelude.{Int64}\n  \
             sort Util\n    operation version() -> Int64 = 3\n    \
             operation twice() -> Int64 = version() * 2\n  end\n  \
             operation drive() -> Int64 = Util.twice()\nend\n",
            "m8mod.drive",
        ),
        Ok(6),
    );
    assert_eq!(
        run_int64(
            "namespace m8sibreq\n  import anthill.prelude.{Int64}\n  \
             sort Sp\n    sort T = ?\n    operation name() -> Int64\n    \
             operation greet() -> Int64 = name() + 1\n  end\n  \
             sort W\n    provides Sp[T = Int64]\n    operation name() -> Int64 = 41\n  end\n  \
             operation g[A](x: A) -> Int64 requires Sp[T = A] = Sp.greet[T = A]()\n  \
             operation drive() -> Int64 = g(1)\nend\n",
            "m8sibreq.drive",
        ),
        Ok(42),
    );
}

/// CONTROLS for two selections the call check must read: a BRACKET riding the receiver of a
/// dot on a type value (`Desc[T = Leaf].label()`), and a requirement reached THROUGH another
/// one (`User requires Mid`, `Mid requires Deep`). Both were refused by the first cut of the
/// check (found migrating `wi_papx0` and `wi_6bx85`).
#[test]
fn a_receiver_bracket_and_a_transitive_requirement_select() {
    assert_eq!(
        run_int64(
            "namespace m8papx\n  import anthill.prelude.{Int64}\n  \
             sort Desc\n    sort T = ?\n    operation label() -> Int64\n  end\n  \
             sort Leaf\n    entity leaf\n    provides Desc[T = Leaf]\n    \
             operation label() -> Int64 = 7\n  end\n  \
             operation drive() -> Int64 = Desc[T = Leaf].label()\nend\n",
            "m8papx.drive",
        ),
        Ok(7),
    );
    assert_loads(
        "namespace m8deep\n  import anthill.prelude.{Int64}\n  \
         sort Deep\n    operation deep_op(x: Int64) -> Int64\n  end\n  \
         sort Mid\n    requires m8deep.Deep\n    operation mid_op(x: Int64) -> Int64\n  end\n  \
         sort User\n    requires m8deep.Mid\n    \
         operation use_both(y: Int64) -> Int64 = Deep.deep_op(Mid.mid_op(y))\n  end\nend\n",
        "a requirement reached through another",
    );
}

// ── the provision ────────────────────────────────────────────────────────────────────

const LO: &str = "  sort Lo\n    sort T = ?\n    operation lo(x: T) -> Int64\n  end\n";

/// (e) A WITNESS provision that backs nothing: `Hi` is the provider of `Lo` at `Int64`, so
/// `Lo.lo(1)` dispatches to `Hi`, which has no `lo`. CONTROL: the witness that does carry
/// `lo` answers.
#[test]
fn a_witness_provision_that_backs_nothing_is_refused() {
    let errs = load_errors_of(&format!(
        "namespace m8e\n  import anthill.prelude.{{Int64}}\n{LO}  \
         sort Hi\n    provides Lo[T = Int64]\n  end\n  \
         operation drive() -> Int64 = Lo.lo(1)\nend\n"
    ));
    assert_refused_naming(
        &errs,
        &["'m8e.Hi' provides 'm8e.Lo' but backs no operation 'm8e.Lo.lo'"],
        "a witness with no member",
    );
    assert_eq!(
        run_int64(
            &format!(
                "namespace m8eok\n  import anthill.prelude.{{Int64}}\n{LO}  \
                 sort Hi\n    provides Lo[T = Int64]\n    \
                 operation lo(x: Int64) -> Int64 = 9\n  end\n  \
                 operation drive() -> Int64 = Lo.lo(1)\nend\n"
            ),
            "m8eok.drive",
        ),
        Ok(9),
    );
}

/// (e) AT A COMPOSITE OF THE PROVIDER'S OWN PARAMETER, which is no forwarding: `Hi` is the
/// provider at `Box[…]`, and a `C` providing `Hi` with a `lo` over `Box[T = C]` is not
/// reached — MEASURED, `Lo.lo(box(…))` died at eval. CONTROL: the FORWARDING provision
/// (`Lo[T = T]`) is a sub-interface, and the carrier behind it answers.
#[test]
fn a_composite_witness_is_refused_and_a_forwarding_sub_interface_is_not() {
    let errs = load_errors_of(&format!(
        "namespace m8ec\n  import anthill.prelude.{{Int64}}\n{LO}  \
         sort Box\n    sort T = ?\n    entity box(v: T)\n  end\n  \
         sort Hi\n    sort T = ?\n    provides Lo[T = Box[T = T]]\n  end\nend\n"
    ));
    assert_refused_naming(
        &errs,
        &["'m8ec.Hi' provides 'm8ec.Lo' but backs no operation 'm8ec.Lo.lo'"],
        "a witness at a composite of the provider's parameter",
    );
    assert_eq!(
        run_int64(
            &format!(
                "namespace m8ef\n  import anthill.prelude.{{Int64}}\n{LO}  \
                 sort Hi\n    sort T = ?\n    provides Lo[T = T]\n  end\n  \
                 sort C\n    entity c(n: Int64)\n    provides Hi[T = C]\n    \
                 operation lo(x: C) -> Int64 = 5\n  end\n  \
                 operation drive() -> Int64 = Lo.lo(c(n: 1))\nend\n"
            ),
            "m8ef.drive",
        ),
        Ok(5),
    );
}

/// A spec whose operations name NONE of its parameters has no carrier parameter, and is
/// read at every binding: `Hi` names `Int64` at `T`, so it is the dictionary a `requires
/// MySpec[T = A]` hands over at `Int64`, and owes `ping`. (Found by review: this loaded and
/// `g(1)` died at eval.)
#[test]
fn a_witness_of_a_spec_naming_no_parameter_is_refused() {
    let errs = load_errors_of(&format!(
        "namespace m8wc\n  import anthill.prelude.{{Int64}}\n{MYSPEC}  \
         sort Hi\n    provides MySpec[T = Int64]\n  end\n  \
         operation g[A](x: A) -> Int64 requires MySpec[T = A] = MySpec.ping[T = A]()\n  \
         operation drive() -> Int64 = g(1)\nend\n"
    ));
    assert_refused_naming(
        &errs,
        &["'m8wc.Hi' provides 'm8wc.MySpec' but backs no operation 'm8wc.MySpec.ping'"],
        "a witness of a carrier-less spec",
    );
}

/// A HOST-REALIZED carrier providing a spec at itself owes its operations as one with
/// constructors does: `Int64` has no constructor and its values are real.
#[test]
fn a_host_carrier_that_backs_nothing_is_refused() {
    let errs = load_errors_of(
        "namespace m8hc\n  import anthill.prelude.{Int64}\n  \
         sort Tick\n    sort T = ?\n    operation tick(x: T) -> Int64\n  end\nend\n\
         namespace anthill.prelude.Int64\n  import m8hc.Tick\n  \
         provides Tick[T = Int64]\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["'anthill.prelude.Int64' provides 'm8hc.Tick' but backs no operation 'm8hc.Tick.tick'"],
        "a host carrier with no member",
    );
}

// ── the standard library, repaired so that it loads under the provision check ──────────

/// `Pair.fst`/`snd` were defined by untagged equations alone, so a call died at eval.
#[test]
fn pair_projections_run() {
    assert_eq!(
        run_int64(
            "namespace m8pair\n  import anthill.prelude.{Int64, Pair}\n  \
             operation drive() -> Int64 = Pair.snd(Pair.pair(fst: 1, snd: 42))\nend\n",
            "m8pair.drive",
        ),
        Ok(42),
    );
}

/// `Int64`, `BigInt` and `Float` provided `Additive` and `Multiplicative` with no `zero` and
/// no `one`: a generic body reaching them through a requirement died at eval.
#[test]
fn the_numeric_identities_are_reached_through_a_requirement() {
    let src = "namespace m8id\n  import anthill.prelude.{Int64, Additive, Multiplicative}\n  \
               operation z[A](x: A) -> A requires Additive[T = A] = Additive.zero()\n  \
               operation o[A](x: A) -> A requires Multiplicative[T = A] = Multiplicative.one()\n  \
               operation drive() -> Int64 = z(5) * 10 + o(5)\nend\n";
    assert_eq!(run_int64(src, "m8id.drive"), Ok(1));
}

/// `Float.recip` was a `@[simp]` equation, which no dispatch through `Field` can run; and
/// `Float.nonEqRefl` an untagged one, inert.
#[test]
fn float_recip_and_non_eq_witness_are_reached_through_a_requirement() {
    let src = "namespace m8fl\n  \
               import anthill.prelude.{Int64, Float, Field, NonEq, Error, DivisionByZero}\n  \
               operation r[A](x: A) -> A effects {Error[T = DivisionByZero]} \
               requires Field[T = A] = Field.recip(x)\n  \
               operation w[A](x: A) -> A requires NonEq[T = A] = NonEq.nonEqRefl()\n  \
               operation drive() -> Int64 effects {Error[T = DivisionByZero]} =\n    \
               Float.floor(Float.mul(r(4.0), 100.0)) + (if Float.isNaN(w(1.0)) then 1 else 0)\n\
               end\n";
    assert_eq!(run_int64(src, "m8fl.drive"), Ok(26));
}
