//! WI-943 — A TYPE PARAMETER HAS ONE CANONICAL VARIABLE, AND EVERY READER GETS IT.
//!
//! Two worlds ask "which logical variable is this type parameter?" and they must
//! answer the same thing:
//!
//!  * THE DECLARATION — what the loader minted. For an OPERATION parameter that is
//!    `OperationInfo.type_params` (`load_operation`'s `fresh_var`), which
//!    `rigidify_op_type_params` skolemizes and `check_unconstrained_type_params`
//!    reads. For a SORT parameter it is the `SortAlias` target.
//!  * THE SYMBOL — what a WRITTEN occurrence of the parameter resolves through:
//!    `typing::type_param_global_var`, and so `sigma_class` (via `elem_var_step`)
//!    when it reads the `Ref(T)` inside a `requires`, and `declared_type_param_vid` /
//!    `type_param_vid_in_sort` when they ground a carrier.
//!
//! WI-942 MEASURED them disagreeing for an operation parameter and bridged both
//! identities onto the body's rigid. WI-943 root-caused the disagreement, and it was
//! not two identities: the symbol side had NO operation channel at all. The loader
//! asserts no `SortAlias` for an op parameter (deliberately — an op parameter is its
//! own variable), so `resolve_sort_alias` missed on the exact symbol and fell through
//! to its SHORT-NAME pass, which returns whichever same-named alias is first in
//! `rules_by_functor` order. `type_param_global_var` now reads the operation's own
//! record, so the symbol side and the declaration are the same variable by
//! construction and the WI-942 double-recording is gone.
//!
//! WHAT FAILS WITH THE FIX BACKED OUT — measured, by disabling
//! `type_param_global_var`'s op-record arm and re-running:
//!  - `op_type_param_resolves_to_the_variable_its_operation_declares` and
//!    `distinct_operations_do_not_share_one_type_param_variable` — on `IDENT_SRC`,
//!    which is written to LOAD either way for exactly this reason. BOTH `cmp[T]` and
//!    `cmp2[T]` answered `VarId(1)` — `anthill.kernel.T`, first of the 37 `T`-named
//!    `SortAlias` sources a stdlib load asserts — while each declared its own distinct
//!    var (`left: 1, right: 1326` on the first assertion). Two different parameters,
//!    one variable, and neither of them their own.
//!  - `an_op_scoped_requires_covers_its_own_call` — at LOAD, twice: `expected
//!    `requires Ord[…]` covering abstract type parameter, got missing `requires
//!    Ord[T = …]` on enclosing sort`. That is WI-942's defect returning once the
//!    bridge is removed and nothing replaces it, which is what says WI-943 REPLACES
//!    that bridge rather than merely permitting its deletion.
//!  - In `vec3_ops_test.rs`, the same three tests WI-942's own revert table names for
//!    "revert the load-side fix": `one_parameter_spec_op_scoped_requires_now_agrees…`,
//!    `renamed_op_type_params_are_covered_by_the_operations_own_requires`, and
//!    `control_ring_now_loads…`, all at LOAD — while
//!    `a_generic_consumer_of_vector_space_loads_and_dispatches` keeps passing on the
//!    name coincidence WI-942 describes.
//!
//! PASSES EITHER WAY BY DESIGN: `sort_type_param_resolves_through_its_sort_alias` —
//! the sort channel is untouched, and it is what says the fix did not simply move the
//! breakage. (It needs its own source: the first draft shared `IDENT_SRC` with an
//! op-scoped `requires` in it, and under the revert the control died at LOAD alongside
//! the subject — a control that cannot load measures nothing.)

use crate::common::load_kb_with;
use anthill_core::eval::Value;
use anthill_core::kb::op_info::lookup_operation_info;
use anthill_core::kb::term::Term;
use anthill_core::kb::typing::type_param_global_var;
use anthill_core::kb::KnowledgeBase;

/// Deliberately free of the op-scoped `requires` that WI-942 was about: these tests
/// measure the IDENTITY, so the program must load with the fix backed out too.
const IDENT_SRC: &str = r#"
namespace test.wi943.identity
  import anthill.prelude.{Int64, Ord}

  sort OpHolder
    operation cmp[T](a: T, b: T) -> Int64 = 0
    operation cmp2[T](a: T, b: T) -> Int64 = 0
    operation pair[A, B](a: A, b: B) -> Int64 = 0
  end

  sort SortHolder
    sort T = ?
    requires Ord[T]
    operation cmp(a: T, b: T) -> Int64 = Ord.compare(a, b)
  end
end
"#;

/// The variable a type parameter's SYMBOL resolves to, i.e. what a written `T` denotes.
/// This is the route `sigma_class` takes for the `Ref(T)` inside `requires Ord[T]`.
fn via_symbol(kb: &KnowledgeBase, owner_qn: &str, param: &str) -> u32 {
    let sym = kb
        .try_resolve_symbol(&format!("{owner_qn}.{param}"))
        .unwrap_or_else(|| panic!("`{owner_qn}.{param}` must be a defined symbol"));
    type_param_global_var(kb, sym)
        .unwrap_or_else(|| panic!("`{owner_qn}.{param}` must resolve to a canonical var"))
        .raw()
}

/// The variable the OPERATION declares for `param`, straight off its record.
fn via_declaration(kb: &KnowledgeBase, op_qn: &str, param: &str) -> u32 {
    let op = kb.try_resolve_symbol(op_qn).expect("the operation must be defined");
    let rec = lookup_operation_info(kb, op).expect("a declared operation has an OperationInfo");
    let (_, var) = rec
        .type_params
        .iter()
        .find(|(n, _)| kb.local_name_of(*n) == param)
        .unwrap_or_else(|| panic!("`{op_qn}` must declare type param `{param}`"));
    var.as_global().unwrap_or_else(|| panic!("`{op_qn}.{param}` must be a flex Global var")).raw()
}

#[test]
fn op_type_param_resolves_to_the_variable_its_operation_declares() {
    let kb = load_kb_with(IDENT_SRC);
    for (op_qn, param) in [
        ("test.wi943.identity.OpHolder.cmp", "T"),
        ("test.wi943.identity.OpHolder.cmp2", "T"),
        ("test.wi943.identity.OpHolder.pair", "A"),
        ("test.wi943.identity.OpHolder.pair", "B"),
    ] {
        assert_eq!(
            via_symbol(&kb, op_qn, param),
            via_declaration(&kb, op_qn, param),
            "`{op_qn}[{param}]`: the variable a WRITTEN occurrence resolves through must be \
             the one the operation DECLARES",
        );
    }
}

/// The sharper half: agreement is not enough, the answers must also be DISCRIMINATING.
/// Two operations in one sort, each declaring `T`, are two different parameters — and
/// the short-name reader gave both the same variable, so nothing downstream could tell
/// one operation's `T` from the other's. `pair`'s `A` / `B` pin the same property
/// within a single operation.
#[test]
fn distinct_operations_do_not_share_one_type_param_variable() {
    let kb = load_kb_with(IDENT_SRC);
    let cmp_t = via_symbol(&kb, "test.wi943.identity.OpHolder.cmp", "T");
    let cmp2_t = via_symbol(&kb, "test.wi943.identity.OpHolder.cmp2", "T");
    assert_ne!(cmp_t, cmp2_t, "`cmp[T]` and `cmp2[T]` are two parameters, not one");

    let a = via_symbol(&kb, "test.wi943.identity.OpHolder.pair", "A");
    let b = via_symbol(&kb, "test.wi943.identity.OpHolder.pair", "B");
    assert_ne!(a, b, "`pair[A, B]`'s two parameters must be two variables");

    // …and neither of them is the sort-level `T` next door, whose declaration is a
    // different construct entirely.
    let sort_t = via_symbol(&kb, "test.wi943.identity.SortHolder", "T");
    for (label, v) in [("cmp.T", cmp_t), ("cmp2.T", cmp2_t)] {
        assert_ne!(v, sort_t, "`{label}` must not be `SortHolder.T`");
    }
}

/// The identity DRIVEN where it decides something: `sigma_class` reads the written
/// `Ord[T]` through `type_param_global_var`, and `op_requires_covers` compares that
/// against the rigid `check_operation_bodies` minted from the RECORD. When the two
/// disagree the operation's own `requires` fails to cover its own call and the program
/// is refused. Kept here beside the identity assertions — the WI-942 tests measure the
/// same thing through `VectorSpace`, but this is the minimal shape, and it is what says
/// the identity matters rather than merely being tidy.
#[test]
fn an_op_scoped_requires_covers_its_own_call() {
    let src = r#"
namespace test.wi943.covered
  import anthill.prelude.{Int64, Ord}
  sort OpHolder
    operation cmp[T](a: T, b: T) -> Int64 requires Ord[T] = Ord.compare(a, b)
    operation cmp2[T](a: T, b: T) -> Int64 requires Ord[T] = Ord.compare(b, a)
  end
  sort Driver
    operation via(n: Int64) -> Int64 = OpHolder.cmp(7, 3)
    operation via2(n: Int64) -> Int64 = OpHolder.cmp2(7, 3)
  end
end
"#;
    // `interp_for` prints every load error and panics on a dirty load, so the "must
    // LOAD" half needs no separate `try_load_kb_with`. One interpreter for both calls:
    // each is asserted `Ok`, so the trapped-call poisoning footgun does not apply.
    //
    // Driven to a VALUE, and to BOTH verdicts, so a dictionary that resolved somewhere
    // wrong could not pass by returning some Int. `cmp2` reverses its arguments, so the
    // two operations must disagree — which they cannot do if their `T`s are one var.
    let mut interp = crate::common::interp_for(src);
    for (entry, want) in
        [("test.wi943.covered.Driver.via", 1), ("test.wi943.covered.Driver.via2", -1)]
    {
        match interp.call(entry, &[Value::Int(0)]) {
            Ok(Value::Int(n)) => {
                assert_eq!(n, want, "{entry} must compare through its own requirement")
            }
            other => panic!(
                "{entry} must dispatch through the operation's own `requires Ord[T]` \
                 (pre-WI-943 the LOAD was refused `MissingRequiresForSpecOp`); got {other:?}"
            ),
        }
    }
}

/// CONTROL — the SORT parameter channel, untouched by WI-943. Its declaration IS the
/// `SortAlias` fact, which `type_param_global_var`'s exact-symbol pass has always
/// found, so both routes agreed before this change and must still. Without this, the
/// tests above would pass on an implementation that answered from the op record for
/// EVERYTHING and broke sort parameters. Its own source, with no op-scoped `requires`
/// anywhere, so the revert cannot take it down at load with the subject.
#[test]
fn sort_type_param_resolves_through_its_sort_alias() {
    let kb = load_kb_with(
        r#"
namespace test.wi943.sortparam
  import anthill.prelude.{Int64, Ord}
  sort SortHolder
    sort T = ?
    requires Ord[T]
    operation cmp(a: T, b: T) -> Int64 = Ord.compare(a, b)
  end
end
"#,
    );
    let holder = kb.try_resolve_symbol("test.wi943.sortparam.SortHolder").expect("sort");
    assert_eq!(
        kb.type_params_of_sort(holder),
        vec!["T".to_string()],
        "`SortHolder` declares one type param",
    );
    let via_sym = via_symbol(&kb, "test.wi943.sortparam.SortHolder", "T");

    // The declaration side for a sort param: the `SortAlias(T, Var)` fact's target.
    let t_sym = kb.try_resolve_symbol("test.wi943.sortparam.SortHolder.T").expect("SortHolder.T");
    let declared = crate::common::sort_alias_backing_var(&kb, t_sym)
        .expect("`sort T = ?` must assert a `SortAlias` with a Var target")
        .raw();
    assert_eq!(
        via_sym, declared,
        "a sort param's symbol must resolve to its own `SortAlias` target",
    );
}
