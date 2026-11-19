//! A CONSTRAINT'S VARIABLES ARE TYPED AS A RULE'S (WI-20261105-CBRD2; the user, 2026-11-19). A
//! constraint is a headless rule (kernel-language §6.2), and a rule takes no dictionary it does
//! not declare: a call at a variable's type needs that type to be one the clause can supply. A
//! rule types a variable by writing it in a head column, `?x: T`; a constraint has no head, and
//! the written type was refused anywhere else ("only meaningful in a rule head pattern"). So a
//! spec's law over its own `T` had no spelling at all: `WeakOrd`'s `compare_congruent`,
//! `eq(compare(?a, ?b), 0) :- eq(?a, ?b)`, read its calls at a type its typing inferred, which
//! only the broad reading of the sort's requirement admitted — the reading that also admitted a
//! rule's call at another instance of the sort (`wi_80zv8_bare_own_sort_test`).
//!
//! A variable's written type is read in a constraint's goals as in a rule head: the bound of
//! the constraint's clause, the type variables it names joining the clause's frame, read by its
//! typing. `WeakOrd`'s law is `eq(compare(?a: T, ?b: T), 0) :- eq(?a, ?b)`, and `Set`'s
//! `contains` types its column, `?x: T`.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every row
//! passes.
//!
//! * The written type refused in a constraint, as before: the stdlib does not load (its typed
//!   law), and with it every row, the quantified one too.
//! * The bound's type variables left out of the clause's frame: the typed law is refused, its
//!   calls read at a type no head column reaches — the stdlib does not load.
//! * The sort's requirement taken to supply any type: [`a_constraints_variable_is_typed_as_a_rules`]
//!   fails, the untyped law loading.

use crate::common::load_errors_of;

/// A spec `Cmp` stating `law` among its members, and two `num` facts.
fn spec(law: &str, tail: &str) -> String {
    format!(
        r#"
namespace test.cbrd2.ctv
  import anthill.prelude.{{Int64, Bool, PartialEq}}
  import anthill.prelude.PartialEq.{{eq}}
  import anthill.prelude.PartialOrd.{{gt}}
  sort Cmp
    sort T = ?
    requires PartialEq[T = T]
    operation cmp(a: T, b: T) -> Int64
    {law}
  end
  sort Num
    entity num(v: Int64)
  end
  fact num(v: 3)
  fact num(v: 5)
{tail}end
"#
    )
}

/// The law over the spec's own `T`, its variables typed, loads; untyped, both its calls are
/// refused at a type nothing supplies; one variable typed two ways is refused, as in a rule head.
#[test]
fn a_constraints_variable_is_typed_as_a_rules() {
    assert_eq!(
        load_errors_of(&spec("constraint congruent: eq(cmp(?a: T, ?b: T), 0) :- eq(?a, ?b)", "")),
        Vec::<String>::new(),
        "typed at the spec's own `T`"
    );
    let untyped = load_errors_of(&spec("constraint congruent: eq(cmp(?a, ?b), 0) :- eq(?a, ?b)", ""));
    assert!(
        untyped.iter().any(|e| e.contains("call of `test.cbrd2.ctv.Cmp.cmp`"))
            && untyped.iter().any(|e| e.contains("call of `anthill.prelude.PartialEq.eq`")),
        "untyped, both calls refused: {untyped:?}"
    );
    let twice = load_errors_of(&spec("constraint congruent: eq(cmp(?a: T, ?b: T), 0) :- eq(?a: Int64, ?b)", ""));
    assert!(
        twice.iter().any(|e| e.contains("conflicting type annotations")),
        "a variable typed two ways: {twice:?}"
    );
}

/// A guard's variable written with its type is read by the guard as without one: `gt(?n:
/// Int64, 0)` holds over `num(3)` and `num(5)`, and `gt(?n: Int64, 4)` is violated by `num(3)`.
#[test]
fn a_typed_variable_in_a_quantified_constraint_is_read() {
    assert_eq!(
        load_errors_of(&spec("", "  constraint pos: forall ?n: num(v: ?n) -: gt(?n: Int64, 0)\n")),
        Vec::<String>::new(),
        "every `num` is positive"
    );
    let violated = load_errors_of(&spec("", "  constraint big: forall ?n: num(v: ?n) -: gt(?n: Int64, 4)\n"));
    assert!(
        violated.iter().any(|e| e.contains("integrity constraint 'big' is violated")),
        "`num(3)` violates it: {violated:?}"
    );
}
