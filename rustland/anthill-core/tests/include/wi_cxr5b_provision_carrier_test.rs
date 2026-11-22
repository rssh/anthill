//! WI-20261122-CXR5B, first step — A PROVISION IS AT ITS CARRIER, AND IS ITS PROVIDER'S OWN
//! WHERE ITS PROVIDER HEADS THAT CARRIER OR ONE OF ITS BINDINGS (decisions 5 and 6 of
//! `docs/design/spec-carrier-set.md`, stage 2; filed with the user 2026-11-22).
//!
//! `anthill.reflect.typing.provision_carrier(?p, ?s, ?c)` answered ONE sort per provision: the
//! binding of the spec's single carrier parameter, read by a ladder of declaration order. With
//! two type-vars that sort moved when two lines were swapped (b3/b4), and so did whether a
//! provider's provision was its own, its inferred default row, and `self_provides`. Now `?c` is
//! the provision's carrier (`typing::provision_carrier`, the one owner): for a spec with a
//! dictionary the SPEC at the provision's bindings (`Bag2[T = Int64, C = MyBag]`), for a
//! self-representing spec the PROVIDER at its own type-vars (`List[T = T]`). A provision is
//! the provider's OWN where the provider is the head of the carrier or of one of its bindings,
//! every binding counting (decision 6) — read by `own_provision`, `self_provides` and the
//! inferred rule of `default_provider`. 058 §3.6's default index is filed per spec at the
//! carrier, and its rows meet a goal where every type-var both bind overlaps.
//!
//! WHAT MOVES — each row says what it answered before at its site. MEASURED 2026-11-22 with
//! `src/` and `stdlib/` backed out and these rows kept: all 8 fail. Each for its own claim: f4
//! loads clean and answers 1; f1's `Num` and the `VectorSpace` shape have no `self_provides`
//! row; b3 reads `Int64`; the rest read the one-sort carrier (`Foo`, `Ones`, `List`,
//! `Colour`). f2's `self_provides` half passes either way, by design.
//!
//! THE REVIEW'S FIXES, MEASURED the same day by putting each pre-review behaviour back at once —
//! a type parameter overlapping any binding, an undeclared bootstrap spec read as declared, a
//! mark dropping every other meeting row: the two rows at the end of this file FAIL, as do the
//! two lookup rows in `kb::defaults::lookup_tests`; the other eight here pass.
//!
//! WHAT DOES NOT MOVE YET: dispatch. Which sort a value-directed call reads, which provider a
//! call's arguments select and the witness filing of the supplier walk still read the single
//! parameter (§4's S, V and W readers, later steps of this ticket). The rows here that run a
//! call drive the default rows through it, and pass on today's dispatch.

use crate::common::{interp_for, load_errors_of, load_kb_with, load_stdlib_kb};
use crate::wi860_default_provider_relations_test::relation_rows;

/// What `{ns}.Driver.answer()` answers.
fn answer(src: &str, ns: &str) -> i64 {
    let mut interp = interp_for(src);
    match interp
        .call(&format!("{ns}.Driver.answer"), &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
    {
        Ok(anthill_core::eval::Value::Int(n)) => n,
        other => panic!("`{ns}.Driver.answer` did not answer an Int64: {other:?}"),
    }
}

/// The rows of `rel` (arity `arity`) one of whose columns is `spec`, a spec's short name —
/// the column `self_provides`, `provision_carrier` and `default_provider` hold it in.
fn rows_of_spec(src: &str, rel: &str, arity: usize, spec: &str) -> Vec<String> {
    let mut kb = load_kb_with(src);
    relation_rows(&mut kb, rel, arity)
        .into_iter()
        .filter(|r| r.split(" | ").any(|col| col == spec))
        .collect()
}

/// b3/b4's `Bag2`, its two type-vars declared in the order given.
fn bag2(ns: &str, first: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Bag2
    sort {first} = ?
    sort {second} = ?
    operation put(c: C, x: T) -> C
  end
  sort MyBag
    entity bag
    provides Bag2[T = Int64, C = Self]
    operation put(c: MyBag, x: Int64) -> MyBag = c
  end
end
"#
    )
}

/// b3/b4. `MyBag provides Bag2[T = Int64, C = Self]`, over `put(c: C, x: T)`, is at
/// `Bag2[T = Int64, C = MyBag]` and is `MyBag`'s own, in both declaration orders. Before, with
/// `T` declared first its carrier was `Int64`, `MyBag` a witness for it with no `self_provides`
/// row and no default; with `C` first it was `MyBag`'s own.
#[test]
fn a_provision_is_at_one_carrier_whichever_type_var_is_declared_first() {
    for (ns, first, second) in [("wicxr5b.tfirst", "T", "C"), ("wicxr5b.cfirst", "C", "T")] {
        let src = bag2(ns, first, second);
        let carrier = rows_of_spec(&src, "provision_carrier", 3, "Bag2");
        assert_eq!(carrier.len(), 1, "{ns}: {carrier:#?}");
        assert!(
            carrier[0].starts_with("MyBag | Bag2 | Bag2[")
                && carrier[0].contains("T = Int64")
                && carrier[0].contains("C = MyBag"),
            "{ns}: the carrier is the spec at both bindings: {carrier:#?}"
        );
        assert_eq!(rows_of_spec(&src, "self_provides", 2, "Bag2"), vec!["MyBag | Bag2".to_string()], "{ns}");
        let defaults = rows_of_spec(&src, "default_provider", 3, "Bag2");
        assert_eq!(defaults.len(), 1, "{ns}: {defaults:#?}");
        assert!(defaults[0].ends_with("| MyBag"), "{ns}: {defaults:#?}");
    }
}

/// Decision 5's table, the carriers a program and the standard library write: the spec at the
/// bindings for a spec with a dictionary, the provider for a self-representing one — `Holder`
/// included, whose `peek(c: C)` beside `joinTwo(a: Self, …)` makes it self-representing
/// (decision 8). Before: `Colour`, `Foo` twice, `Box` for both `Holder` providers, and the
/// bare provider for the stdlib's three.
#[test]
fn a_provisions_carrier_is_its_substituted_sort() {
    let src = r#"
namespace wicxr5b.table
  import anthill.prelude.{Int64, String}
  import anthill.reflect.{SortDomain}
  sort Colour
    entity red
  end
  sort W
    entity w
    provides SortDomain[T = Colour]
    rule domain(?x) :- ?x <=> red()
  end
  sort Coll
    sort C = ?
    sort Elem = ?
    operation first(c: C) -> Elem
  end
  sort Foo
    entity foo
  end
  sort W1
    provides Coll[C = Foo, Elem = Int64]
    operation first(c: Foo) -> Int64 = 1
  end
  sort W2
    provides Coll[C = Foo, Elem = String]
    operation first(c: Foo) -> String = "two"
  end
  sort Holder
    sort C = ?
    sort Element = ?
    operation peek(c: C) -> Int64
    operation joinTwo(a: Self, b: Self) -> Int64
  end
  sort Box
    entity box(n: Int64)
  end
  sort BoxHolder
    provides Holder[C = Box, Element = Int64]
    operation peek(c: Box) -> Int64 = 2
    operation joinTwo(a: BoxHolder, b: Holder) -> Int64 = 3
  end
  sort Bag
    entity bag(n: Int64)
    provides Holder[C = Box, Element = Int64]
    operation peek(c: Box) -> Int64 = 2
    operation joinTwo(a: Bag, b: Holder) -> Int64 = 3
  end
end
"#;
    let mut kb = load_kb_with(src);
    let rows = relation_rows(&mut kb, "provision_carrier", 3);
    for want in [
        "W | SortDomain | SortDomain[T = Colour]",
        "W1 | Coll | Coll[C = Foo, Elem = Int64]",
        "W2 | Coll | Coll[C = Foo, Elem = String]",
        "BoxHolder | Holder | BoxHolder",
        "Bag | Holder | Bag",
        "Option | Monad | Monad[M = Option[T = T]]",
        "List | Stream | List[T = T]",
        "FiniteStream | Stream | FiniteStream[T = T, E = E]",
    ] {
        assert!(rows.contains(&want.to_string()), "missing `{want}`");
    }
}

/// The stdlib's `Stream` providers keep their inferred default rows, each at its own carrier,
/// and those do not overlap: the standard library loads, `one_default` passing (decision 5's
/// reason for reading a self-representing spec at the provider — at `Stream[T = T, E = …]`,
/// six rows would unify).
#[test]
fn the_stream_providers_are_their_own_defaults_at_their_own_carriers() {
    let mut kb = load_stdlib_kb();
    let rows = relation_rows(&mut kb, "default_provider", 3);
    for want in [
        "Stream | List[T = T] | List",
        "Stream | FiniteStream[T = T, E = E] | FiniteStream",
        "Stream | LogicalStream[T = T, E = E] | LogicalStream",
    ] {
        assert!(rows.contains(&want.to_string()), "missing `{want}`");
    }
}

/// f1. `Num provides Coll[C = Foo, Elem = Self]`: `Num` heads a binding, so the provision is
/// `Num`'s own (decision 6, every binding counting) and gains an inferred default row. Before,
/// a witness at `Foo`, with no `self_provides` row. The call answers 42 either way.
#[test]
fn a_provider_named_only_at_a_result_type_var_owns_its_provision() {
    let ns = "wicxr5b.resultonly";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Coll
    sort C = ?
    sort Elem = ?
    operation first(c: C) -> Elem
  end
  sort Foo
    entity foo
  end
  sort Num
    entity num(v: Int64)
    provides Coll[C = Foo, Elem = Self, first = Num.firstOf]
    operation firstOf(c: Foo) -> Num = num(v: 42)
    operation value(n: Num) -> Int64 =
      match n
        case num(v) -> v
  end
  sort Driver
    operation answer() -> Int64 = Num.value(Coll.first(foo))
  end
end
"#
    );
    assert_eq!(rows_of_spec(&src, "self_provides", 2, "Coll"), vec!["Num | Coll".to_string()]);
    assert_eq!(
        rows_of_spec(&src, "default_provider", 3, "Coll"),
        vec!["Coll | Coll[C = Foo, Elem = Num] | Num".to_string()]
    );
    assert_eq!(answer(&src, ns), 42);
}

/// f2, the control of decision 6's rule 1 against rule 2: `Foo provides Dflt[T = Self]` over
/// `dflt() -> T`, its one type-var in a result only, keeps its own provision and its default.
/// Its `self_provides` half passes either way, by design; the default row's carrier is the
/// substituted sort, where it was `Foo`.
#[test]
fn a_provision_at_a_result_only_type_var_stays_its_providers_own() {
    let src = r#"
namespace wicxr5b.dflt
  sort Dflt
    sort T = ?
    operation dflt() -> T
  end
  sort Foo
    entity foo
    provides Dflt[T = Self]
    operation dflt() -> Foo = foo
  end
end
"#;
    assert_eq!(rows_of_spec(src, "self_provides", 2, "Dflt"), vec!["Foo | Dflt".to_string()]);
    assert_eq!(
        rows_of_spec(src, "default_provider", 3, "Dflt"),
        vec!["Dflt | Dflt[T = Foo] | Foo".to_string()]
    );
}

/// f4's program, one of its two provisions marked `default provides` by `mark`.
fn two_owns(ns: &str, mark: &str) -> String {
    let (num, foo) = match mark {
        "Num" => ("default provides", "provides"),
        "Foo" => ("provides", "default provides"),
        _ => ("provides", "provides"),
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Coll
    sort C = ?
    sort Elem = ?
    operation first(c: C) -> Elem
  end
  sort Num
    entity num(v: Int64)
    {num} Coll[C = Foo, Elem = Self, first = Num.firstOf]
    operation firstOf(c: Foo) -> Num = num(v: 2)
    operation value(n: Num) -> Int64 =
      match n
        case num(v) -> v
  end
  sort Foo
    entity foo
    {foo} Coll[C = Self, Elem = Num, first = Foo.firstOf]
    operation firstOf(c: Foo) -> Num = num(v: 1)
  end
  sort Driver
    operation answer() -> Int64 = Num.value(Coll.first(foo))
  end
end
"#
    )
}

/// f4. `Num` and `Foo` each provide `Coll[C = Foo, Elem = Num]` for themselves, each heading a
/// binding: two own rows at one carrier, refused at load (`DefaultCollision::TwoOwnProviders`)
/// until one is marked `default provides`, which a call then takes. Before, the program ran and
/// answered 1: `Foo`'s provision its own and the default, `Num` a witness for `Foo`.
#[test]
fn two_providers_owning_one_carrier_are_refused_until_one_is_marked() {
    let errs = load_errors_of(&two_owns("wicxr5b.twoowns", ""));
    assert!(
        errs.iter().any(|e| e.contains("two own defaults") && e.contains("Coll[C = Foo, Elem = Num]")),
        "{errs:#?}"
    );
    assert_eq!(answer(&two_owns("wicxr5b.markfoo", "Foo"), "wicxr5b.markfoo"), 1, "the mark on `Foo`'s");
    assert_eq!(answer(&two_owns("wicxr5b.marknum", "Num"), "wicxr5b.marknum"), 2, "the mark on `Num`'s");
}

/// `VectorSpace`'s shape with `F` declared first: `vec_scale(c: F, v: V)` takes `F` too, so the
/// single parameter was `F`, and `Vec3 provides VS[V = Self, F = Float]` read as a witness for
/// `Float` — no `self_provides` row. Now `Vec3` heads `V`'s binding in either order.
#[test]
fn a_vector_space_declared_field_first_is_its_vectors_own() {
    let src = r#"
namespace wicxr5b.vs
  import anthill.prelude.{Float}
  sort VS
    sort F = ?
    sort V = ?
    operation vec_scale(c: F, v: V) -> V
  end
  sort Vec3
    entity vec3(x: Float, y: Float, z: Float)
    provides VS[V = Self, F = Float]
    operation vec_scale(c: Float, v: Vec3) -> Vec3 = v
  end
end
"#;
    assert_eq!(rows_of_spec(src, "self_provides", 2, "VS"), vec!["Vec3 | VS".to_string()]);
}

/// g2. Two providers of a self-representing spec, each at its own carrier (`Ones[T = T]`,
/// `Twos[T = T]`, where both were bare), and the call's values pick them: 12 either way.
#[test]
fn a_self_representing_specs_providers_are_each_at_its_own_carrier() {
    let ns = "wicxr5b.src";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Src
    sort T = ?
    operation next(s: Self) -> Int64
  end
  sort Ones
    sort T = ?
    entity ones
    provides Src[T = T]
    operation next(s: Ones) -> Int64 = 1
  end
  sort Twos
    sort T = ?
    entity twos
    provides Src[T = T]
    operation next(s: Twos) -> Int64 = 2
  end
  sort Driver
    operation answer() -> Int64 = Src.next(ones) * 10 + Src.next(twos)
  end
end
"#
    );
    assert_eq!(
        rows_of_spec(&src, "default_provider", 3, "Src"),
        vec!["Src | Ones[T = T] | Ones".to_string(), "Src | Twos[T = T] | Twos".to_string()]
    );
    assert_eq!(answer(&src, ns), 12);
}

/// A KB loaded WITHOUT the standard library: its `PartialEq` is a bootstrap name with no
/// declaration and no type-var, and the equality derivation's rows are each a composite's own
/// provision, at the composite, with an inferred default row. Read as a declared spec of no
/// type-var, each was a witness at the bare spec and had no row (found by review).
#[test]
fn a_bare_kbs_derived_equality_is_its_composites_own() {
    let kb = crate::common::load_kb_bare(&["namespace wicxr5b.bare\n  sort Leaf\n    entity leaf\n  end\nend\n"]);
    let rows = kb
        .default_provider_index()
        .expect("a loaded KB carries the default index")
        .rendered_rows(&kb);
    assert!(rows.iter().any(|r| r == "PartialEq | Leaf | Leaf"), "{rows:#?}");
}

/// `one_default` gives one verdict whichever type-var is declared first: a mark on a provision
/// at a type parameter (`Coll[C = E, Elem = Int64]`, at every `C`) beside a mark at
/// `Coll[C = Foo, Elem = Int64]` coexist, a type parameter at the top of a binding meeting only
/// itself. Before the review's fix the pair loaded with `C` declared first and was refused as
/// overlapping with `Elem` first, the rows then partitioned by `Elem`'s binding.
#[test]
fn a_mark_at_a_type_parameter_beside_one_at_a_sort_loads_in_either_order() {
    for (ns, first, second) in [("wicxr5b.anyc", "C", "Elem"), ("wicxr5b.anye", "Elem", "C")] {
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Coll
    sort {first} = ?
    sort {second} = ?
    operation first(c: C) -> Elem
  end
  sort Foo
    entity foo
  end
  sort AnyC
    sort E = ?
    default provides Coll[C = E, Elem = Int64]
    operation first(c: E) -> Int64 = 1
  end
  sort W
    default provides Coll[C = Foo, Elem = Int64]
    operation first(c: Foo) -> Int64 = 2
  end
end
"#
        );
        let errs = load_errors_of(&src);
        assert!(!errs.iter().any(|e| e.contains("overlapping defaults")), "{ns}: {errs:#?}");
    }
}
