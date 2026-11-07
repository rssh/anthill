//! WI-20261105-0BD56 — a provision that binds a spec operation to a member of a THIRD sort
//! (neither the spec nor the provider) carries that sort's requirements in its dictionary,
//! at the provision's binding, and is refused at load where nothing supplies them (decided
//! with the user 2026-11-05; proposal 073 §6.3: the binding `describe =
//! LeafDesc.describeLeaf` is the call `lambda (x: Leaf) -> LeafDesc.describeLeaf(x)`, typed
//! at the provision).
//!
//! Before, `gen[A](x: A) requires Desc[T = A] = Desc.describe(x)` called as `gen(leaf())`
//! died `Internal` at the frame push — the dictionary at `Desc[T = Leaf]` held nothing for
//! `LeafDesc requires Tag[G = L]` — and the rule spelling panicked the CLI. The direct call
//! `Desc.describe(leaf())` answered through the typer's own route (WI-20261102-6GAS1).
//!
//! ## Back-out
//!
//! MEASURED, each part backed out alone (temporary switches, one build):
//!   * the members' requirements in the dispatch chain (`provider_dispatch_chain`) — every
//!     row but the refusals and the CONTROL: a call through a requirement dies `Internal` at
//!     the frame push ("neither the spec nor the provider of the dictionary"), and the
//!     defaulted row's `Dog` call is refused at load ("no dictionary can answer");
//!   * the same for a provision written as two clauses only —
//!     `a_provision_of_two_clauses_carries_the_member`;
//!   * the load check of the members' requirements (`provision_requirement_errors`) — the
//!     two refusal rows, whose provisions are no longer refused.
//!
//! The refusals of a member parameter the binding does not fix, or fixes twice, were added
//! from /code-review; both programs load clean on the parent commit.
//!
//! The CONTROL row passes either way, by design, and says why at its site.

use anthill_core::eval;

const GEN: &str = r#"
namespace test.bd56.gen
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Tag
    sort G = ?
    operation tagval(x: G) -> Int64
  end
  sort Leaf
    entity leaf
    provides Tag[G = Leaf]
    operation tagval(x: Leaf) -> Int64 = 7
  end
  sort LeafDesc
    sort L = ?
    requires Tag[G = L]
    operation describeLeaf(x: L) -> Int64 = Tag.tagval(x)
  end
  namespace Leaf
    provides Desc[T = Leaf, describe = LeafDesc.describeLeaf]
  end
  operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)
  operation probe() -> Int64 = Desc.describe(leaf())
  operation useGen() -> Int64 = gen(leaf())
  rule viaGen(?r) :- ?r <=> gen(leaf())
  rule viaUse(?r) :- useGen(?r)
end
"#;

fn call(src: &str, entry: &str) -> Result<eval::Value, eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[])
}

fn answers(src: &str, entry: &str, want: i64) {
    match call(src, entry) {
        Ok(eval::Value::Int(n)) if n == want => {}
        other => panic!("`{entry}` should answer {want}: {other:?}"),
    }
}

/// The ticket's rows: `useGen()` through the interpreter, and `viaGen` from a rule. Before,
/// `Internal("deferred dispatch frame-push: … whose parent `…LeafDesc` is neither the spec nor
/// the provider of the dictionary …")`, and a panic from the rule.
#[test]
fn a_call_through_a_requirement_enters_a_third_sorts_member() {
    answers(GEN, "test.bd56.gen.useGen", 7);
    let mut kb = crate::common::load_kb_with(GEN);
    for goal in ["test.bd56.gen.viaGen(7)", "test.bd56.gen.viaUse(7)"] {
        let q = crate::common::query_pattern_term(&mut kb, goal);
        let sols = kb.resolve(&[q], &anthill_core::kb::resolve::ResolveConfig::default());
        assert!(
            sols.len() == 1 && sols[0].is_definite(),
            "`{goal}` should hold once, definitely: {} solution(s)",
            sols.len()
        );
    }
}

/// CONTROL — the direct call, which the typer's route answered before (WI-20261102-6GAS1) and
/// the dictionary's slot answers now: passes either way.
#[test]
fn the_direct_call_answers_as_before() {
    answers(GEN, "test.bd56.gen.probe", 7);
}

/// Two providers, each binding a member of its own third sort: each answers its own value.
#[test]
fn each_provider_answers_its_own_member() {
    let src = r#"
namespace test.bd56.two
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Tag
    sort G = ?
    operation tagval(x: G) -> Int64
  end
  sort Leaf
    entity leaf
    provides Tag[G = Leaf]
    operation tagval(x: Leaf) -> Int64 = 7
  end
  sort Twig
    entity twig
    provides Tag[G = Twig]
    operation tagval(x: Twig) -> Int64 = 9
  end
  sort LeafDesc
    sort L = ?
    requires Tag[G = L]
    operation describeLeaf(x: L) -> Int64 = Tag.tagval(x)
  end
  sort TwigDesc
    sort W = ?
    requires Tag[G = W]
    operation describeTwig(x: W) -> Int64 = Tag.tagval(x) + 100
  end
  namespace Leaf
    provides Desc[T = Leaf, describe = LeafDesc.describeLeaf]
  end
  namespace Twig
    provides Desc[T = Twig, describe = TwigDesc.describeTwig]
  end
  operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)
  operation useLeaf() -> Int64 = gen(leaf())
  operation useTwig() -> Int64 = gen(twig())
end
"#;
    answers(src, "test.bd56.two.useLeaf", 7);
    answers(src, "test.bd56.two.useTwig", 109);
}

/// A provision over the provider's own parameter: the member's requirement is `Tag[G = Box[V
/// = V]]`, built at each goal's binding — `Box[V = Leaf]` (7 + 1, times 10) and `Box[V =
/// Box[V = Leaf]]` — beside the provision's own condition.
#[test]
fn a_parametric_provision_carries_the_member_at_the_goals_binding() {
    answers(BOX, "test.bd56.par.useBox", 80);
    answers(BOX, "test.bd56.par.useBox2", 90);
    answers(BOX, "test.bd56.par.direct", 80);
}

const BOX: &str = r#"
namespace test.bd56.par
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Tag
    sort G = ?
    operation tagval(x: G) -> Int64
  end
  sort Leaf
    entity leaf
    provides Tag[G = Leaf]
    operation tagval(x: Leaf) -> Int64 = 7
  end
  sort Box
    sort V = ?
    entity box(v: V)
    provides Tag[G = Box[V = V]] :- Tag[G = V] where
      operation tagval(x: Box[V = V]) -> Int64 = match x case box(v) -> Tag.tagval(v) + 1
    end
  end
  sort BoxDesc
    sort B = ?
    requires Tag[G = B]
    operation d(x: B) -> Int64 = Tag.tagval(x) * 10
  end
  namespace Box
    provides Desc[T = Box[V = V], describe = BoxDesc.d] :- Tag[G = V]
  end
  operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)
  operation useBox() -> Int64 = gen(box(v: leaf()))
  operation useBox2() -> Int64 = gen(box(v: box(v: leaf())))
  operation direct() -> Int64 = Desc.describe(box(v: leaf()))
end
"#;

/// A witness: `W` provides `Desc` at `Leaf` and binds the member.
#[test]
fn a_witness_provision_carries_the_member() {
    let src = r#"
namespace test.bd56.wit
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Tag
    sort G = ?
    operation tagval(x: G) -> Int64
  end
  sort Leaf
    entity leaf
    provides Tag[G = Leaf]
    operation tagval(x: Leaf) -> Int64 = 7
  end
  sort LeafDesc
    sort L = ?
    requires Tag[G = L]
    operation describeLeaf(x: L) -> Int64 = Tag.tagval(x) + 1000
  end
  sort W
    provides Desc[T = Leaf, describe = LeafDesc.describeLeaf]
  end
  operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)
  operation useGen() -> Int64 = gen(leaf())
end
"#;
    answers(src, "test.bd56.wit.useGen", 1007);
}

/// WI-20261025-ZAWX9's former refusal row, `TOrd[T = Animal, cmp = Helper.cmp]` with `Helper
/// requires Tag[T = Seven]`: the dictionary carries `Tag[T = Seven]` now, and the binding
/// answers by name on a `Dog` (refused at load before, "no dictionary can answer"), on an
/// `Animal`, and through a requirement (`Internal` at the frame push before). A provision of
/// two clauses still lays out nothing and is still refused
/// (`wi_zawx9_…::a_binding_the_instance_cannot_enter_…`).
#[test]
fn a_defaulted_operations_binding_enters_with_the_members_requirements() {
    let src = r#"
namespace test.bd56.zawx9
  import anthill.prelude.{Int64}
  sort TOrd
    sort T = ?
    operation cmp(a: T, b: T) -> Int64 = 20
  end
  sort Tag
    sort T = ?
    operation tag() -> Int64
  end
  sort Seven
    entity seven
    provides Tag[T = Seven]
    operation tag() -> Int64 = 7
  end
  sort Animal
    entity animal(n: Int64)
  end
  sort Dog
    requires Animal
    entity dog(n: Int64)
  end
  sort Helper
    requires Tag[T = Seven]
    operation cmp(a: Animal, b: Animal) -> Int64 = 30
  end
  sort AscW
    provides TOrd[T = Animal, cmp = Helper.cmp]
  end
  operation direct() -> Int64 = TOrd.cmp(dog(1), dog(2))
  operation directAnimal() -> Int64 = TOrd.cmp(animal(1), animal(2))
  operation gen[A](a: A, b: A) -> Int64 requires TOrd[T = A] = TOrd.cmp(a, b)
  operation viaGen() -> Int64 = gen(animal(1), animal(2))
end
"#;
    answers(src, "test.bd56.zawx9.direct", 30);
    answers(src, "test.bd56.zawx9.directAnimal", 30);
    answers(src, "test.bd56.zawx9.viaGen", 30);
}

/// A provision written as two clauses at one application — alternatives, whose conditions
/// are decided at the dispatch and lay out no slot — owes the member's requirements whichever
/// clause holds, and carries them: through a requirement (`Internal` at the frame push
/// before) and by name.
#[test]
fn a_provision_of_two_clauses_carries_the_member() {
    let src = r#"
namespace test.bd56.alt
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Tag
    sort G = ?
    operation tagval(x: G) -> Int64
  end
  sort Ok
    sort T = ?
  end
  sort Box
    sort V = ?
    entity box(v: V)
    provides Tag[G = Box[V = V]]
    operation tagval(x: Box[V = V]) -> Int64 = 3
  end
  sort LeafDesc
    sort L = ?
    requires Tag[G = L]
    operation describeLeaf(x: L) -> Int64 = Tag.tagval(x)
  end
  namespace Box
    provides Desc[T = Box[V = V], describe = LeafDesc.describeLeaf] :- Ok[T = V]
    provides Desc[T = Box[V = V], describe = LeafDesc.describeLeaf] :- Tag[G = V]
  end
  operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)
  operation useGen() -> Int64 = gen(box(v: 1))
  operation direct() -> Int64 = Desc.describe(box(v: 1))
end
namespace anthill.prelude.Int64
  import test.bd56.alt.Ok
  provides Ok[T = Int64]
end
"#;
    answers(src, "test.bd56.alt.useGen", 3);
    answers(src, "test.bd56.alt.direct", 3);
}

/// Two provisions binding each other's block members: each dictionary carries the frame of
/// the member it binds — what that member's body reads — and not the other provision's
/// bound members in turn, so the layouts are finite and each call answers. `A`'s provision
/// has no condition of its own, so its dictionary holds `B.h`'s `Tag[G = Leaf]` only as the
/// member's. A layout that read the member's whole dispatch chain recursed without end here.
#[test]
fn two_provisions_binding_each_others_members_answer() {
    let src = r#"
namespace test.bd56.cyc
  import anthill.prelude.{Int64}
  sort S1
    sort T = ?
    operation f(x: T) -> Int64
    operation f2(x: T) -> Int64
  end
  sort S2
    sort T = ?
    operation g(x: T) -> Int64
    operation h(x: T) -> Int64
  end
  sort Tag
    sort G = ?
    operation tagval(x: G) -> Int64
  end
  sort Leaf
    entity leaf
    provides Tag[G = Leaf]
    operation tagval(x: Leaf) -> Int64 = 7
  end
  sort A
    sort X = ?
    provides S1[T = Leaf, f = B.h] where
      operation f2(x: Leaf) -> Int64 = Tag.tagval(x) + 1
    end
  end
  sort B
    sort Y = ?
    provides S2[T = Leaf, g = A.f2] :- Tag[G = Leaf] where
      operation h(x: Leaf) -> Int64 = Tag.tagval(x) + 2
    end
  end
  operation g1[P](x: P) -> Int64 requires S1[T = P] = S1.f(x)
  operation g2[P](x: P) -> Int64 requires S2[T = P] = S2.g(x)
  operation u1() -> Int64 = g1(leaf())
  operation u2() -> Int64 = g2(leaf())
end
"#;
    answers(src, "test.bd56.cyc.u1", 9);
    answers(src, "test.bd56.cyc.u2", 8);
}

/// With no `Tag` at `Leaf`, the provision is refused at load, naming the member and the
/// requirement — with no call of it anywhere. The advised repair, `provides Tag[…]` on the
/// carrier, is [`GEN`], which answers.
#[test]
fn a_member_whose_requirement_nothing_provides_is_refused_at_load() {
    let src = r#"
namespace test.bd56.notag
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Tag
    sort G = ?
    operation tagval(x: G) -> Int64
  end
  sort Leaf
    entity leaf
  end
  sort LeafDesc
    sort L = ?
    requires Tag[G = L]
    operation describeLeaf(x: L) -> Int64 = Tag.tagval(x)
  end
  namespace Leaf
    provides Desc[T = Leaf, describe = LeafDesc.describeLeaf]
  end
end
"#;
    let errs = crate::common::load_errors_of(src);
    let ns = "test.bd56.notag";
    assert!(
        errs.iter().any(|e| e.contains(&format!(
            "'{ns}.Leaf' provides '{ns}.Desc' with `describe = {ns}.LeafDesc.describeLeaf`, \
             whose sort requires '{ns}.Tag', but '{ns}.Leaf' does not provide '{ns}.Tag'"
        ))),
        "the provision, refused for its member's requirement: {errs:?}",
    );
}

/// The parametric provision without its condition: `Tag[G = Box[V = V]]` holds only where
/// `Tag[G = V]` does, which nothing at the provision supplies. The advised repair, the
/// provision conditional on it, is [`BOX`], which answers.
#[test]
fn a_parametric_member_requirement_the_provision_cannot_supply_is_refused() {
    let src = BOX.replace(
        "provides Desc[T = Box[V = V], describe = BoxDesc.d] :- Tag[G = V]",
        "provides Desc[T = Box[V = V], describe = BoxDesc.d]",
    );
    assert_ne!(src, BOX, "the fixture's provision was rewritten");
    let errs = crate::common::load_errors_of(&src);
    let ns = "test.bd56.par";
    assert!(
        errs.iter().any(|e| e.contains(&format!(
            "'{ns}.Box' provides '{ns}.Desc' with `describe = {ns}.BoxDesc.d`, whose sort \
             requires '{ns}.Tag'"
        )) && e.contains(&format!("`{ns}.Tag[G = {ns}.Box.V]` beneath it does not hold"))),
        "the provision, refused for its member's requirement: {errs:?}",
    );
}

/// A requirement of the member at a parameter of its sort that its signature does not fix at
/// the provision: nothing chooses the type it is owed at, so the provision is refused naming
/// the parameter, where "nothing provides" would advise a provision that cannot help.
#[test]
fn a_member_requirement_at_a_parameter_the_binding_does_not_fix_is_refused() {
    let src = GEN
        .replace(
            "    sort L = ?\n    requires Tag[G = L]",
            "    sort L = ?\n    sort K = ?\n    requires Tag[G = K]",
        )
        .replace(
            "describeLeaf(x: L) -> Int64 = Tag.tagval(x)",
            "describeLeaf(x: L) -> Int64 = 1",
        );
    assert_ne!(src, GEN, "the fixture's member sort was rewritten");
    let errs = crate::common::load_errors_of(&src);
    let ns = "test.bd56.gen";
    assert!(
        errs.iter().any(|e| e.contains(&format!(
            "'{ns}.Leaf' provides '{ns}.Desc' with `describe = {ns}.LeafDesc.describeLeaf`, \
             whose sort requires '{ns}.Tag', at `{ns}.Tag[G = {ns}.LeafDesc.K]`, which names \
             `{ns}.LeafDesc.K`"
        ))),
        "the provision, refused for the unfixed parameter: {errs:?}",
    );
}

/// The provision's types fix one parameter of the member's sort to two types: `both(x: L, y:
/// L)` bound where the spec takes `Leaf` and `Twig`. No call of the member takes both, so the
/// requirement it owes has no one type, and the provision is refused. Before, it loaded.
#[test]
fn a_member_parameter_the_provision_fixes_twice_is_refused() {
    let src = r#"
namespace test.bd56.twice
  import anthill.prelude.{Int64}
  sort Pair2
    sort T = ?
    sort U = ?
    operation both(x: T, y: U) -> Int64
  end
  sort Tag
    sort G = ?
    operation tagval(x: G) -> Int64
  end
  sort Leaf
    entity leaf
    provides Tag[G = Leaf]
    operation tagval(x: Leaf) -> Int64 = 7
  end
  sort Twig
    entity twig
  end
  sort Same
    sort L = ?
    requires Tag[G = L]
    operation both(x: L, y: L) -> Int64 = Tag.tagval(x)
  end
  namespace Leaf
    provides Pair2[T = Leaf, U = Twig, both = Same.both]
  end
end
"#;
    let errs = crate::common::load_errors_of(src);
    let ns = "test.bd56.twice";
    assert!(
        errs.iter().any(|e| e.contains(&format!(
            "the provision's types fix `{ns}.Same.L` to `Leaf` and to `Twig`"
        ))),
        "the provision, refused for the parameter fixed twice: {errs:?}",
    );
}
