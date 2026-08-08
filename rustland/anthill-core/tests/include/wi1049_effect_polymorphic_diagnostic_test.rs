//! WI-1049 — an effect-POLYMORPHIC operation is not an effectful one, and the
//! `[simp]`/`[unfold]` formation gate now says which it is refusing.
//!
//! FOUND BY DRIVING, not by reading. Writing proposal-054's own example law on
//! `PersistentCollection` —
//!
//!     rule isEmpty(insert(?c, ?x)) <=> false [simp]
//!
//! — is refused twice with "an effectful operation is not equational", naming
//! `PersistentCollection.insert` and `Iterable.isEmpty`. NEITHER IS EFFECTFUL.
//! Both carry a row VARIABLE (`effects Effect` / `effects E`), and `List`'s
//! provision is documented pure ("grounded to `{}` at the consumption
//! boundary", list.anthill). The message sent the reader hunting an effect that
//! does not exist.
//!
//! The VERDICT is unchanged and deliberately so: a rule declared on the spec
//! binds every carrier, including one that provides an effectful `insert`,
//! where the rewrite would DROP the call — the effect running zero times
//! instead of once. `effect_row_blocking_equations`' doc has always said the
//! polymorphic case is over-refused knowingly; only the wording was wrong.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT: `polymorphic_row_is_not_reported_as_effectful`
//! and `the_two_arms_read_differently`. `concrete_effect_still_reads_as_effectful`
//! and `pure_carrier_ops_still_admit_the_law` pass either way, BY DESIGN — they
//! are the controls that the classification did not simply relabel everything,
//! and that the gate still admits what it always admitted.

use anthill_core::kb::EquationBlock;

/// A spec whose operations are effect-POLYMORPHIC (`effects E`, a row variable
/// declared `effects E = ?`) — the `PersistentCollection` shape, minimised.
const POLYMORPHIC_SRC: &str = r#"
    namespace wi1049.poly
      import anthill.prelude.{Int64, Bool}
      sort Coll
        sort C = ?
        effects E = ?
        operation put(c: C, x: Int64) -> C effects E
        operation isNone(c: C) -> Bool effects E
      end
    end
"#;

/// The same two operations with NO effects clause at all — genuinely pure.
const PURE_SRC: &str = r#"
    namespace wi1049.pure
      import anthill.prelude.{Int64, Bool}
      sort Box
        entity box(n: Int64)
        operation put(b: Box, x: Int64) -> Box = box(n: x)
        operation isNone(b: Box) -> Bool = false
        rule isNone(put(?b, ?x)) <=> false [simp]
      end
    end
"#;

fn block_for(src: &str, qn: &str) -> Option<EquationBlock> {
    let kb = crate::common::load_kb_with(src);
    let op = kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("no symbol {qn}"));
    kb.effect_row_blocking_equations(op)
}

#[test]
fn polymorphic_row_is_not_reported_as_effectful() {
    // The row `{E}` is a VARIABLE. It blocks — but as `Polymorphic`, and the
    // rendered sentence must not call the operation effectful.
    let block = block_for(POLYMORPHIC_SRC, "wi1049.poly.Coll.put")
        .expect("an effect-polymorphic op still blocks equational treatment");
    assert!(matches!(block, EquationBlock::Polymorphic(_)),
        "`effects E` over a row variable is POLYMORPHIC, not effectful; got {block:?}");
    let sentence = block.to_string();
    assert!(sentence.contains("effect-POLYMORPHIC") && sentence.contains("row VARIABLE"),
        "the sentence must name the row as a variable; got: {sentence}");
    assert!(!sentence.contains("is not a function"),
        "an effect-polymorphic op is not disqualified from function-hood — that \
         claim belongs to the Effectful arm only; got: {sentence}");
}

#[test]
fn path_dependent_row_projection_is_polymorphic_too() {
    // The second spelling of "the row is a parameter": `effects s.E` — the
    // RECEIVER's effect parameter, projected (WI-376/WI-606). `Stream.isEmpty`
    // is written exactly this way.
    //
    // FOUND BY DRIVING the law one place further in: inside `List`, the
    // `insert` leg passes (List declares its OWN pure `insert`, list.anthill:254
    // — an earlier claim that it declares neither was wrong), leaving
    // `Stream.isEmpty`'s `{s.E}` as the only refusal. Reading the HEAD alone
    // called that `Effectful`, reproducing the misdescription WI-1049 exists to
    // fix, one term shape along.
    //
    // BACKED OUT (the `ExprCarried` arm of `effect_member_is_parametric`): this
    // test FAILS — `{s.E}` reverts to `Effectful`. The other tests in this file
    // pass either way; they never exercise a projection.
    let src = r#"
        namespace wi1049.proj
          import anthill.prelude.{Int64, Bool}
          sort Feed
            sort T = ?
            effects E = ?
            operation peek(f: Feed) -> Bool effects f.E
          end
        end
    "#;
    let block = block_for(src, "wi1049.proj.Feed.peek")
        .expect("a projected row still blocks equational treatment");
    assert!(matches!(block, EquationBlock::Polymorphic(_)),
        "`effects f.E` projects the receiver's row PARAMETER — polymorphic, not \
         effectful; got {block:?}");
    assert!(block.row().contains("E"), "the row must still be named: {}", block.row());
}

#[test]
fn concrete_effect_still_reads_as_effectful() {
    // CONTROL — passes with and without the change, by design. A concrete label
    // must keep the original classification and the original claim: no carrier
    // can make this one pure.
    let src = r#"
        namespace wi1049.eff
          import anthill.prelude.{Int64, External}
          sort Sink
            entity sink(n: Int64)
            operation emit(s: Sink, x: Int64) -> Int64 effects External
          end
        end
    "#;
    let block = block_for(src, "wi1049.eff.Sink.emit")
        .expect("an External-rowed op blocks equational treatment");
    assert!(matches!(block, EquationBlock::Effectful(_)),
        "a concrete `External` row is Effectful; got {block:?}");
    assert!(block.row().contains("External"), "the row must name External: {}", block.row());
    assert!(block.to_string().contains("is not a function"),
        "the Effectful arm keeps its claim; got: {block}");
}

#[test]
fn the_two_arms_read_differently() {
    // The point of the change: a reader can tell the cases apart. If both arms
    // rendered alike, the classification would be decoration.
    let poly = block_for(POLYMORPHIC_SRC, "wi1049.poly.Coll.isNone")
        .expect("polymorphic op blocks").to_string();
    let eff = block_for(r#"
        namespace wi1049.eff2
          import anthill.prelude.{Int64, External}
          sort Sink2
            entity sink2(n: Int64)
            operation emit2(s: Sink2, x: Int64) -> Int64 effects External
          end
        end
    "#, "wi1049.eff2.Sink2.emit2").expect("effectful op blocks").to_string();
    assert_ne!(poly, eff, "the two arms must not render identically");
    assert!(poly.contains("pure at a pure carrier"),
        "the polymorphic arm must explain that the row depends on the carrier; got: {poly}");
}

#[test]
fn pure_carrier_ops_still_admit_the_law() {
    // CONTROL — passes either way. The gate is not refusing all laws: over
    // genuinely pure operations the same `[simp]` equation loads clean. This is
    // also the REPAIR the polymorphic message now points at, so it must work.
    let kb = crate::common::load_kb_with(PURE_SRC);
    for qn in ["wi1049.pure.Box.put", "wi1049.pure.Box.isNone"] {
        let op = kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("no symbol {qn}"));
        assert!(kb.effect_row_blocking_equations(op).is_none(),
            "{qn} is pure — it must not block equational treatment");
    }
}
