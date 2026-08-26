//! WI-20260825-X9RRN — A PROVIDED MEMBER ANSWERS TO THE HEAD THAT OFFERS IT.
//!
//! ## The half-kept promise this closes
//!
//! A spec's `provides` is a CONVERSION — "hold a `Numeric[T]` and you can obtain an
//! `Additive[T]`" — and it brings the provided sort's scope with it. So one spelling of
//! the inherited member has always worked:
//!
//!   `import anthill.prelude.Numeric.{add}` then bare `add(a, b)`   -> resolves
//!   `Numeric.add(a, b)` written out                                 -> "unknown functor"
//!
//! The two are the same question. The first is answered by `process_imports`' strategy 2,
//! which resolves the short name IN the base scope and so crosses the parent link
//! `wire_provides_scope_parent` wrote; the second by `load::dotted_by_head`, a
//! `by_qualified_name` string join for which `anthill.prelude.Numeric.add` is simply not a
//! key. `load::dotted_by_provision` is the missing rung.
//!
//! ## Why provides-ONLY, and not the import path's walk
//!
//! The obvious fix — `resolve_in_scope(tail, head's scope)`, literally what the import
//! path does — was measured and rejected. That walk crosses `requires` edges and re-enters
//! the enclosing chain, and on the DELIVERED tree both over-hits are live:
//!
//!   `import anthill.prelude.Numeric.{List}` -> LOADS   `List` is a SIBLING of `Numeric`
//!   `import anthill.prelude.Numeric.{lt}`   -> LOADS   `lt` is `PartialOrd`'s, by `requires`
//!
//! Copying it would have minted `Numeric.List` and `Numeric.lt` as addresses. Both rows
//! below refuse them, at the qualified spelling. The import path's own over-hits are NOT
//! touched here — a different population, and a `Sort.{Sibling}` import is WI-751's shape
//! one clause over rather than this ticket's.
//!
//! ## The back-out these rows are stated against
//!
//! Delete the `None =>` arm of `resolve_dotted_in_kb`'s relative reading (the
//! `dotted_by_provision` call). Then every POSITIVE row here fails with "unknown functor"
//! / "names nothing". The two NEGATIVE rows (`requires` is not an address, the enclosing
//! namespace is not an address) pass either way BY DESIGN — they are what says the rung
//! was widened by exactly one edge kind, and they are the rows that fail if the walk is
//! ever re-spelled as `resolve_in_scope`.

use crate::common::{interp_for, try_load_kb_with};

/// Load `src`, call `qn`, render the value.
fn drive(src: &str, qn: &str) -> String {
    let mut interp = interp_for(src);
    let got = interp
        .call(qn, &[])
        .unwrap_or_else(|e| panic!("{qn} must evaluate: {e:?}"));
    format!("{got:?}")
}

/// The load errors of `src`, empty when it loads.
fn errs_of(src: &str) -> Vec<String> {
    try_load_kb_with(src)
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e)
}

/// PURE USER SORTS, DRIVEN TO A VALUE. `Mid` declares nothing; it reaches `zug` through
/// `provides Base[T = T]`, and `Mid.zug(…)` must both RESOLVE and DISPATCH to the
/// carrier's own body.
///
/// 42 rather than "it loads": the address resolving to `Base.zug` is only half the claim
/// — the other half is that dispatch off `fact Mid[T = Cell]` still finds `Cell.zug`
/// through the same conversion. A rung that resolved the name but broke the dispatch
/// would load clean and answer nothing.
///
/// BACKED OUT: "type mismatch in Mid.zug.apply: … got unknown functor" — measured on the
/// delivered tree, and the ticket's own repro.
#[test]
fn a_provided_member_is_callable_at_the_offering_heads_address() {
    let src = r#"
namespace test.x9rrn.user
  import anthill.prelude.{Int64}
  sort Base
    sort T = ?
    operation zug(x: T) -> T
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  sort Cell
    entity Cell(v: Int64)
    operation zug(x: Cell) -> Cell = Cell(v: x.v + 1)
  end
  fact Mid[T = Cell]
  operation drive() -> Int64 = Mid.zug(Cell(v: 41)).v
end
"#;
    assert_eq!(
        drive(src, "test.x9rrn.user.drive"),
        "Int(42)",
        "`Mid.zug` must reach the `Base.zug` that `provides` puts in `Mid`'s hands, and \
         dispatch to the carrier's own body"
    );
}

/// THE THREE STDLIB ADDRESSES THE TICKET NAMED, each computing rather than loading.
///
/// `Eq.eq` has been "unknown functor" since WI-1109/WI-1110 moved `eq` onto `PartialEq`,
/// `Field.div` since WI-20260824-VT8CF moved `div` onto `Divisible`, and
/// WI-20260825-1WBZT added `Numeric.{add,sub,mul,neg}` and `Ring`'s five to the same
/// population. One rung answers all of them.
#[test]
fn the_stdlib_addresses_the_ticket_named_now_compute() {
    let src = r#"
namespace test.x9rrn.stdlib
  import anthill.prelude.{Int64, Bool, Float, Numeric, Eq}
  import anthill.prelude.algebra.{Field, Ring}
  operation same() -> Bool = Eq.eq(21, 21)
  operation plus() -> Int64 = Numeric.add(20, 22)
  operation quot() -> Float = Field.div(10.0, 4.0)
  operation dbl() -> Float = Ring.add(2.5, 2.5)
end
"#;
    for (op, want) in [
        ("same", "Bool(true)"),
        ("plus", "Int(42)"),
        ("quot", "Float(2.5)"),
        ("dbl", "Float(5.0)"),
    ] {
        assert_eq!(
            drive(src, &format!("test.x9rrn.stdlib.{op}")),
            want,
            "`{op}` writes a qualified address reached through `provides`; it must \
             resolve to the DECLARING spec's operation and dispatch"
        );
    }
}

/// THE ADDRESS RESOLVES TO THE DECLARING SPEC, NOT TO A HEAD-OWNED COPY — and the proof
/// is a message that NAMES the symbol.
///
/// A nullary spec op cannot select a provider from its arguments, so `Additive.zero()`
/// reports "ambiguous dispatch of `anthill.prelude.Additive.zero`". Writing `Numeric.zero()`
/// and `Ring.zero()` must produce that SAME sentence, naming `anthill.prelude.Additive.zero`
/// — which is only possible if both addresses landed on the one declaration. An
/// alias-shaped fix that minted `anthill.prelude.Numeric.zero` would name itself here.
///
/// It is also the row that separates "resolved" from "loads": WI-20260825-6RRVA is open
/// precisely because a law position accepts a name that denotes nothing, so loadability
/// proves nothing about an address. A dispatch complaint that spells the target does.
#[test]
fn the_resolved_target_is_the_declaring_spec() {
    let goal = |head: &str| {
        format!(
            r#"
namespace test.x9rrn.target
  import anthill.prelude.{{Int64, Numeric, Additive}}
  import anthill.prelude.algebra.{{Ring}}
  rule g(?r) :- ?r = {head}.zero()
end
"#
        )
    };
    for head in ["Additive", "Numeric", "Ring"] {
        let errs = errs_of(&goal(head));
        assert!(
            errs.iter().any(|e| e.contains("ambiguous dispatch of")
                && e.contains("anthill.prelude.Additive.zero")),
            "`{head}.zero` must denote `anthill.prelude.Additive.zero` itself — the \
             nullary ambiguity is what names the symbol the address landed on; got {errs:?}"
        );
    }
}

/// A `requires` IS NOT AN ADDRESS, and the same member IS reachable bare — both halves,
/// because only together do they say the rung was narrowed on purpose rather than by
/// accident.
///
/// `requires Mid[T]` means "a caller hands me one", not "I have one to offer under my
/// name". So `Mid.zug` from a scope that merely requires `Mid` is not an address for
/// `Base.zug`… except that here `Mid` PROVIDES `Base`, so it is — which is why the
/// refusal has to be measured on a head that only REQUIRES its target.
///
/// PASSES ON THE PRE-CHANGE TREE TOO, by design: it is what fails if the rung is ever
/// re-spelled as `resolve_in_scope` at the head's scope, which crosses `requires` edges.
/// The stdlib witness is `Numeric.lt` — `Numeric requires PartialOrd[T]` and `lt` is
/// `PartialOrd`'s — and the bare control beside it is `zug`, chosen because it is NOT an
/// implicit-prelude name: a bare `lt` would resolve through the tier and measure nothing.
#[test]
fn a_requires_is_not_an_address_though_it_is_reachable_bare() {
    let qualified = r#"
namespace test.x9rrn.req
  import anthill.prelude.{Int64, Numeric}
  rule g(?a, ?r) :- ?r = Numeric.lt(?a, ?a)
end
"#;
    let errs = errs_of(qualified);
    assert!(
        errs.iter()
            .any(|e| e.contains("Numeric.lt") && e.contains("names nothing")),
        "`Numeric requires PartialOrd[T]`; a requirement is not a member, so `Numeric.lt` \
         must stay unaddressable — this is the row that refuses the `resolve_in_scope` \
         spelling of the rung; got {errs:?}"
    );

    // THE CONTROL, on a name the implicit tier cannot rescue: `requires` DOES put the
    // provided member in scope BARE, which is why the qualified refusal above costs
    // nothing.
    let bare = r#"
namespace test.x9rrn.reqbare
  sort Base
    sort T = ?
    operation zug(x: T) -> T
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  sort User
    sort T = ?
    requires Mid[T]
    operation viaMid(x: T) -> T = zug(x)
  end
end
"#;
    assert!(
        errs_of(bare).is_empty(),
        "a `requires Mid[T]` must still reach `Mid`'s PROVIDED `zug` bare — the parent \
         walk crosses both edge kinds and that is untouched here; got {:?}",
        errs_of(bare)
    );
}

/// THE ENCLOSING NAMESPACE IS NOT AN ADDRESS EITHER — the second refusal, and the second
/// row that passes both ways by design.
///
/// `sibling` is declared BESIDE `Mid`, not inside it. `resolve_in_scope` at `Mid`'s scope
/// would find it by walking out to the namespace — measured on the stdlib as
/// `import anthill.prelude.Numeric.{List}` loading clean, `List` being `Numeric`'s
/// SIBLING. The join-per-provided-sort cannot: each hop asks `by_qualified_name` at a
/// sort's own path, so a sort answers with what it DECLARES and nothing it merely sees.
#[test]
fn the_enclosing_namespace_is_not_an_address() {
    let src = r#"
namespace test.x9rrn.encl
  import anthill.prelude.{Int64}
  operation sibling(x: Int64) -> Int64 = x
  sort Base
    sort T = ?
    operation zug(x: T) -> T
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  rule g(?a, ?r) :- ?r = Mid.sibling(?a)
end
"#;
    let errs = errs_of(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("Mid.sibling") && e.contains("names nothing")),
        "`sibling` is a NEIGHBOUR of `Mid`, not a member reached by any conversion — the \
         rung joins per provided sort rather than walking `Mid`'s scope; got {errs:?}"
    );
}

/// RUNG ONE STILL WINS, driven with values that DISAGREE.
///
/// The provision rung sits BELOW the declared-member join and fires only on a miss, so no
/// name that resolved before can move. Asserting that with two bodies returning the same
/// number would measure nothing: `Mid.zug` adds 1 and `Base.zug` subtracts 1, so the
/// answer says which declaration won.
#[test]
fn rung_one_still_wins_over_the_provision() {
    let src = r#"
namespace test.x9rrn.rung1
  import anthill.prelude.{Int64}
  sort Base
    sort T = ?
    operation zug(x: T) -> T
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
    operation zug(x: T) -> T
  end
  sort Cell
    entity Cell(v: Int64)
    operation zug(x: Cell) -> Cell = Cell(v: x.v + 1)
  end
  fact Mid[T = Cell]
  operation drive() -> Int64 = Mid.zug(Cell(v: 41)).v
end
"#;
    assert_eq!(
        drive(src, "test.x9rrn.rung1.drive"),
        "Int(42)",
        "a head that DECLARES the name answers with its own — the provision rung is \
         consulted only where the join missed"
    );
}

/// TWO PROVISION ROUTES ARE AN AMBIGUITY, NOT A COIN FLIP — and in BOTH source orders.
///
/// `Mid provides L` and `Mid provides R`, each declaring `b`. One level, two hits: the
/// rung returns `Ambiguous` and the ladder reports it by name
/// (`Loader::resolve_dotted_reported`). Running the two clause orders is the point —
/// WI-20260825-EBMG8's finding is that a same-named member reached twice resolves by
/// SOURCE ORDER, stable in tests and stable across machines, which is worse than a coin
/// flip because it looks safe. This rung must not add a fourth instance of that.
///
/// The candidates are asserted, not just "an error": "names nothing" is also an error and
/// is the opposite verdict.
#[test]
fn two_provision_routes_are_ambiguous_in_either_source_order() {
    let program = |first: &str, second: &str| {
        format!(
            r#"
namespace test.x9rrn.amb
  sort L
    sort T = ?
    operation b(x: T) -> T
  end
  sort R
    sort T = ?
    operation b(x: T) -> T
  end
  sort Mid
    sort T = ?
    provides {first}[T = T]
    provides {second}[T = T]
  end
  sort User
    sort T = ?
    operation viaMid(x: T) -> T = Mid.b(x)
  end
end
"#
        )
    };
    for (a, b) in [("L", "R"), ("R", "L")] {
        let errs = errs_of(&program(a, b));
        assert!(
            errs.iter().any(|e| e.contains("ambiguous symbol 'Mid.b'")
                && e.contains("test.x9rrn.amb.L.b")
                && e.contains("test.x9rrn.amb.R.b")),
            "with `provides {a}` before `provides {b}`, `Mid.b` reaches two declarations \
             and must SAY so rather than pick by clause order (WI-20260825-EBMG8); got \
             {errs:?}"
        );
    }
}

/// THE CHAIN IS TRANSITIVE, AND THE NEARER LEVEL WINS.
///
/// `Top provides Mid`, `Mid provides Base`, and both `Mid` and `Base` declare `zug`. A
/// walk that collected every level would call this ambiguous; level-by-level makes it
/// `Mid`'s, which is the same "nearest declaration wins" `resolve_in_scope` gives a
/// parent chain. Driven with disagreeing bodies again — `Mid.zug` adds 1, `Base.zug`
/// adds 100 — so the number names the level.
///
/// The stdlib has no two-hop chain to drive this on: `Ord provides WeakOrd` and
/// `Eq provides PartialEq` are one hop each, and `WeakOrd` reaches `PartialOrd` by
/// `requires`. Hence user sorts.
#[test]
fn the_provision_chain_is_transitive_and_the_nearest_level_wins() {
    let src = r#"
namespace test.x9rrn.deep
  import anthill.prelude.{Int64}
  sort Base
    sort T = ?
    operation zug(x: T) -> T
    operation far(x: T) -> T
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
    operation zug(x: T) -> T
  end
  sort Top
    sort T = ?
    provides Mid[T = T]
  end
  sort Cell
    entity Cell(v: Int64)
    operation zug(x: Cell) -> Cell = Cell(v: x.v + 1)
    operation far(x: Cell) -> Cell = Cell(v: x.v + 100)
  end
  fact Top[T = Cell]
  operation near() -> Int64 = Top.zug(Cell(v: 41)).v
  operation deep() -> Int64 = Top.far(Cell(v: 41)).v
end
"#;
    assert_eq!(
        drive(src, "test.x9rrn.deep.near"),
        "Int(42)",
        "`Top.zug` must take `Mid`'s declaration — one hop — and not go on to `Base`'s"
    );
    assert_eq!(
        drive(src, "test.x9rrn.deep.deep"),
        "Int(141)",
        "`Top.far` is declared only on `Base`, two hops out; the walk must reach it"
    );
}

/// THE RESIDUAL, PINNED WITH ITS CONTROL: a TYPE reference does not read this ladder.
///
/// `Mid.f()` in TERM position now resolves through the conversion; `Mid.Inner` in TYPE
/// position does not, and the message says why — it is read as a TYPE PROJECTION by a
/// separate check with its own member table ("type '…Mid' has no member 'Inner'"), never
/// by `resolve_dotted_in_kb`. The DECLARED twin `Base.Inner` loads in the same position, so
/// the difference is the conversion and not the spelling.
///
/// NOT WIDENED HERE, and the reason is that it is a different QUESTION rather than the same
/// one at a second site. "What does this dotted NAME denote" is what the ladder answers; a
/// type projection asks "does this TYPE have this member", and a spec's `provides` is
/// documented as a value-level conversion — "hold a `Mid[T]` and you can obtain a
/// `Base[T]`" — which says nothing about a nested SORT being reachable through it. Deciding
/// that is a design question with its own population, and the type-member table is exactly
/// where WI-751's field over-hit lived. Filed rather than absorbed.
///
/// BOTH HALVES ARE ASSERTED. Without the `Base.Inner` control, the refusal reads as "a
/// nested sort is unnameable from outside", which is false; without the refusal, nothing
/// records that the rung stops at the ladder's own readers.
#[test]
fn the_type_position_reads_a_different_table() {
    let program = |head: &str| {
        format!(
            r#"
namespace test.x9rrn.typepos
  import anthill.prelude.{{Int64}}
  sort Base
    sort T = ?
    sort Inner
      entity inner(v: Int64)
    end
    operation f() -> Int64 = 41
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  sort Use
    operation g(x: {head}.Inner) -> Int64 = 2
  end
end
"#
        )
    };
    assert!(
        errs_of(&program("Base")).is_empty(),
        "THE CONTROL: a nested sort IS nameable in type position when the head \
         declares it; got {:?}",
        errs_of(&program("Base"))
    );
    let errs = errs_of(&program("Mid"));
    assert!(
        errs.iter()
            .any(|e| e.contains("has no member 'Inner'")),
        "the TYPE position reads a type-projection table, not the dotted ladder, so \
         the conversion does not reach it — recorded rather than widened; got {errs:?}"
    );
}

/// A DIAMOND IS ONE ANSWER, NOT AN AMBIGUITY — the row beside
/// `two_provision_routes_are_ambiguous_in_either_source_order`, and the one that says the
/// ambiguity arm discriminates rather than fires on any two routes.
///
/// `Mid provides L` and `Mid provides R`, and BOTH provide `Base`, which declares `zug`
/// once. Two routes, one declaration: the walk's `visited` set probes `Base` once, so
/// `Mid.zug` answers. Reporting this as contested would refuse the shape `algebra.anthill`
/// records as the benign diamond — `Float` reaches `Additive` through both
/// `provides Numeric` and `provides Ring` — which the library is built on.
///
/// Driven to 42 rather than to "it loads", because "one answer" and "the right answer" are
/// different claims and only the number carries the second.
#[test]
fn a_diamond_over_one_declaration_is_one_answer() {
    let src = r#"
namespace test.x9rrn.diamond
  import anthill.prelude.{Int64}
  sort Base
    sort T = ?
    operation zug(x: T) -> T
  end
  sort L
    sort T = ?
    provides Base[T = T]
  end
  sort R
    sort T = ?
    provides Base[T = T]
  end
  sort Mid
    sort T = ?
    provides L[T = T]
    provides R[T = T]
  end
  sort Cell
    entity Cell(v: Int64)
    operation zug(x: Cell) -> Cell = Cell(v: x.v + 1)
  end
  fact Mid[T = Cell]
  operation drive() -> Int64 = Mid.zug(Cell(v: 41)).v
end
"#;
    assert_eq!(
        drive(src, "test.x9rrn.diamond.drive"),
        "Int(42)",
        "two provision routes to ONE declaration are one answer — the ambiguity arm must \
         discriminate on the DECLARATION, not on the number of routes"
    );
}

/// AN UNUSABLE PROVISION HIT MUST NOT RE-OPEN THE ABSOLUTE READING — the row this ticket
/// SHIPPED WRONG WITHOUT, found by `/code-review`.
///
/// The first cut let the provision hit fall out of its arm into the ladder's tail, where
/// WI-752's visibility fall-through re-reads the literal path text as a top-level qualified
/// name. A hit hidden by `internal` therefore reached `dotted_absolute`, and with an
/// unrelated top-level `namespace Mid` in the program the path bound THAT: measured, this
/// source loaded clean and `app.drive()` answered **999**, the foreign namespace's
/// operation, from a scope whose `Mid` is `lib.Mid` the sort.
///
/// WI-752's fall-through is right for what it was built for and wrong here, and the
/// distinction is the whole finding: it exists for the WI-751 COLLISION, where rung 1's
/// string join lands on a stranger BY COINCIDENCE, so "this reading did not bind the path"
/// is true. A conversion hit is deliberate — the author's `provides` put it there — so a
/// hit the citing scope may not see means the path is REFUSED, not that another reading
/// should be tried.
///
/// THREE ASSERTIONS, because two of them alone would pass on the defect:
///   * the load is refused, and the message is the precise `internal` one — which is what
///     says the refusal comes from visibility and not from the name being absent;
///   * `999` appears nowhere — the capture is what made this a silent wrong answer rather
///     than a missing diagnostic;
///   * THE CONTROL: the same program with the member PUBLIC loads and answers through the
///     conversion. Without it the row passes on a tree where the rung was never added.
#[test]
fn an_unusable_provision_hit_does_not_reopen_the_absolute_reading() {
    let program = |modifier: &str| {
        format!(
            r#"
namespace Mid
  import anthill.prelude.{{Int64}}
  operation zug(x: Int64) -> Int64 = 999
end
namespace lib
  import anthill.prelude.{{Int64}}
  sort Base
    sort T = ?
    {modifier}operation zug(x: T) -> T
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  sort Cell
    entity Cell(v: Int64)
    operation zug(x: Cell) -> Cell = Cell(v: x.v + 1)
  end
  fact Mid[T = Cell]
end
namespace app
  import anthill.prelude.{{Int64}}
  import lib.{{Mid, Cell}}
  operation drive() -> Int64 = Mid.zug(Cell(v: 41)).v
end
"#
        )
    };
    let errs = errs_of(&program("internal "));
    assert!(
        errs.iter()
            .any(|e| e.contains("is internal to 'lib.Base'") && e.contains("Mid.zug")),
        "a provision hit the citing scope may not see must be REFUSED as the forbidden \
         access it is; got {errs:?}"
    );
    assert!(
        !errs.is_empty() && errs.iter().all(|e| !e.contains("999")),
        "…and must never fall through to the ABSOLUTE reading, which bound the unrelated \
         top-level `Mid.zug` and answered 999; got {errs:?}"
    );

    // THE CONTROL: drop the `internal` and the very same path resolves and computes, so
    // the refusal above is about visibility rather than about the rung being absent.
    assert_eq!(
        drive(&program(""), "app.drive"),
        "Int(42)",
        "the same address with a VISIBLE member must reach the carrier through the \
         conversion — otherwise the refusal above measures nothing"
    );
}

/// AN UNREACHABLE ROUTE DOES NOT MAKE THE REACHABLE ONE AMBIGUOUS — the second row
/// `/code-review` earned, and the twin of
/// `two_provision_routes_are_ambiguous_in_either_source_order`.
///
/// `Mid provides L` and `provides R`, both declaring `b`, but `L.b` is `internal`. The
/// first cut collected raw `by_qualified_name` hits and gated only the WINNER, so the set
/// had two members and the ladder reported `ambiguous symbol 'Mid.b' … candidates
/// ["lib.L.b", "lib.R.b"]` — withholding the one answer the scope can actually bind, and
/// printing a name it may not see.
///
/// The gate now runs at COLLECTION, because the SIZE of the set is the verdict. The row
/// asserts the positive half (`R.b` is reached and computes) rather than merely "no
/// ambiguity": a rung that answered `NotFound` would also produce no ambiguity message.
#[test]
fn an_internal_route_does_not_contest_the_reachable_one() {
    let src = r#"
namespace lib3
  import anthill.prelude.{Int64}
  sort L
    sort T = ?
    internal operation b(x: T) -> T
  end
  sort R
    sort T = ?
    operation b(x: T) -> T
  end
  sort Mid
    sort T = ?
    provides L[T = T]
    provides R[T = T]
  end
  sort Cell
    entity Cell(v: Int64)
    operation b(x: Cell) -> Cell = Cell(v: x.v + 1)
  end
  fact Mid[T = Cell]
end
namespace app3
  import anthill.prelude.{Int64}
  import lib3.{Mid, Cell}
  operation drive() -> Int64 = Mid.b(Cell(v: 41)).v
end
"#;
    assert_eq!(
        drive(src, "app3.drive"),
        "Int(42)",
        "with one route `internal` and one visible, `Mid.b` has exactly ONE answer here \
         and must deliver it — the unreachable candidate must not be counted"
    );
}

/// THE QUALIFIED SPELLING'S POPULATION IS A SUBSET OF THE MEMBER IMPORT'S, AND THE
/// DIFFERENCE IS EXACTLY THE TWO EDGE KINDS THIS RUNG REFUSES.
///
/// The ticket is "the member IMPORT works and the call does not". The repair is not "make
/// the call work everywhere" — it is to give the address the CONVERSION edges, which is
/// where the two spellings had disagreed. They now agree on every conversion, because they
/// cross the same clauses: `process_imports` strategy 2 resolves the short name in the base
/// scope, which `wire_provides_scope_parent` gave a parent per `provides`, and this rung
/// walks those same clauses' edges.
///
/// THEY DO NOT AGREE EVERYWHERE, AND THAT IS DELIBERATE. Strategy 2 is a full
/// `resolve_in_scope`, so it ALSO crosses `requires` edges and re-enters the enclosing
/// chain. `import anthill.prelude.Numeric.{lt}` and `…{List}` both load — `lt` being
/// `PartialOrd`'s and `List` a SIBLING of `Numeric` — and neither is an address. This row
/// asserts the containment and then names both witnesses, so the gap is a stated shape
/// rather than a surprise; the import side of it is filed separately, since a
/// `Sort.{Sibling}` import is WI-751's over-hit rather than this rung's business.
///
/// AN EARLIER DRAFT ASSERTED EQUALITY AND WAS WRONG, which is why the containment is
/// spelled out rather than assumed: `Numeric.lt` answered `qualified=false, import=true`
/// and the row failed. Recorded because "the two spellings now agree" is the natural thing
/// to claim and it is false in one direction.
#[test]
fn the_qualified_population_is_contained_in_the_member_imports() {
    // `Sort.member` in a rule-body goal — a CHECKED position (WI-1034).
    let qualified_resolves = |path: &str| {
        let (head, member) = path.rsplit_once('.').expect("a dotted path");
        let short_head = head.rsplit('.').next().unwrap();
        let src = format!(
            r#"
namespace test.x9rrn.pop
  import anthill.prelude.{{Int64, Bool, Float}}
  import {head}
  rule g(?a, ?r) :- ?r = {short_head}.{member}(?a, ?a)
end
"#
        );
        !errs_of(&src)
            .iter()
            .any(|e| e.contains("names nothing") || e.contains("unknown functor"))
    };
    // The same member, imported by name.
    let import_resolves = |path: &str| {
        let (head, member) = path.rsplit_once('.').expect("a dotted path");
        let src = format!(
            r#"
namespace test.x9rrn.popimp
  import {head}.{{{member}}}
  sort S
    sort T = ?
  end
end
"#
        );
        !errs_of(&src)
            .iter()
            .any(|e| e.contains("unresolved import"))
    };

    // THE CONVERSIONS: both spellings resolve. Two negatives sit beside them so the
    // containment below is not satisfied by a rung that accepts everything.
    for (path, want) in [
        ("anthill.prelude.Numeric.add", true),
        ("anthill.prelude.Eq.eq", true),
        ("anthill.prelude.algebra.Ring.mul", true),
        // A CONCRETE `provides` binding (`TotalFloat provides PartialEq[T = TotalFloat]`)
        // is a claim about a value, not a conversion, so it wires no scope parent — and
        // the IMPORT refuses it too.
        ("anthill.prelude.TotalFloat.neq", false),
    ] {
        let (q, i) = (qualified_resolves(path), import_resolves(path));
        assert_eq!(
            q, want,
            "`{path}` should {} as an ADDRESS",
            if want { "resolve" } else { "name nothing" }
        );
        assert_eq!(
            q, i,
            "`{path}`: on a conversion the two spellings must answer the same question — \
             that is what this ticket repairs. qualified={q}, import={i}"
        );
    }

    // CONTAINMENT, and its two witnesses: the import is STRICTLY wider, by exactly the
    // edge kinds `dotted_by_provision` refuses.
    for (path, why) in [
        ("anthill.prelude.Numeric.lt", "`lt` is `PartialOrd`'s, reached by `requires`"),
        (
            "anthill.prelude.Numeric.List",
            "`List` is a SIBLING of `Numeric`, reached by the enclosing chain",
        ),
    ] {
        assert!(
            import_resolves(path),
            "{path}: the member import DOES reach it ({why}) — if this ever stops being \
             true, the containment below is measuring nothing"
        );
        assert!(
            !qualified_resolves(path),
            "{path}: …and the ADDRESS must not, because {why} and neither edge is an offer"
        );
    }
}

/// AN `internal` MEMBER IS STILL `internal` THROUGH THE CONVERSION.
///
/// The rung hands its hit back into the ladder's own visibility gate rather than
/// answering past it, so a provided member the citing scope may not see is reported as
/// the forbidden access it is — the same verdict the DECLARED spelling gets. Without this
/// the new rung would be a hole in WI-369 reachable from four lines of source.
///
/// The CAPTURE half of the same question — that such a hit must not fall through to the
/// absolute reading — is `an_unusable_provision_hit_does_not_reopen_the_absolute_reading`,
/// which is where the shipped defect was.
#[test]
fn an_internal_provided_member_is_refused_not_delivered() {
    let src = r#"
namespace test.x9rrn.hidden
  import anthill.prelude.{Int64}
  sort Base
    sort T = ?
    internal operation zug(x: T) -> T
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  rule g(?a, ?r) :- ?r = Mid.zug(?a)
end
"#;
    let errs = errs_of(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("zug") && e.contains("internal")),
        "an `internal` member reached by conversion must report the FORBIDDEN access, \
         not be delivered and not be reported as absent; got {errs:?}"
    );
}
