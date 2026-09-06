//! WI-040 — the kernel DESUGARING VOCAB (reflect `Expr` / `Pattern` constructors,
//! `field_access`, the literal carriers `ListLiteral` / `SetLiteral` / `TupleLiteral`,
//! reflection primitives) resolves to its qualified home with no `<global>` import.
//!
//! WI-20260825-5W3RJ CHANGED HOW, AND THE POLARITY OF TWO ROWS WITH IT — recorded here
//! rather than quietly edited, because it is the measurement.
//!
//! WI-040's mechanism was a RESERVED SHORT NAME: the converter minted `field_access`,
//! and `KERNEL_VOCAB_QUALIFIED` — 28 stdlib addresses written into the resolver — was
//! consulted as the lowest rung of the name ladder when nothing else answered. That
//! encoded one fact twice (the mint site said which form, the table said where it
//! lived) and nothing kept the two agreeing. The converter now names its target
//! outright (`crate::parse::desugar_target`), so a synthesized node resolves through
//! the ordinary ABSOLUTE rung and the table is gone.
//!
//! THE CONSEQUENCE THIS FILE OWNS: a reserved name written BARE, BY HAND, in a query
//! pattern no longer resolves. It was reachable only through the rung that is gone, and
//! this file's two original rows were its ONLY customers in the whole workspace —
//! censused before the change over `anthill-cli`, `anthill-stl`, every `.anthill` source
//! and every Rust fixture; the two other textual hits are prose inside description
//! blocks in `stdlib/anthill/prelude/sort.anthill`. So the population that pays for the
//! deletion is exactly these rows, and what they pay is one `-i` flag.
//!
//! Backing WI-20260825-5W3RJ out inverts every row below: the first three would fail
//! (a bare name would resolve again), and `a_desugared_field_access_carries_its_address`
//! would fail because the minted node would carry the short spelling.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::parse::desugar_target as dt;

use crate::common::query_pattern_functor_qn;

fn load_stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib loads clean");
    kb
}

/// Every `field_access`-shaped functor a source text produces, by its PARSE-level name.
fn field_access_functor_names(src: &str) -> Vec<String> {
    let parsed = parse::parse(src).expect("parses");
    let mut out = Vec::new();
    for (_, term) in parsed.terms.iter() {
        if let Term::Fn { functor, .. } = term {
            let n = parsed.symbols.local_name(*functor);
            if n.ends_with("field_access") {
                out.push(n.to_owned());
            }
        }
    }
    out
}

/// A reflection primitive written BARE by hand in a query no longer resolves — it
/// bare-interns, which is what every other unimported name does. The reserved-name rung
/// that used to rescue it is gone.
///
/// THE ASSERTION IS THE OLD ONE INVERTED. Before WI-20260825-5W3RJ this asserted
/// `anthill.reflect.field_access`.
#[test]
fn query_pattern_bare_field_access_no_longer_resolves() {
    let mut kb = load_stdlib_kb();
    let qn = query_pattern_functor_qn(&mut kb, "field_access(object: ?o, field: ?f)");
    assert_eq!(
        qn, "field_access",
        "a bare reserved name in a query is now an ordinary unimported name; got {qn:?}"
    );
}

/// …and the reach is not LOST, only unspelled: the qualified name resolves through the
/// absolute rung, which is what a query author writes (or reaches with
/// `anthill query -i anthill.reflect.field_access`).
///
/// THIS IS THE ROW THAT MAKES THE ONE ABOVE ACCEPTABLE. Without it the pair would read
/// as a capability removed rather than a spelling required.
#[test]
fn query_pattern_qualified_field_access_resolves() {
    let mut kb = load_stdlib_kb();
    let query = format!(
        "{}(object: ?o, field: ?f)",
        dt::qualified(dt::FIELD_ACCESS)
    );
    let qn = query_pattern_functor_qn(
        &mut kb,
        &query,
    );
    assert_eq!(
        qn,
        dt::qualified(dt::FIELD_ACCESS),
        "the qualified spelling resolves by qualified name, with no tier involved; \
         got {qn:?}"
    );
}

/// The literal carrier, both ways, for the same reason as the pair above.
#[test]
fn query_pattern_list_literal_needs_its_address() {
    let mut kb = load_stdlib_kb();
    assert_eq!(
        query_pattern_functor_qn(&mut kb, "ListLiteral(?x)"),
        "ListLiteral",
        "bare: an ordinary unimported name"
    );
    assert_eq!(
        query_pattern_functor_qn(
            &mut kb,
            &format!("{}(?x)", dt::qualified(dt::LIST_LITERAL)),
        ),
        dt::qualified(dt::LIST_LITERAL),
        "qualified: resolves through the absolute rung"
    );
}

/// THE ROW THAT DRIVES THE NEW MECHANISM, and the reason the rows above can lose their
/// rung without losing coverage: a `p.x` written in an operation body is DESUGARED, and
/// the node the converter builds carries the reflect address itself. Nothing looks the
/// name up in a table, and no scope rung stands between the mint and its target.
///
/// FAILS IF a mint site goes back to a short spelling — `dt::FIELD_ACCESS` → the string
/// `"field_access"` in `convert.rs` — which is precisely the back-out.
#[test]
fn a_desugared_field_access_carries_its_address() {
    let names = field_access_functor_names(
        "namespace test.w5w3rj.desugar\n  \
         import anthill.prelude.{Int64}\n  \
         entity Point(x: Int64, y: Int64)\n  \
         operation getx(p: Point) -> Int64 = p.x\n\
         end\n",
    );
    assert_eq!(
        names,
        vec![anthill_core::parse::desugar_target::FIELD_ACCESS.to_owned()],
        "a desugared member access must name its reflect declaration outright, not \
         mint a bare name for a table to look up"
    );
}

/// EVERY ADDRESS THE CONVERTER OR THE INFIX DESUGAR MINTS, as one list — `dt::ALL`
/// chained with pratt's three functor tables.
///
/// EXTRACTED IN WI-910 so the two invariants over this domain cannot drift apart: the
/// orphan row below asks whether each address DENOTES something, and
/// `no_two_minted_addresses_share_a_short_name` asks whether any two of them collapse
/// onto one short spelling. Before the extraction the domain was built inline in one of
/// them, which is how a `.chain` gets added to one question and not the other.
///
/// REPEATS ARE DELIBERATE AND LOAD-BEARING. `EQ_FUNCTOR` arrives TWICE — from
/// `SPEC_OP_FUNCTORS` and again from `EQUALITY_FAMILY_FUNCTORS`, walked whole so a
/// FOURTH equality spelling joins by being added to the family list rather than by
/// someone noticing. The orphan row does not care. The distinctness row MUST dedupe by
/// ADDRESS before it compares short names, or it reports `eq` colliding with itself;
/// that is why `first_short_name_collision` keys on the address and not on a count.
///
/// `pratt::ARROW_FUNCTOR` / `ARROW_EFFECT_FUNCTOR` are OUT OF DOMAIN and not an
/// oversight: they carry no `..` marker, so they are not addresses at all, and
/// `dt::qualified` panics rather than answering on them.
fn every_minted_address() -> Vec<&'static str> {
    dt::ALL
        .iter()
        .copied()
        .chain(anthill_core::parse::pratt::SPEC_OP_FUNCTORS.iter().copied())
        // WI-20260825-P9Y67: the boolean connectives carry addresses too, at
        // `anthill.kernel` rather than a prelude spec. Same claim, same row — an
        // address that denotes nothing is the failure the orphan test exists to name.
        .chain(
            anthill_core::parse::pratt::CONNECTIVE_FUNCTORS
                .iter()
                .copied(),
        )
        // WI-909: `unify` / `struct_eq` carry kernel addresses too.
        .chain(
            anthill_core::parse::pratt::EQUALITY_FAMILY_FUNCTORS
                .iter()
                .copied(),
        )
        .collect()
}

/// The first pair of DISTINCT addresses in `targets` sharing a short name, or `None`.
///
/// KEYED ON THE ADDRESS, so the same address arriving twice — which `EQ_FUNCTOR` does
/// by construction — is not a collision. Returns both members, which is what WI-910's
/// acceptance asks a report to name.
fn first_short_name_collision<'a>(targets: &[&'a str]) -> Option<(&'a str, &'a str)> {
    let mut seen: Vec<(&'a str, &'a str)> = Vec::new();
    for &target in targets {
        let short = dt::short(target);
        match seen.iter().find(|(s, _)| *s == short) {
            Some(&(_, prev)) if prev != target => return Some((prev, target)),
            Some(_) => {}
            None => seen.push((short, target)),
        }
    }
    None
}

/// NO TWO DISTINCT ADDRESSES SHARE A SHORT NAME — WI-910's invariant, re-homed onto the
/// tables that replaced the two it was filed against.
///
/// WI-910 asked this of `kb::load`'s implicit tier, where resolution WAS a linear `find`
/// by last dot-segment over 61 entries: a duplicate short name made the second entry
/// unreachable by every consumer, silently. Both tables it named are gone —
/// `KERNEL_VOCAB_QUALIFIED` with WI-20260825-5W3RJ, `PRELUDE_QUALIFIED` with WI-909 —
/// and the fallback RUNG that consulted them with it.
///
/// WHAT DID NOT GO IS SHORT-NAME LOOKUP ITSELF, and saying otherwise is the error this
/// row is written against. Ordinary scope resolution still resolves a short name against
/// a scope's locals, and `register_stdlib_scopes` still DEFINES nine of these addresses
/// under `dt::short(X)`. So the currency WI-910 was about is still live; only the
/// lowest-precedence table lookup is gone. Readers that key on a last segment today:
///   * `dt::is`'s third arm (`name == short(target)`) — a collision makes one written
///     name answer `true` for two targets.
///   * `kb::node_occurrence::expr_form_key`, the dispatch key of the hand-written
///     `match` arms in `visit_fn` / `is_reflect_form_functor`. It covers EIGHT of
///     `dt::ALL`, not all twelve — `field_access`, `ho_apply`, `cut` and
///     `find_dictionary` have no arm.
///   * `kb::load::register_stdlib_scopes`.
///   * `kb::resolve`'s `ho_apply` gate (`local_name_of(f) == dt::short(dt::HO_APPLY)`)
///     and `Some("ListLiteral")` in `bounded_list_elements`.
///   * `kb::load`'s `ho_apply` intern fallback and `type_expr_base_name`, which names a
///     `TypeExpr::Tuple` by `dt::short(dt::TUPLE_LITERAL)`.
///   * `kb::node_occurrence`'s `debug_assert!(!dot_chain || key == "field_access", …)`,
///     whose own comment says the safety is one name collision away.
///
/// WHAT THIS ROW DOES NOT COVER, said plainly so the census is not read as complete.
/// The dispatch KEY SPACE is wider than this domain: `visit_fn` matches roughly twenty
/// strings, and `register_stdlib_scopes` hand-writes `apply` / `constructor` / `var_ref`
/// / the `*_lit` family into the same scopes the `dt::short` defines land in. A
/// collision between a minted address and one of THOSE is the same hazard and is not
/// measured here. `expr_form_key` is namespace-blind, so `is_reflect_form_functor`
/// already answers `true` for `anthill.reflect.Substitution.apply` and
/// `anthill.prelude.Function.apply` — a live, pre-existing defect, older than this
/// ticket and not repaired by it.
///
/// THE SAME-SCOPE HALF IS ALREADY LOUD, which is why this row is about the rest.
/// `SymbolTable::define` MERGES on a name already bound in the scope — it calls
/// `add_kind` and early-returns — so a collision inside one scope leaves the SECOND
/// address unregistered in `by_qualified_name`, and
/// `every_desugar_target_is_declared_by_the_standard_load` above reports it as a named
/// orphan. It is a collision ACROSS scopes, or one in a reader that never touches the
/// symbol table, that says nothing.
///
/// IT PASSES TODAY AND IS A ROT GUARD. `node_occurrence`'s
/// `the_hand_written_dispatch_arms_still_key_off_their_addresses` already pins eight of
/// these pairwise-distinct by driving `expr_form_key`; what is new here is the other
/// twenty-two addresses and every cross-product, including the cross-table pairs
/// WI-910's acceptance names ("within a list, or ACROSS the two").
#[test]
fn no_two_minted_addresses_share_a_short_name() {
    let domain = every_minted_address();

    // A LOWER BOUND ON WHAT WAS SWEPT, derived rather than pinned to a magic number: an
    // empty or shrunken domain returns the same `None` as a clean sweep, which is the
    // silent-shrinkage failure this file's own orphan row was rewritten to avoid. A
    // dropped `.chain` reds here.
    assert_eq!(
        domain.len(),
        dt::ALL.len()
            + anthill_core::parse::pratt::SPEC_OP_FUNCTORS.len()
            + anthill_core::parse::pratt::CONNECTIVE_FUNCTORS.len()
            + anthill_core::parse::pratt::EQUALITY_FAMILY_FUNCTORS.len(),
        "`every_minted_address` lost a table; the sweep below would still report None"
    );

    assert_eq!(
        first_short_name_collision(&domain),
        None,
        "two distinct minted addresses share a short name. Which readers break depends \
         on which pair: see this row's doc for the census — `dt::is`, `expr_form_key`'s \
         eight arms, `register_stdlib_scopes`, the `ho_apply` gate. A pair reachable by \
         none of them is still a defect: the short spelling no longer identifies one \
         address"
    );
}

/// THE DETECTOR, DRIVEN OVER A COLLISION — a separate `#[test]` on purpose.
///
/// `assert_eq!` panics, so folding this into the row above would make the control
/// unreachable at exactly the moment anyone reads it: a real collision reds the first
/// assertion and the detector's own evidence never runs. Separate functions also mean a
/// broken detector is reported under a name that says so, instead of under a name
/// asserting the opposite.
///
/// FOUR ELEMENTS, COLLIDING AT 1 AND 3, and the shape is the measurement: a two-element
/// probe cannot tell "finds the earlier colliding member" from "returns `targets[0]`",
/// and an adjacent pair cannot tell a full scan from one comparing only its neighbour.
/// Each of those mutations passes a two-element probe while missing a real collision
/// between the ends of `dt::ALL`.
///
/// THE SECOND ROW IS THE `EQ_FUNCTOR` CASE, which is not hypothetical: that address is
/// in the domain twice, so a detector keyed on the short name alone would fail
/// `no_two_minted_addresses_share_a_short_name` on a perfectly healthy tree.
#[test]
fn the_short_name_collision_detector_finds_what_it_is_given() {
    // Synthetic — same last segment as `MATCH_EXPR`, different namespace. Nothing
    // declares it; it never reaches a load.
    //
    // DERIVED FROM THE CONSTANT, NOT SPELLED OUT. A hardcoded `…Pattern.match_expr`
    // stops colliding the moment `MATCH_EXPR` is renamed, and this row would then fail
    // saying the DETECTOR cannot name both members — sending the reader after a helper
    // nobody touched when all that moved was an address. Raised by `/code-review`.
    let pattern_twin = format!("..anthill.reflect.Pattern.{}", dt::short(dt::MATCH_EXPR));
    let probe = [
        anthill_core::parse::pratt::ADD_FUNCTOR,
        dt::MATCH_EXPR,
        dt::CUT,
        pattern_twin.as_str(),
    ];
    assert_eq!(
        first_short_name_collision(&probe),
        Some((dt::MATCH_EXPR, pattern_twin.as_str())),
        "the detector must find a non-adjacent collision and name BOTH members"
    );

    assert_eq!(
        first_short_name_collision(&[dt::MATCH_EXPR, dt::MATCH_EXPR]),
        None,
        "one ADDRESS repeated is not a collision — `EQ_FUNCTOR` reaches the real \
         domain twice by construction"
    );
}

/// EVERY DESUGAR TARGET IS DECLARED AFTER A STANDARD LOAD — the invariant the deleted
/// `implicit_target_orphans` half used to cover, restored as a row over the constants
/// the converter actually mints.
///
/// IT IS NOT REDUNDANT WITH THE ROWS BELOW, and the reason is the split registration:
/// `register_stdlib_scopes` pre-defines the literal carriers and the `Expr` entities in
/// Rust, but NOT `anthill.reflect.field_access`, which exists only because
/// `stdlib/anthill/reflect/reflect.anthill` declares it. So those addresses are kept
/// in step by two different mechanisms, and a rename in either now surfaces as an
/// unrelated downstream typing error rather than a named orphan report. This row is
/// what names it.
///
/// RESOLVABILITY ALONE IS VACUOUS FOR BUILTIN-TAGGED NAMES: `register_builtin_tag`
/// inserts a missing qualified name into the same map `try_resolve_symbol` reads. The
/// second assertion therefore checks the ten reflect targets against the defining
/// scan's DECLARATION ledger. A bootstrap definition or builtin tag cannot satisfy it.
/// Rename `ListLiteral` (or `field_access`) in `reflect.anthill` without updating the
/// canonical address and this row now fails naming that address; before S66VH it loaded
/// clean because `register_stdlib_scopes` / `register_builtin_tags` masked the orphan.
///
/// The two kernel controls deliberately stay outside that declaration assertion:
/// `find_dictionary` has no source declaration at all, while `cut` does. Making their
/// existence policy uniform is not part of the reflect-address sweep.
///
/// WI-909'S TWO ARE IN THE FIRST WALK AND VACUOUS IN IT, said here rather than left for
/// a reader to discover: `anthill.kernel.unify` and `.struct_eq` are BUILTIN-TAGGED
/// (`register_builtin_tag(…, BuiltinTag::Unify / ::Eq)`), and `register_builtin_tag`
/// DEFINES a missing qualified name rather than skipping it — so deleting
/// `operation unify[T]` from `kernel.anthill` leaves the symbol minted and this row
/// green. That is `cut`'s situation exactly. They are walked anyway because the walk is
/// over a LIST, and a fourth equality spelling added to `EQUALITY_FAMILY_FUNCTORS`
/// might not be builtin-tagged; what actually covers these two is every `<=>` and `===`
/// in the stdlib, which stop resolving at their use sites.
///
/// FAILS IF a constant is edited without its declaration, in either place. Raised by
/// `/code-review`, which caught the module doc claiming "nothing has to be kept in
/// step" — true of the mint-vs-table duplication that was deleted, false of this.
#[test]
fn every_desugar_target_is_declared_by_the_standard_load() {
    let kb = load_stdlib_kb();
    // WALKS `dt::ALL` rather than a hand-copied mirror (raised by `/code-review`): a
    // constant added to the module without a row here was simply never checked for
    // being an orphan, which is the failure this test is named after.
    //
    // WI-20260825-KD9SW — THE TWELVE SPEC-OP ADDRESSES WALK HERE TOO. A minted operator
    // names its target outright now, so `..anthill.prelude.Additive.add` has exactly the
    // property this test exists for: a rename in the library surfaces at every USE site
    // as "unknown functor" and never as a named orphan. `NEG_FUNCTOR` has no other
    // coverage at all — a prefix `-` on a non-literal does not parse (WI-529), so no
    // program can drive it and this row is the only thing that would catch a wrong
    // address. (The pratt-side doc once claimed this test covered them while it walked
    // `desugar_target`'s ten by hand; it walks `dt::ALL` now, so that is fixed rather
    // than merely reported.)
    let targets = every_minted_address();
    let orphans: Vec<&str> = targets
        .iter()
        .copied()
        .filter(|t| {
            let qualified = anthill_core::intern::absolute_path_target(t).unwrap_or(t);
            kb.try_resolve_symbol(qualified).is_none()
        })
        .collect();
    assert!(
        orphans.is_empty(),
        "these desugar targets resolve to nothing after a standard load, so every \
         program using the surface form they lower would fail at its USE site with a \
         diagnostic that names neither the form nor this list: {orphans:?}"
    );

    // S66VH CONTROL: this is the assertion that inverts under the requested rename.
    // `register_stdlib_scopes` defines nine of these names and builtin-tag bootstrap
    // defines the tenth, so symbol-table existence cannot distinguish a declaration
    // from a stale Rust-side address. `declared_symbols_of_last_scan` can: it is the
    // pass-1 ledger of what the `.anthill` sources actually declared.
    let declared: std::collections::HashSet<_> =
        kb.declared_symbols_of_last_scan().into_iter().collect();
    // The exclusion is the PARTITION (`dt::is_kernel_control`), not a namespace-prefix
    // test on the address. `/code-review` caught the prefix version: it is true today
    // and silently drops any reflect target that ever moves namespace, leaving the row
    // reading as though it still covered it.
    let undeclared_reflect_targets: Vec<&str> = dt::ALL
        .iter()
        .copied()
        .filter(|target| !dt::is_kernel_control(target))
        .filter(|target| {
            kb.try_resolve_symbol(dt::qualified(target))
                .map_or(true, |sym| !declared.contains(&sym))
        })
        .collect();
    assert!(
        undeclared_reflect_targets.is_empty(),
        "these reflect desugar target addresses have no declaration in the standard \
         sources; bootstrap registration only masks the stale address: \
         {undeclared_reflect_targets:?}"
    );
}

/// THE HEAD SEGMENT IS A SCOPE RUNG, AND THE `..` MARKER IS WHAT TAKES IT OUT OF PLAY.
/// A desugar target is written `..anthill.reflect.…`: an UNMARKED `anthill.reflect.X`
/// takes the relative, head-qualified reading (WI-1075), so `resolve_in_scope("anthill",
/// scope)` runs first and any scope where `anthill` denotes something else captures every
/// desugaring in it.
///
/// MEASURED BOTH WAYS on the unmarked version, which is the back-out: a sibling
/// `namespace myapp.anthill` beside the using namespace turned `(a: 1, b: 2)`, `{1, 2}`
/// and `?P(?x)` into "unknown functor" / "names nothing" (3 errors), while renaming that
/// sibling to `myapp.anthillX` loaded clean — 2675 facts either way once marked. A
/// file-local `sort anthill` does it too, which is this row's second arm. Found by
/// `/code-review`; the first cut of this ticket shipped the unmarked spelling AND a spec
/// paragraph asserting a desugaring could not be captured.
///
/// THE BREAKAGE IS PARTIAL, which is why the row drives tuples / sets / lists / `?P(?x)`
/// rather than `if` or `p.x`: those four go through loader arms that are SHAPE-gated and
/// never resolve the functor at all, so they survive an unmarked spelling and would make
/// this row pass while the defect stood.
#[test]
fn a_scope_named_anthill_does_not_capture_a_desugaring() {
    for shadow in [
        "namespace myapp.cap.sibling\n  import anthill.prelude.{Int64}\n  \
         entity Marker(n: Int64)\nend\n",
        "",
    ] {
        let local = if shadow.is_empty() {
            "  sort anthill\n    entity Thing(n: Int64)\n  end\n"
        } else {
            ""
        };
        let src = format!(
            "{shadow}namespace myapp.cap.user\n  \
             import anthill.prelude.{{Int64, Set}}\n{local}  \
             operation tup() -> (a: Int64, b: Int64) = (a: 1, b: 2)\n  \
             operation st() -> Set[T = Int64] = {{1, 2}}\n  \
             rule call(?P, ?x) :- ?P(?x)\n\
             end\n"
        );
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_default();
        assert!(
            errs.is_empty(),
            "a scope named `anthill` must not reach the desugar targets — they are \
             written with the absolute marker precisely so their head segment is not \
             resolved in scope. errors: {errs:#?}"
        );
    }
}

/// A USER-WRITTEN `field_access(...)` still carries the SHORT spelling, which is why
/// the loader's shape questions ask `desugar_target::is` rather than comparing to the
/// address. The two spellings are the same shape and different provenance.
///
/// PASSES BOTH WITH AND WITHOUT the change, by design — it pins the property that made
/// `dt::is` necessary. FAILS if the converter ever starts rewriting a hand-written call
/// to the address, which would silently give it the converter's provenance.
#[test]
fn a_written_field_access_keeps_the_short_spelling() {
    let names = field_access_functor_names(
        "namespace test.w5w3rj.written\n  \
         import anthill.prelude.{Int64}\n  \
         rule r(?o, ?f) :- field_access(?o, ?f)\n\
         end\n",
    );
    assert_eq!(
        names,
        vec!["field_access".to_owned()],
        "a hand-written call is not a desugar; it keeps the name the author typed"
    );
}
