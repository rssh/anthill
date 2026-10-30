//! WI-20261003-EK43F — a variable an alias's definition writes by a name is a parameter
//! (kernel-language §8.1, *Type aliases*). In a member of a sort it is the sort's parameter of
//! that name: `sort Holder  sort P = Pair[?A, ?B]  …` is `sort A = ?`, `sort B = ?`, `sort P =
//! Pair[A, B]`, and `Holder[A = Int64, B = String]` binds them. Outside a sort it is a parameter
//! of the alias, given by name or by position: `PureFunction[A = Int64, B = Int64]` over `sort
//! PureFunction = Function[?A, ?B, {}]` is `Function[Int64, Int64, {}]`. Each row drives the
//! alias beside the spelling it stands for.
//!
//! The ticket's first half — an anonymous `?` in a member's binding (`sort P = Pair[?, ?]`)
//! leaving `P` uninhabitable — was closed before this ticket was taken up: ZY11J made an alias
//! written bare the type it stands for, and since KPBVX `Pair[?, ?]` is the bare `Pair`, fresh
//! at each use as a bare sort is. Its row is here as it was asked for.
//!
//! CONTROLS. Each part was backed out alone in one build, and the rows that then failed are
//! named at their site, with two of the earlier changes' readers:
//! - BARE: an alias written bare is its own name (ZY11J's reader, `alias_type_at_a_use`);
//! - OPEN: an alias's variables are the declaration's at every use (`open_slots_anew`);
//! - MEMBER: the parser leaves a member's named variable as written;
//! - PARAMS: an alias declares no parameter (`alias_parameters` answers none), so every
//!   reader takes an argument for the sort the alias stands for, as before;
//! - STRUCTURAL: an alias of a tuple or an arrow is not applied;
//! - one switch per reader of an applied alias: TYPE (a type position), BINDING (a clause
//!   binding's value), TERM (a bracket in a clause's term), BODY (a bracket in an operation
//!   body), QUERY (a bracket in a query), CONTRACT (an operation's `requires`), SPEC (a sort's
//!   `provides` and `requires`), GUARD (a rule's bounding guard).

use crate::common::{
    assert_refused_naming, load_errors_of, load_kb_with, parse_errs, query_unary, run_int64,
};

const PAIR: &str = "\
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(a: A, b: B)
  end
";

fn program(ns: &str, body: &str) -> String {
    format!(
        "namespace test.ek43f.{ns}\n  import anthill.prelude.{{Int64, String, Bool, List, Type, \
         Function, Error}}\n{PAIR}{body}\nend\n"
    )
}

fn run(ns: &str, body: &str) -> Result<i64, String> {
    run_int64(&program(ns, body), &format!("test.ek43f.{ns}.go"))
}

fn refused(ns: &str, body: &str, tokens: &[&str]) {
    let errs = load_errors_of(&program(ns, body));
    assert_refused_naming(&errs, tokens, &format!("{ns}: {body}"));
}

/// The ticket's first half: an anonymous `?` in a member's binding is a fresh slot, so `P` is
/// any pair, as a bare `Pair` is — a holder takes one and refuses what is no pair, and two
/// `P`-typed parameters of one operation take pairs of different element types. BARE: `P`
/// takes no pair. Passes with every back-out of this ticket, and with OPEN, by design.
#[test]
fn an_anonymous_slot_in_a_member_is_fresh() {
    let body = "  sort Holder
    sort P = Pair[?, ?]
    entity holder(p: P)
    operation two(x: P, y: P) -> Int64 = 3
  end
  operation take(h: Holder) -> Int64 = 4
  operation go() -> Int64 =
    take(holder(p: pair(a: 1, b: \"s\"))) + Holder.two(pair(a: 1, b: \"s\"), pair(a: \"t\", b: 2))";
    assert_eq!(run("anon", body), Ok(7));
    refused(
        "anonbad",
        "  sort Holder\n    sort P = Pair[?, ?]\n    entity holder(p: P)\n  end\n  operation go() -> Holder = holder(p: 5)",
        &["holder.p (entity-field): expected P (Pair), got Int64"],
    );
}

/// A named variable in a member's binding is the sort's parameter: `Holder[A = Int64, B =
/// String]` binds it, so a read through the field is an `Int64`, and a holder of a pair at the
/// other two types is refused for it — as under the parameters written out. MEMBER: the bracket
/// is refused, "declares no type parameters". BARE fails it too: `P` holds no pair.
#[test]
fn a_named_variable_in_a_member_is_the_sorts_parameter() {
    for (tag, holder) in [
        ("member", "  sort Holder\n    sort P = Pair[?A, ?B]\n    entity holder(p: P)\n  end\n"),
        (
            "written",
            "  sort Holder\n    sort A = ?\n    sort B = ?\n    sort P = Pair[A, B]\n    entity holder(p: P)\n  end\n",
        ),
    ] {
        let body = format!(
            "{holder}  operation first(h: Holder[A = Int64, B = String]) -> Int64 = h.p.a
  operation go() -> Int64 = first(holder(p: pair(a: 5, b: \"s\")))"
        );
        assert_eq!(run(tag, &body), Ok(5), "{tag}");
        refused(
            &format!("{tag}bad"),
            &format!(
                "{holder}  operation first(h: Holder[A = Int64, B = String]) -> Int64 = 0
  operation go() -> Int64 = first(holder(p: pair(a: \"x\", b: 1)))"
            ),
            &["expected Holder[A = Int64, B = String], got Holder[A = String, B = Int64]"],
        );
    }
}

/// The parameter is the sort's, so inside the sort every member writing `?A` writes the one
/// parameter: `swap(x: P) -> P` returns a pair at the same types, and one that swaps them is
/// refused. A variable a parameter is declared with is that parameter (`sort T = ?X`). MEMBER:
/// both loaded — `P` was fresh at each use — and the `T` row's `bad` was not refused. BARE fails
/// it too.
#[test]
fn every_member_writing_the_variable_writes_one_parameter() {
    refused(
        "tie",
        "  sort Holder\n    sort P = Pair[?A, ?B]\n    operation swap(x: P) -> P = pair(a: x.b, b: x.a)\n  end",
        &["swap.return (op-return): expected P"],
    );
    let declared = "  sort Holder
    sort T = ?X
    sort P = Pair[?X, ?X]
    entity holder(p: P, t: T)
  end
";
    assert_eq!(
        run("declared", &format!("{declared}  operation take(h: Holder[T = Int64]) -> Int64 = h.t\n  operation go() -> Int64 = take(holder(p: pair(a: 1, b: 2), t: 3))")),
        Ok(3)
    );
    refused(
        "declaredbad",
        &format!("{declared}  operation go() -> Holder = holder(p: pair(a: 1, b: 2), t: \"s\")"),
        &["holder.t (entity-field): expected Int64, got String"],
    );
}

/// A name the sort declares as anything but a parameter is refused where the variable is
/// written, as the file is parsed; `?_` names nothing a bracket can bind and declares no
/// parameter. MEMBER: each clash loaded, the variable a fresh slot.
#[test]
fn a_variable_naming_another_member_is_refused() {
    for (tag, member, kind) in [
        ("entity", "    entity A(x: Int64)\n", "an entity"),
        ("alias", "    sort A = Int64\n", "a type alias"),
        ("op", "    operation A() -> Int64 = 1\n", "an operation"),
        ("self", "", "a type alias"),
    ] {
        let (var, name) = if tag == "self" { ("?P", "P") } else { ("?A", "A") };
        let src = program(&format!("clash{tag}"), &format!("  sort Holder\n{member}    sort P = Pair[{var}, ?B]\n  end"));
        let errs = parse_errs(&src);
        assert_refused_naming(
            &errs,
            &[&format!("`{var}` in the definition of `P` writes the sort's parameter `{name}`, but the sort declares `{name}` as {kind}")],
            tag,
        );
    }
    refused(
        "underscore",
        "  sort Holder\n    sort P = Pair[?_, ?_]\n  end\n  operation go(h: Holder[Int64]) -> Int64 = 0",
        &["declares no type parameters"],
    );
}

const FUNCTIONS: &str = "\
  sort PureFunction = Function[?A, ?B, {}]
  operation inc(x: Int64) -> Int64 = x + 1
  operation boom(x: Int64) -> Int64 effects {Error} = x
";

/// Outside a sort the variable is the alias's own parameter, given by name or by position:
/// `PureFunction[A = Int64, B = Int64]` and `PureFunction[Int64, Int64]` admit `inc` and refuse
/// `boom` in the words `Function[Int64, Int64, {}]` refuses it. PARAMS and TYPE: the named
/// spelling is refused "already binds `A` to `?A`", the positional one "over-applied".
#[test]
fn a_pure_function_alias_takes_its_parameters() {
    for (tag, ty) in [
        ("named", "PureFunction[A = Int64, B = Int64]"),
        ("positional", "PureFunction[Int64, Int64]"),
        ("direct", "Function[Int64, Int64, {}]"),
    ] {
        let body = format!("{FUNCTIONS}  operation use(f: {ty}) -> Int64 = f(5)\n  operation go() -> Int64 = use(inc)");
        assert_eq!(run(&format!("pf{tag}"), &body), Ok(6), "{tag}");
        refused(
            &format!("pf{tag}bad"),
            &format!("{FUNCTIONS}  operation use(f: {ty}) -> Int64 = f(5)\n  operation go() -> Int64 = use(boom)"),
            &["declares `Error`, which the closed row does not admit"],
        );
    }
}

/// A parameter is known by its own name, wherever the definition writes it: `Sw[A = Int64, B =
/// String]` over `sort Sw = Pair[?B, ?A]` is `Pair[A = String, B = Int64]`, and positionally the
/// parameters are in the order they stand in `Pair`'s slots (`B` at `A`, then `A` at `B`), as
/// written out of order too (`Pair[B = ?Y, A = ?X]` is `X`, then `Y`). A variable
/// written twice is one parameter (`Q[X = Int64]`), and an alias that writes one slot leaves
/// the others to its sort (`U[X = Int64, B = String]`). Left out, a parameter is open at each
/// use, as `?` is. PARAMS and TYPE: every applied spelling is refused. OPEN: the two uses of the
/// bare `Q` share one variable, and `two` is refused; BARE fails it too.
#[test]
fn a_parameter_is_given_where_the_definition_writes_it() {
    let aliases = "  sort Sw = Pair[?B, ?A]\n  sort So = Pair[B = ?Y, A = ?X]\n  sort Q = Pair[?X, ?X]\n  sort U = Pair[A = ?X]\n";
    for (tag, sig, call, read, want) in [
        ("swnamed", "p: Sw[A = Int64, B = String]", "pair(a: \"s\", b: 7)", "p.b", 7),
        ("swpos", "p: Sw[String, Int64]", "pair(a: \"s\", b: 7)", "p.b", 7),
        ("sopos", "p: So[Int64, String]", "pair(a: 7, b: \"s\")", "p.a", 7),
        ("tie", "p: Q[X = Int64]", "pair(a: 3, b: 7)", "p.a + p.b", 10),
        ("partial", "p: U[X = Int64, B = String]", "pair(a: 10, b: \"s\")", "p.a", 10),
    ] {
        let body = format!("{aliases}  operation use({sig}) -> Int64 = {read}\n  operation go() -> Int64 = use({call})");
        assert_eq!(run(tag, &body), Ok(want), "{tag}");
    }
    refused(
        "swbad",
        &format!("{aliases}  operation use(p: Sw[A = Int64, B = String]) -> Int64 = 0\n  operation go() -> Int64 = use(pair(a: 7, b: \"s\"))"),
        &["use.p (op-arg): expected Pair[A = String, B = Int64], got Pair[A = Int64, B = String]"],
    );
    refused(
        "tiebad",
        &format!("{aliases}  operation use(p: Q[X = Int64]) -> Int64 = 0\n  operation go() -> Int64 = use(pair(a: 3, b: \"s\"))"),
        &["use.p (op-arg): expected Pair[A = Int64, B = Int64], got Pair[A = Int64, B = String]"],
    );
    let open = format!("{aliases}  operation two(x: Q, y: Q) -> Int64 = 1\n  operation go() -> Int64 = two(pair(a: 1, b: 1), pair(a: \"t\", b: \"u\"))");
    assert_eq!(run("open", &open), Ok(1));
}

/// An argument whose name is a parameter of the alias and a slot the definition leaves out
/// would bind two things, and is refused. PARAMS: `U[B = Int64]` loaded, binding `Pair`'s `B`.
#[test]
fn a_name_that_is_a_parameter_and_an_open_slot_is_refused() {
    refused(
        "ambiguous",
        "  sort U = Pair[A = List[?B]]\n  operation use(p: U[B = Int64]) -> Int64 = 0",
        &["`B` names the parameter `?B` of `test.ek43f.ambiguous.U` and the slot `B` of `test.ek43f.ambiguous.Pair` it leaves open"],
    );
}

/// An alias applied as a VALUE is the type its definition writes with the parameters given:
/// in a clause's data slot (a fact a query finds under the type written out) and in an
/// operation body (the type value a call answers), by name and by position. TERM, and BODY:
/// the relations of that position answer nothing; PARAMS fails it too.
#[test]
fn an_applied_alias_written_as_a_value_gives_its_parameters() {
    let src = program(
        "values",
        "  sort Sw = Pair[?B, ?A]
  sort Q = Pair[?X, ?X]
  operation idt(t: Type) -> Type = t
  fact holds(Sw[A = Int64, B = String])
  fact holdsQ(Q[X = Int64])
  fact written(Pair[A = String, B = Int64])
  fact writtenQ(Pair[A = Int64, B = Int64])
  rule same(?t) :- holds(?t), written(?t)
  rule sameQ(?t) :- holdsQ(?t), writtenQ(?t)
  operation viaSw() -> Type = idt(Sw[A = Int64, B = String])
  operation viaQ() -> Type = idt(Q[Int64])
  rule bodySw(?t) :- ?t <=> viaSw(), written(?t)
  rule bodyQ(?t) :- ?t <=> viaQ(), writtenQ(?t)",
    );
    let mut kb = load_kb_with(&src);
    for rel in ["same", "sameQ", "bodySw", "bodyQ"] {
        assert_eq!(query_unary(&mut kb, &format!("test.ek43f.values.{rel}")).len(), 1, "{rel}");
    }
}

/// In an operation body an argument is written where the parameter stands, as a bracket's
/// own binding is — a type, a generic operation's own type parameter, a tuple entry, a value
/// (`viaVal` loads as `Pair[B = c]` does; evaluating either is refused alike, "expected Type,
/// got Node"); where the parameter stands inside a tuple, only a type written out can be given
/// there, and a value is refused. A name given a parameter nested in a clause's term is read
/// in its type context, as `Pair[A = List[T = Red]]` reads `Red`. BODY: every relation here
/// answers nothing. Backed out alone, writing a value as a node refuses `viaVal`'s load, and
/// reading the argument in its type context leaves `isRed` without an answer.
#[test]
fn a_given_argument_is_read_as_the_brackets_own_binding() {
    let decls = "  sort Sw = Pair[?B, ?A]
  sort LT = List[T = (?A, Int64)]
  sort SL = Pair[A = List[?X]]
  entity Red
  operation idt(t: Type) -> Type = t
";
    let src = program(
        "given",
        &format!(
            "{decls}  fact writtenB(Pair[B = Int64])
  fact writtenTup(Pair[B = (Int64, String)])
  operation viaGen[T](x: T) -> Type requires anthill.reflect.TypeValue[T = T] = idt(Sw[A = T])
  operation callGen() -> Type = viaGen(5)
  operation viaTup() -> Type = idt(Sw[A = (Int64, String)])
  rule bodyGen(?t) :- ?t <=> callGen(), writtenB(?t)
  rule bodyTup(?t) :- ?t <=> viaTup(), writtenTup(?t)
  operation viaVal(c: Int64) -> Type = idt(Sw[A = c])
  operation dirVal(c: Int64) -> Type = idt(Pair[B = c])
  fact holdsRed(SL[X = Red])
  fact writtenRed(Pair[A = List[T = Red]])
  rule isRed(?t) :- holdsRed(?t), writtenRed(?t)"
        ),
    );
    let mut kb = load_kb_with(&src);
    for rel in ["bodyGen", "bodyTup", "isRed"] {
        assert_eq!(query_unary(&mut kb, &format!("test.ek43f.given.{rel}")).len(), 1, "{rel}");
    }
    refused(
        "giventuple",
        &format!("{decls}  operation go(c: Int64) -> Type = idt(LT[A = c])"),
        &["the parameter `?A` of `test.ek43f.giventuple.LT` stands inside a tuple, an arrow or a row"],
    );
}

/// A query's bracket reads the alias as a clause's does. QUERY, and PARAMS: no answer.
#[test]
fn a_query_gives_the_aliases_parameters() {
    let src = program(
        "query",
        "  sort Sw = Pair[?B, ?A]\n  fact written(Pair[A = String, B = Int64])",
    );
    let mut kb = load_kb_with(&src);
    for (q, n) in [
        ("test.ek43f.query.written(test.ek43f.query.Sw[A = anthill.prelude.Int64, B = anthill.prelude.String])", 1),
        ("test.ek43f.query.written(test.ek43f.query.Sw[anthill.prelude.String, anthill.prelude.Int64])", 1),
        ("test.ek43f.query.written(test.ek43f.query.Sw[anthill.prelude.Int64, anthill.prelude.String])", 0),
    ] {
        let goal = crate::common::query_pattern_term(&mut kb, q);
        let answers = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
        assert_eq!(answers.len(), n, "{q}");
    }
}

const TAG: &str = "\
  sort Tag
    sort T = ?
    sort Out = ?
    operation tg(x: T) -> Out
  end
  sort IntTag = Tag[T = ?X, Out = Int64]
";

/// A spec clause reads an alias's parameters as a type does: `provides IntTag[X = Self]` and
/// `provides IntTag[Self]` provide `Tag[T = Self, Out = Int64]`, an operation's `requires
/// IntTag[X = Box]` is `Tag` at `Box`, and one at `String` cannot be supplied. A clause binding
/// through one is the type it stands for (`provides Show[T = Sw[A = Int64, B = Self]]`). SPEC:
/// the two provisions are refused, the member taking less than the spec's `?X`; CONTRACT: the
/// `String` requirement loads, its `X` dropped; BINDING: the `Show` provision is refused.
/// PARAMS fails it too.
#[test]
fn a_spec_clause_gives_the_aliases_parameters() {
    for (tag, clause, want) in [("provnamed", "IntTag[X = Self]", 5), ("provpos", "IntTag[Self]", 5)] {
        let body = format!(
            "{TAG}  sort Box\n    entity box(n: Int64)\n    provides {clause}\n    operation tg(x: Self) -> Int64 = 5\n  end\n  operation go() -> Int64 = Tag.tg(Box.box(1))"
        );
        assert_eq!(run(tag, &body), Ok(want), "{tag}");
    }
    let requiring = |at: &str| {
        format!(
            "{TAG}  sort Box\n    entity box(n: Int64)\n    provides Tag[T = Self, Out = Int64]\n    operation tg(x: Self) -> Int64 = 7\n  end\n  operation use(b: Box) -> Int64 requires IntTag[X = {at}] = Tag.tg(b)\n  operation go() -> Int64 = use(Box.box(1))"
        )
    };
    assert_eq!(run("reqbox", &requiring("Box")), Ok(7));
    refused(
        "reqstring",
        &requiring("String"),
        &["requirement `test.ek43f.reqstring.Tag[T = anthill.prelude.String, Out = anthill.prelude.Int64]` cannot be supplied"],
    );
    let show = "  sort Sw = Pair[?B, ?A]
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort Box
    entity box(n: Int64)
    provides Show[T = Sw[A = Int64, B = Self]]
    operation show(x: Pair[A = Self, B = Int64]) -> Int64 = 9
  end
  operation go() -> Int64 = Show.show(pair(a: Box.box(1), b: 2))";
    assert_eq!(run("binding", show), Ok(9));
}

/// A rule's bounding guard gives an alias's parameter as a spec clause does, the carrier
/// included — the slot its parameter stands at alone, checked as a named carrier is, so one
/// that is no carrier of the spec is refused (`IO[A]`, `A` at `Out`) — and refuses a carrier
/// at a parameter written twice. GUARD, and PARAMS: `IT[A]` and `IT[X = A]` are refused, "declares no type
/// parameters".
#[test]
fn a_bounding_guard_gives_the_aliases_parameters() {
    let decls = "  sort Tagger
    sort C = ?
    sort Out = ?
    operation tag(x: C) -> Out
  end
  sort IT = Tagger[C = ?X, Out = Int64]
  sort IU = Tagger[C = ?X, Out = ?X]
  sort Ints
    provides Tagger[C = Int64, Out = Int64]
    operation tag(x: Int64) -> Int64 = x
  end
  fact item(1)
  fact item(\"s\")
";
    for (tag, guard) in [("direct", "Tagger[C = A, Out = Int64]"), ("pos", "IT[A]"), ("named", "IT[X = A]")] {
        let mut kb = load_kb_with(&program(&format!("g{tag}"), &format!("{decls}  rule ints[A](?x: A) :- item(?x), {guard}")));
        assert_eq!(query_unary(&mut kb, &format!("test.ek43f.g{tag}.ints")).len(), 1, "{tag}");
    }
    refused(
        "gout",
        &format!("{decls}  sort IO = Tagger[C = Int64, Out = ?X]\n  rule ints[A](?x: A) :- item(?x), IO[A]"),
        &["a sort that provides `test.ek43f.gout.Tagger` is its `C`, not its `Out`"],
    );
    refused(
        "gtied",
        &format!("{decls}  rule ints[A](?x: A) :- item(?x), IU[A]"),
        &["the carrier `A` gives the parameter `?X` of `test.ek43f.gtied.IU`, which does not stand alone at one parameter"],
    );
}

/// An alias of a tuple or an arrow takes its own parameters where a type is written — in a
/// signature and in a clause binding — and refuses an argument that gives none of them.
/// STRUCTURAL: every row is refused, "declares no type parameters". BARE fails it too.
#[test]
fn a_tuple_or_arrow_alias_takes_its_own_parameters() {
    let decls = "  sort Cb = (?A) -> ?A\n  sort Pr = (?A, ?B)\n  operation inc(x: Int64) -> Int64 = x + 1\n";
    let body = format!(
        "{decls}  operation use(f: Cb[A = Int64]) -> Int64 = f(4)\n  operation fst(p: Pr[Int64, String]) -> Int64 = 1\n  operation go() -> Int64 = use(inc) + fst((1, \"s\"))"
    );
    assert_eq!(run("structural", &body), Ok(6));
    refused(
        "structuralbad",
        &format!("{decls}  operation fst(p: Pr[Int64, String]) -> Int64 = 1\n  operation go() -> Int64 = fst((\"s\", 1))"),
        &["fst.p (op-arg): expected (_1: Int64, _2: String), got (_1: String, _2: Int64)"],
    );
    refused(
        "structuralextra",
        &format!("{decls}  operation use(f: Cb[A = Int64, Z = Int64]) -> Int64 = 0"),
        &["`test.ek43f.structuralextra.Cb` stands for", "which has no parameter for `Z`"],
    );
    refused(
        "structuraltwo",
        &format!("{decls}  sort Pr2 = (Pr[A = Int64], ?B)\n  operation use(p: Pr2[B = String]) -> Int64 = 0"),
        &["`B` names two variables of the definition of `test.ek43f.structuraltwo.Pr2`"],
    );
    let show = format!(
        "{decls}  sort Show\n    sort T = ?\n    operation show(x: T) -> Int64\n  end\n  sort P\n    provides Show[T = Pr[Int64, String]]\n    operation show(x: (Int64, String)) -> Int64 = 3\n  end\n  operation go() -> Int64 = Show.show((1, \"s\"))"
    );
    assert_eq!(run("structuralbinding", &show), Ok(3));
}

/// FOUND ON THE WAY: a type-position application binding again what its alias fixes was
/// refused in the words of a spec clause — "which a spec clause reads as the spec it stands
/// for" — where no spec clause is written. It says what the alias binds now. Fails against the
/// parent tree's message by construction; passes with every switch.
#[test]
fn a_rebinding_in_a_type_says_no_spec_clause() {
    let errs = load_errors_of(&program(
        "rebind",
        "  sort IP = Pair[A = Int64]\n  operation use(p: IP[A = Bool]) -> Int64 = 0",
    ));
    assert_refused_naming(
        &errs,
        &["'test.ek43f.rebind.IP' is a type alias that already binds `A` to `Int64`, which the application binds again"],
        "rebinding",
    );
    assert!(!errs.join(" ").contains("spec clause"), "{errs:#?}");
}
