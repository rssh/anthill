//! FAMILY (a) — THE DECLARATION RULE: a member must take every argument list its spec
//! takes (`kernel-language.md` §8.7), over a member whose parameter is typed by its own
//! sort at arguments naming that sort's parameter, and whose next parameter projects it.
//!
//! The template is the one WI-20260929-0RP29's ninth pass ran by script — a spec
//! `Sp[T, K, L, J]` with `op(t: T, x: K, y: L)`, and a carrier `Car[V]` providing it at
//! `T = Int64` whose member is `op(t: Int64, x: <x>, y: <y>)` — in today's spelling: the
//! carrier inside the carrier is `Self`, and its bare name is the sort at `?`. One hole
//! is added to it, `spec-x`: the spec's `x` left to the unwritten `K`, as there, or
//! written — the member's own type with `Car`'s parameter at `String` — which is where
//! the rule has two written types to compare.
//!
//! THE ENTRY POINT is built from a model of the types the holes write ([`Ty`]): the
//! member's body reads `x` by its shape, and `go()` passes the spec call a value of each
//! parameter. The model is not the typer's: where it has no value — a projection it does
//! not reduce — the program has no entry point, and where it is wrong the verdict says
//! `loads; drive refused`: the declarations are judged first, without `go()`.
//!
//! ── CONTROLS, MEASURED on this family through `scripts/families.sh a` (2026-10-13,
//! 6,160 programs; on the tree all of them hold) ────────────────────────────────
//!
//!  * THE ONCE-ONLY PARAMETER REPLACEMENT backed out (`typing/result.rs`
//!    `walk_pattern_field_type_deep` walking `PatternSubst::as_built` whatever the
//!    arguments hold — every parameter resolved to a fixpoint): 176 programs DIE of a
//!    stack overflow, each named, in 273 child processes where the tree takes 97, and
//!    the run goes on to judge the other 5,984 as the file has them. All 176 write
//!    `x: Car[V = List[T = V]]`, alone or under an `Option`.
//!  * THE DECLARING SORT'S PARAMETERS KEPT OUT OF A PROVISION'S OPEN SLOTS backed out
//!    (`typing/signature.rs` `declaring_own`): 1,596 verdicts differ from the file and
//!    none of them crosses between loading and refused — each is refused by another LEG
//!    (`tied@1` → `return`, `narrower@2` → `return`). The refusal's class is what shows
//!    it: by the `LoadError` variant alone, the same back-out moves no line of the file.
//!  * ONE LINE OF A VERDICT FILE EDITED BY HAND: the run fails with that program's name
//!    and both verdicts, and nothing else.
//!
//! THE CONTROLS ABOVE PREDATE THE LEFT-OUT PARAMETER'S `?` (WI-20261003-GR5EN's follow-up,
//! decided with the user): a spec parameter a `provides` clause leaves out is the `?` written
//! there, and every provision here leaves `K` and `L` out, so a member writing `x` or `y` at a
//! type of its own fixes the caller's slot and is refused there — 3,704 verdicts moved, each to
//! `narrower` at `x` or `y`, none from refused to running. Most programs now stop at that
//! refusal, before the rule the family was built for; the controls were not measured again.

use super::{opt, spelt, Exception, Family, Hole, Picks, Program};

pub static FAMILY: Family = Family {
    name: "a-declaration-rule",
    rule: "a member typed by its own sort at its own parameter, and a projection off it, behind a spec",
    holes: &[
        // The member's `x`.
        Hole {
            name: "x",
            options: &[
                opt("car-list-v", "Car[V = List[T = V]]"),
                spelt("car-car-v", "Car[V = Car[V = V]]", "car-self"),
                spelt("car-self", "Car[V = Self]", "car-self"),
                opt("car-car", "Car[V = Car]"),
                opt("list-self", "List[T = Self]"),
                opt("option-car-list-v", "Option[T = Car[V = List[T = V]]]"),
                opt("car-arrow", "Car[V = (a: V) -> V]"),
                spelt("car-v", "Car[V = V]", "self"),
                spelt("self", "Self", "self"),
                spelt("car", "Car", "any"),
                spelt("car-open", "Car[V = ?]", "any"),
            ],
        },
        // The member's `y`.
        Hole {
            name: "y",
            options: &[
                opt("x.J", "x.J"),
                opt("x.V", "x.V"),
                opt("x.v.T", "x.v.T"),
                opt("x.v.J", "x.v.J"),
                opt("x.v.V", "x.v.V"),
                opt("list-x.J", "List[T = x.J]"),
                opt("list-x.V", "List[T = x.V]"),
            ],
        },
        // What the MEMBER writes before `t`; [`spec_receiver`] is what the spec writes there.
        Hole {
            name: "receiver",
            options: &[
                opt("none", ""),
                opt("car-any", "c: Car, "),
                opt("car-self", "c: Self, "),
                opt("spec-self", "c: Self, "),
                opt("spec-spec", "s: Sp, "),
            ],
        },
        Hole {
            name: "provides",
            options: &[
                opt("j-v", "provides Sp[T = Int64, J = V]"),
                opt("j-lent", "provides Sp[T = Int64]\n    provides Sq[J = V]"),
                opt("j-both", "provides Sp[T = Int64, J = V]\n    provides Sq[J = V]"),
                opt("j-list-v", "provides Sp[T = Int64, J = List[T = V]]"),
            ],
        },
        // The spec's `x`: its unwritten `K`, or [`Ty::written_at_string`] of the member's.
        Hole {
            name: "spec-x",
            options: &[opt("k", "K"), opt("at-string", "the member's, `V` at `String`")],
        },
        // Both returns: `Int64`, or the member's `y` projection on both sides.
        Hole {
            name: "returns",
            options: &[opt("int64", "Int64"), opt("projection", "the `y` hole's text")],
        },
    ],
    render,
    skips: None,
    judge: super::judge_program,
    exceptions: EXCEPTIONS,
};

const EXCEPTIONS: &[Exception] = &[];

/// The types the holes write, as far as the entry point needs them.
#[derive(Clone, Debug, PartialEq)]
enum Ty {
    /// `Car`'s own parameter, inside `Car`.
    V,
    /// A slot left open: `?`, or a bare `Car`'s.
    Open,
    Int,
    Str,
    List(Box<Ty>),
    Option(Box<Ty>),
    Car(Box<Ty>),
    /// `(a: T) -> T`
    Arrow(Box<Ty>),
}

fn list(of: Ty) -> Ty {
    Ty::List(Box::new(of))
}

fn car(of: Ty) -> Ty {
    Ty::Car(Box::new(of))
}

impl Ty {
    /// The type with `V`, and every open slot, at `leaf` — what the entry point passes.
    fn at(&self, leaf: &Ty) -> Ty {
        let inner = |t: &Ty| Box::new(t.at(leaf));
        match self {
            Ty::V | Ty::Open => leaf.clone(),
            Ty::Int | Ty::Str => self.clone(),
            Ty::List(t) => Ty::List(inner(t)),
            Ty::Option(t) => Ty::Option(inner(t)),
            Ty::Car(t) => Ty::Car(inner(t)),
            Ty::Arrow(t) => Ty::Arrow(inner(t)),
        }
    }

    /// Written with `V` at `String` and an open slot still open: the spec's `x` under
    /// `spec-x=at-string`.
    fn written_at_string(&self) -> String {
        match self {
            Ty::Open => "?".to_string(),
            Ty::V => "String".to_string(),
            Ty::Int | Ty::Str => self.text(),
            Ty::List(t) => format!("List[T = {}]", t.written_at_string()),
            Ty::Option(t) => format!("Option[T = {}]", t.written_at_string()),
            Ty::Car(t) => format!("Car[V = {}]", t.written_at_string()),
            Ty::Arrow(t) => format!("(a: {0}) -> {0}", t.written_at_string()),
        }
    }

    /// Written, for a type holding neither `V` nor an open slot.
    fn text(&self) -> String {
        match self {
            Ty::V | Ty::Open => panic!("{self:?} is written only at a leaf"),
            Ty::Int => "Int64".to_string(),
            Ty::Str => "String".to_string(),
            Ty::List(t) => format!("List[T = {}]", t.text()),
            Ty::Option(t) => format!("Option[T = {}]", t.text()),
            Ty::Car(t) => format!("Car[V = {}]", t.text()),
            Ty::Arrow(t) => format!("(a: {0}) -> {0}", t.text()),
        }
    }

    /// A value of it.
    fn value(&self) -> String {
        match self {
            Ty::V | Ty::Open => panic!("{self:?} has a value only at a leaf"),
            Ty::Int => "7".to_string(),
            Ty::Str => "\"s\"".to_string(),
            Ty::List(t) => format!("[{}]", t.value()),
            Ty::Option(t) => format!("some({})", t.value()),
            Ty::Car(t) => format!("car(v: {})", t.value()),
            Ty::Arrow(t) => format!("lambda (a: {}) -> a", t.text()),
        }
    }

    /// An `Int64` expression that READS `expr` by this shape, so that a value of another
    /// shape fails where it is read: a field off an entity, a match over a list or an
    /// option. Under `V` and an open slot there is nothing to read but that it is there.
    fn read(&self, expr: &str) -> String {
        match self {
            Ty::Int => expr.to_string(),
            Ty::Str => format!("String.length({expr})"),
            Ty::List(_) => format!("len({expr})"),
            Ty::Option(_) => format!("opt({expr})"),
            Ty::Car(t) => t.read(&format!("{expr}.v")),
            Ty::V | Ty::Open | Ty::Arrow(_) => format!("one({expr})"),
        }
    }
}

/// The member's `x` as its option writes it.
fn x_type(label: &str) -> Ty {
    match label {
        "car-list-v" => car(list(Ty::V)),
        "car-car-v" | "car-self" => car(car(Ty::V)),
        "car-car" => car(car(Ty::Open)),
        "list-self" => list(car(Ty::V)),
        "option-car-list-v" => Ty::Option(Box::new(car(list(Ty::V)))),
        "car-arrow" => car(Ty::Arrow(Box::new(Ty::V))),
        "car-v" | "self" => car(Ty::V),
        "car" | "car-open" => car(Ty::Open),
        other => panic!("no x `{other}`"),
    }
}

/// What `y`'s projection reduces to over an `x` of type `x`, where the model reduces it:
/// `V` is a `Car`'s argument, `v` its field, `T` a `List`'s argument or the `Int64`
/// every provision here binds `Sp`'s `T` to, and `J` what the provision binds it to, at
/// the `Car` projected.
fn y_type(label: &str, x: &Ty, j_is_a_list: bool) -> Option<Ty> {
    let argument = |of: &Ty| match of {
        Ty::Car(a) => Some((**a).clone()),
        _ => None,
    };
    let j = |of: &Ty| argument(of).map(|a| if j_is_a_list { list(a) } else { a });
    match label {
        "x.J" => j(x),
        "x.V" => argument(x),
        "x.v.T" => match argument(x)? {
            Ty::List(t) => Some(*t),
            Ty::Car(_) => Some(Ty::Int),
            _ => None,
        },
        "x.v.J" => j(&argument(x)?),
        "x.v.V" => argument(&argument(x)?),
        "list-x.J" => j(x).map(list),
        "list-x.V" => argument(x).map(list),
        other => panic!("no y `{other}`"),
    }
}

/// What the spec writes where the member writes its receiver: nothing; the carrier by
/// name, which outside it is any `Car`; or the spec's own receiver.
fn spec_receiver(label: &str) -> &'static str {
    match label {
        "none" => "",
        "car-any" | "car-self" => "c: Car, ",
        "spec-self" | "spec-spec" => "s: Self, ",
        other => panic!("no receiver `{other}`"),
    }
}

fn render(picks: &Picks<'_>) -> Program {
    let spec_receiver = spec_receiver(picks.label("receiver"));
    let x = x_type(picks.label("x"));
    let j_is_a_list = picks.is("provides", "j-list-v");
    let y = y_type(picks.label("y"), &x, j_is_a_list);
    let lends = picks.text("provides").contains("Sq[");
    let at_string = picks.is("spec-x", "at-string");
    let (returns, body) = if picks.is("returns", "int64") {
        ("Int64", format!("t + {} + one(y)", x.read("x")))
    } else {
        (picks.text("y"), "y".to_string())
    };
    let declarations = format!(
        r#"  import anthill.prelude.{{Int64, String, List, Option}}
  operation len[A](xs: List[T = A]) -> Int64 =
    match xs
      case cons(h, t) -> 1 + len(t)
      case nil -> 0
  operation opt[A](o: Option[T = A]) -> Int64 =
    match o
      case some(v) -> 1
      case none() -> 0
  operation one[A](a: A) -> Int64 = 1
  sort Sp
    sort T = ?
    sort K = ?
    sort L = ?
    sort J = ?
    operation op({spec_receiver}t: T, x: {spec_x}, y: L) -> {returns}
  end
{lender}  sort Car
    sort V = ?
    entity car(v: V)
    {provides}
    operation op({member_receiver}t: Int64, x: {member_x}, y: {member_y}) -> {returns} = {body}
{lent_member}  end
"#,
        spec_x = if at_string {
            x.written_at_string()
        } else {
            "K".to_string()
        },
        lender = if lends {
            "  sort Sq\n    sort J = ?\n    operation oq(j: J) -> Int64\n  end\n"
        } else {
            ""
        },
        provides = picks.text("provides"),
        member_receiver = picks.text("receiver"),
        member_x = picks.text("x"),
        member_y = picks.text("y"),
        lent_member = if lends {
            "    operation oq(j: V) -> Int64 = 1\n"
        } else {
            ""
        },
    );
    let subject = format!("namespace family.a\n{declarations}end\n");
    let Some(y) = y else {
        return Program {
            source: subject,
            entry: None,
            subject: None,
            refused: false,
        };
    };
    // The instance the entry point drives: `V` where the spec's `x` says it, else `Int64`.
    let leaf = if at_string { Ty::Str } else { Ty::Int };
    let (x, y) = (x.at(&leaf), y.at(&leaf));
    let (receiver, receiver_argument) = if spec_receiver.is_empty() {
        (String::new(), "")
    } else {
        let c = car(leaf.clone());
        (format!("    let c: {} = {}\n", c.text(), c.value()), "c, ")
    };
    // A call the spec's own receiver does not dispatch names `J` itself: no argument
    // says it.
    let bracket = if spec_receiver.starts_with("s:") {
        String::new()
    } else if j_is_a_list {
        format!("[J = {}]", list(leaf).text())
    } else {
        format!("[J = {}]", leaf.text())
    };
    let call = format!("Sp.op{bracket}({receiver_argument}41, x, y)");
    let result = if picks.is("returns", "int64") {
        call
    } else {
        y.read(&format!("({call})"))
    };
    Program {
        source: format!(
            "namespace family.a\n{declarations}  operation go() -> Int64 =\n{receiver}    let x: {} = {}\n    let y: {} = {}\n    {result}\nend\n",
            x.text(),
            x.value(),
            y.text(),
            y.value(),
        ),
        entry: Some("family.a.go"),
        subject: Some(subject),
        refused: false,
    }
}
