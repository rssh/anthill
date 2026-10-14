//! FAMILY (b) — A PROJECTED MEMBER AT A CALL: `k: r.M` is read from the spec the
//! receiver `r` is declared by (`kernel-language.md` §8.7, *A projected member is read
//! from the spec its receiver is declared by*) — who declares the receiver, how the
//! member is bound and by how many provisions, and what the call passes for it.
//!
//! The operation under the call returns its `k` by the same projection, and `go()` reads
//! the result by the shape the binding says: a call that types `r.M` as anything else
//! either refuses the argument or fails where the result is read. The call is the
//! subject, so it is not judged apart from `go()`.
//!
//! ONE PROGRAM, TWO SPELLINGS (P4): a binding and an alias of it; two provisions in
//! either order; a bare argument the call wraps in `some(…)` and the same one wrapped by
//! hand; a receiver written at the call and the same one held in a `let`.

use super::{opt, spelt, Exception, Family, Hole, Picks, Program};

pub static FAMILY: Family = Family {
    name: "b-projected-call",
    rule: "`k: r.M` at a call, by who declares the receiver `r` and how `M` is bound",
    holes: &[
        // Who declares the receiver: the spec's own operation (`s: Self`), a free
        // operation over the carrier (`c: Car`), a witness for the carrier (`c: C` at
        // `C = Car[…]`), a free operation over a field path (`h.item`).
        Hole {
            name: "declared",
            options: &[
                opt("spec", "s"),
                opt("carrier", "c"),
                opt("witness", "c"),
                opt("field", "h.item"),
            ],
        },
        // What `M` is bound to.
        Hole {
            name: "binds",
            options: &[
                spelt("int64", "Int64", "int64"),
                spelt("my-int", "MyInt", "int64"),
                spelt("list", "List[T = Int64]", "list"),
                spelt("my-list", "MyList", "list"),
                opt("v", "V"),
            ],
        },
        // A second provision binding an `M`: none; the same type, unaliased, written
        // before or after; another type, before or after.
        Hole {
            name: "second",
            options: &[
                opt("none", ""),
                spelt("agrees-before", "", "agrees"),
                spelt("agrees-after", "", "agrees"),
                spelt("differs-before", "String", "differs"),
                spelt("differs-after", "String", "differs"),
            ],
        },
        // The parameter and what the call passes: `k: r.M` given a value of it; `k:
        // Option[T = r.M]` given the bare value, or the value in `some(…)`; `k: r.M`
        // given a `String`.
        Hole {
            name: "argument",
            options: &[
                opt("plain", ""),
                spelt("wrapped", "", "option"),
                spelt("some", "", "option"),
                opt("wrong", ""),
            ],
        },
        Hole {
            name: "receiver",
            options: &[spelt("let", "c", "car"), spelt("inline", "car(v: 7)", "car")],
        },
    ],
    render,
    skips: None,
    judge: super::judge_program,
    exceptions: EXCEPTIONS,
};

const EXCEPTIONS: &[Exception] = &[];

fn render(picks: &Picks<'_>) -> Program {
    let binding = picks.text("binds");
    // The binding with no alias in it, and whether it is a list.
    let (unaliased, is_list) = match picks.label("binds") {
        "int64" | "my-int" => ("Int64", false),
        "list" | "my-list" => ("List[T = Int64]", true),
        "v" => ("V", false),
        other => panic!("no binds `{other}`"),
    };
    let second = match picks.label("second") {
        "none" => None,
        "agrees-before" | "agrees-after" => Some(unaliased),
        "differs-before" | "differs-after" => Some("String"),
        other => panic!("no second `{other}`"),
    };
    let second_first = picks.label("second").ends_with("-before");
    let optional = picks.is("argument", "wrapped") || picks.is("argument", "some");
    // `k`'s type over the receiver path `r`, and at the binding `b`.
    let projected = |r: &str| {
        if optional {
            format!("Option[T = {r}.M]")
        } else {
            format!("{r}.M")
        }
    };
    let at = |b: &str| {
        if optional {
            format!("Option[T = {b}]")
        } else {
            b.to_string()
        }
    };
    let in_order = |first: String, other: Option<String>| match other {
        None => first,
        Some(other) if second_first => format!("{other}{first}"),
        Some(other) => format!("{first}{other}"),
    };

    let witness = picks.is("declared", "witness");
    let on_spec = picks.is("declared", "spec");
    // `Car`'s own provisions: of `Sp`, and of `Other` where a second one is written —
    // none where a witness binds the member instead.
    let provisions = if witness {
        String::new()
    } else {
        in_order(
            format!("    provides Sp[M = {binding}]\n"),
            second.map(|b| format!("    provides Other[M = {b}]\n")),
        )
    };
    let spec_operation = if on_spec {
        format!("put(s: Self, k: {0}) -> {0}", projected("s"))
    } else {
        "size(s: Self) -> Int64".to_string()
    };
    let member = if on_spec {
        format!("put(c: Self, k: {0}) -> {0} = k", at(binding))
    } else {
        "size(c: Self) -> Int64 = 1".to_string()
    };
    let (declarations, call) = match picks.label("declared") {
        "spec" => (String::new(), "Sp.put"),
        "carrier" => (
            format!("  operation f(c: Car, k: {0}) -> {0} = k\n", projected("c")),
            "f",
        ),
        "field" => (
            format!(
                "  sort Has\n    entity has(item: Car[V = Int64])\n  end\n  operation g(h: Has, k: {0}) -> {0} = k\n",
                projected("h.item")
            ),
            "g",
        ),
        "witness" => {
            // A witness is generic in the carrier's parameter, which its binding names
            // as `E`.
            let holder = |name: &str, binding: &str| {
                let binding = if binding == "V" { "E" } else { binding };
                format!(
                    "  sort {name}\n    sort E = ?\n    provides Holder[C = Car[V = E], M = {binding}]\n    operation get(c: Car[V = E], k: {0}) -> {0} = k\n  end\n",
                    at(binding)
                )
            };
            (
                format!(
                    "  sort Holder\n    sort C = ?\n    sort M = ?\n    operation get(c: C, k: {0}) -> {0}\n  end\n{1}",
                    projected("c"),
                    in_order(holder("First", binding), second.map(|b| holder("Second", b))),
                ),
                "Holder.get",
            )
        }
        other => panic!("no declared `{other}`"),
    };

    let value = if is_list { "[41]" } else { "41" };
    let argument = match picks.label("argument") {
        "plain" | "wrapped" => value.to_string(),
        "some" => format!("some({value})"),
        "wrong" => "\"s\"".to_string(),
        other => panic!("no argument `{other}`"),
    };
    let receiver = picks.text("receiver");
    let receiver = if picks.is("declared", "field") {
        format!("has(item: {receiver})")
    } else {
        receiver.to_string()
    };
    let called = format!("{call}({receiver}, {argument})");
    let result = if optional {
        format!("opt({called})")
    } else if is_list {
        format!("len({called})")
    } else {
        called
    };
    let held = if picks.is("receiver", "let") {
        "    let c: Car[V = Int64] = car(v: 7)\n"
    } else {
        ""
    };
    Program {
        source: format!(
            r#"namespace family.b
  import anthill.prelude.{{Int64, String, List, Option}}
  import anthill.prelude.Option.{{some, none}}
  operation len[A](xs: List[T = A]) -> Int64 =
    match xs
      case cons(h, t) -> 1 + len(t)
      case nil -> 0
  operation opt[A](o: Option[T = A]) -> Int64 =
    match o
      case some(v) -> 1
      case none() -> 0
  sort MyInt = Int64
  sort MyList = List[T = Int64]
  sort Other
    sort M = ?
    operation other(o: Self) -> Int64
  end
  sort Sp
    sort M = ?
    operation {spec_operation}
  end
  sort Car
    sort V = ?
    entity car(v: V)
{provisions}    operation other(c: Self) -> Int64 = 0
    operation {member}
  end
{declarations}  operation go() -> Int64 =
{held}    {result}
end
"#
        ),
        entry: Some("family.b.go"),
        subject: None,
        refused: false,
    }
}
