//! WI-20261122-CXR5B — THE X READERS: what a refusal tells the author to write names the type-var
//! the value stands at, whichever is declared first (`docs/design/spec-carrier-set.md`, §4's X
//! row; `readers.md`).
//!
//! Over `Sp[A, B] { op(c: A, x: B); tag(x: B) }` with `P provides Sp[A = Self, B = Int64]`:
//!   * a `P` value where a `Sp` is expected was told "`Sp` is a spec over its parameter `B`…
//!     Type this position `Sp.B`" with `B` declared first — the single carrier parameter, where
//!     `P` stands at `A` (`provider_is_not_the_spec_note`, at an argument and at a field);
//!   * `Sp.tag(w)` with `w: Sp` was refused as the value typed at the spec it is with `B` first,
//!     and "missing `requires Sp[A = …]`" — a type-var `tag` takes no value of — with `A` first:
//!     the check asked only the single carrier parameter.
//! Now the note names the type-var a provision binds the provider at
//! (`param_a_provider_stands_at`), and a value typed at the spec is refused at every type-var the
//! operation takes a value of.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-23: see each row.

use crate::common::load_errors_of;

/// `Sp[A, B]` (with `B` first where `b_first`) and `P`, with `tail` beside them.
fn program(ns: &str, b_first: bool, tail: &str) -> String {
    let (x, y) = if b_first { ("B", "A") } else { ("A", "B") };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Sp
    sort {x} = ?
    sort {y} = ?
    operation op(c: A, x: B) -> Int64
    operation tag(x: B) -> Int64
  end
  sort P
    entity p
    provides Sp[A = Self, B = Int64]
    operation op(c: P, x: Int64) -> Int64 = 1
    operation tag(x: Int64) -> Int64 = 2
  end
{tail}
end
"#
    )
}

fn orders() -> [(&'static str, bool); 2] {
    [("afirst", false), ("bfirst", true)]
}

/// A provider's value where the spec is expected is told the type-var it stands at, `A`, in either
/// order — at an operation's argument and at an entity's field. FAILS backed out: with `B` first
/// both named `B`.
#[test]
fn a_providers_value_is_told_the_type_var_it_stands_at() {
    for (order, b_first) in orders() {
        for (shape, tail, repair) in [
            ("arg", "  operation use(x: Sp) -> Int64 = 1\n  operation go() -> Int64 = use(p)", "Sp.A`"),
            ("field", "  sort H\n    entity h(x: Sp)\n  end\n  operation go() -> Int64 =\n    let v = h(x: p)\n    1", "Sp[A = P]"),
        ] {
            let ns = format!("wicxr5bx.note.{shape}.{order}");
            let text = load_errors_of(&program(&ns, b_first, tail)).join("\n");
            assert!(text.contains("is a spec over its parameter `A`"), "`{ns}`:\n{text}");
            assert!(text.contains(repair), "`{ns}`: `{repair}` missing:\n{text}");
        }
    }
}

/// A value typed at the spec, passed where the operation takes a `B`, is refused as such in either
/// order, naming `B`. FAILS backed out: with `A` first it was "missing `requires Sp[A = …]`".
#[test]
fn a_value_typed_at_the_spec_is_refused_at_every_type_var_taken() {
    for (order, b_first) in orders() {
        let ns = format!("wicxr5bx.typed.{order}");
        let text = load_errors_of(&program(&ns, b_first, "  operation via(w: Sp) -> Int64 = Sp.tag(w)")).join("\n");
        assert!(text.contains("a value typed at it is not a value of a sort that provides it"), "`{ns}`:\n{text}");
        assert!(text.contains(&format!("Type the value `{ns}.Sp.B`")), "`{ns}`:\n{text}");
        assert!(!text.contains("missing `requires"), "`{ns}`:\n{text}");
    }
}

/// A witness binding `P` at `B`, filed before `P`'s own provision heading `A`, does not decide the
/// note: `P`'s own provision is asked first. FAILS with every provision of the spec asked in the
/// order filed (the first cut of this step; found by /code-review): the note named `B`.
#[test]
fn the_providers_own_provision_names_the_type_var_before_a_witness() {
    let ns = "wicxr5bx.ownfirst";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Sp
    sort A = ?
    sort B = ?
    operation op(c: A, x: B) -> Int64
    operation tag(x: B) -> Int64
  end
  sort W
    provides Sp[A = Int64, B = P]
    operation op(c: Int64, x: P) -> Int64 = 3
    operation tag(x: P) -> Int64 = 4
  end
  sort P
    entity p
    provides Sp[A = Self, B = Int64]
    operation op(c: P, x: Int64) -> Int64 = 1
    operation tag(x: Int64) -> Int64 = 2
  end
  operation use(x: Sp) -> Int64 = 1
  operation go() -> Int64 = use(p)
end
"#
    );
    let text = load_errors_of(&src).join("\n");
    assert!(text.contains("is a spec over its parameter `A`"), "`{ns}`:\n{text}");
}
