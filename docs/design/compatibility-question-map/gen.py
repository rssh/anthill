#!/usr/bin/env python3
"""The compatibility question as a matrix: may a value of type A stand where B is expected?
One program per (pair, position). The value always comes from `mkA() -> A`, so its static
type is A and no constructor is classified at the expectation (kernel-language §8.2).
    python3 gen.py <out_dir>
"""
import os, sys

OUT = sys.argv[1]
os.makedirs(OUT, exist_ok=True)

# (name, A, a literal of type A, B, what the spec says: yes / no / ?)
PAIRS = [
    ("variant-to-sort", "Colour.red", "red(v: 1)", "Colour", "yes"),          # §8.2
    ("sort-to-variant", "Colour", "red(v: 1)", "Colour.red", "no"),           # §8.2
    ("sibling-variant", "Colour.blue", "blue(v: 2)", "Colour.red", "no"),     # §8.2
    ("self-carrier", "List[T = Int64]", "[1, 2]", "Stream[T = Int64, E = {}]", "yes"),  # §8.2 provider admissibility
    ("param-spec", "Bk", "bk(k: 0)", "Tagger", "no"),                         # §8.2 `direct(b(k: 0))` refused
    ("refinement", "Narrow", "narrow()", "Wide[W = Int64]", "yes"),            # 071: each instance its clauses give it
    ("refinement-other-args", "Narrow", "narrow()", "Wide[W = String]", "no"),
    ("open-slot", "Box[V = Int64]", "box(v: 1)", "Box", "yes"),               # a slot left out is open
    ("slot-mismatch", "Box[V = Int64]", "box(v: 1)", "Box[V = String]", "no"),
    ("alias", "Option[T = Int64]", "Option.some(1)", "IntOpt", "yes"),        # an alias is its expansion
    ("alias-reverse", "IntOpt", "Option.some(1)", "Option[T = Int64]", "yes"),
    ("tuple-width", "(a: Int64, b: String, c: Bool)", '(a: 1, b: "s", c: true)', "(a: Int64, c: Bool)", "yes"),  # §4.5
    ("tuple-permutation", "(b: String, a: Int64)", '(b: "s", a: 1)', "(a: Int64, b: String)", "yes"),        # §4.5
    ("tuple-order", "(String, Int64)", '("s", 1)', "(Int64, String)", "no"),                                   # §4.5
    ("covariant-list", "List[T = Colour.red]", "[red(v: 1)]", "List[T = Colour]", "yes"),  # Covariant(List, T)
    ("no-variance-fact", "Box[V = Colour.red]", "box(v: red(v: 1))", "Box[V = Colour]", "?"),
    ("arrow-parameter-wider", "(Colour) -> Int64", "lambda (x: Colour) -> 1", "(Colour.red) -> Int64", "yes"),
    ("arrow-parameter-narrower", "(Colour.red) -> Int64", "lambda (x: Colour.red) -> 1", "(Colour) -> Int64", "no"),
    ("arrow-fewer-effects", "(Int64) -> Int64", "lambda (x: Int64) -> x", "(Int64) -> Int64 @ {Error[String]}", "yes"),
    ("arrow-more-effects", "(Int64) -> Int64 @ {Error[String]}", "lambda (x: Int64) -> x", "(Int64) -> Int64", "no"),
]
NAMED = {"refinement", "refinement-other-args", "variant-to-sort", "sort-to-variant", "sibling-variant", "self-carrier", "param-spec", "open-slot",
         "slot-mismatch", "alias", "alias-reverse", "covariant-list", "no-variance-fact"}

# (name, declarations, go's body) — `{B}` is the expected type.
POSITIONS = [
    ("argument", "  operation take(x: {B}) -> Int64 = 1\n", "take(mkA())"),
    ("let", "", "let y: {B} = mkA()\n    1"),
    ("return", "  operation conv() -> {B} = mkA()\n", "let _ = conv()\n    1"),
    ("field", "  sort H\n    entity h(x: {B})\n  end\n", "let _ = h(x: mkA())\n    1"),
    ("list-element", "", "let ys: List[T = {B}] = [mkA()]\n    1"),
    ("lambda-argument", "", "let f = lambda (x: {B}) -> 1\n    f(mkA())"),
    ("provision", "  sort W\n    provides Desc[T = {B}]\n    operation d(x: {B}) -> Int64 = 5\n  end\n", "Desc.d(mkA())"),
    ("type-admits", "", "if type_admits({B}, {A}) then 1 else 0"),
]

HEAD = """namespace probe.{ns}
  import anthill.cli.Main
  import anthill.prelude.Console.{{console, println, ConsoleOutput}}
  import anthill.prelude.Int64.{{to_string}}
  import anthill.prelude.{{List, String, Bool, Option, Stream, Error}}
  import anthill.reflect.{{type_admits}}

  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort IntOpt = Option[T = Int64]
  sort Tagger
    sort C = ?
    operation probe(x: C) -> Int64
  end
  sort Bk
    entity bk(k: Int64)
    provides Tagger[C = Bk]
    operation probe(x: Bk) -> Int64 = 7
  end
  sort Desc
    sort T = ?
    operation d(x: T) -> Int64
  end
  sort Wide
    sort W = ?
  end
  sort Narrow
    requires Wide[W = Int64]
    entity narrow
  end
  sort WP
    provides Wide[W = Int64]
  end
"""

rows = []
n = 0
for pname, A, lit, B, expect in PAIRS:
    for pos, decls, body in POSITIONS:
        if pos == "type-admits" and pname not in NAMED:
            continue
        n += 1
        ns = f"c{n:03d}"
        text = HEAD.format(ns=ns)
        text += f"  operation mkA() -> {A} = {lit}\n"
        text += decls.replace("{B}", B)
        text += f"  operation go() -> Int64 =\n    {body.replace('{B}', B).replace('{A}', A)}\n"
        text += """  sort Program
    requires anthill.cli.Main
    operation main(args: List[T = String]) -> Int64 effects {ConsoleOutput} =
      let _ = println(console(), to_string(go()))
      0
  end
end
"""
        open(os.path.join(OUT, f"{ns}.anthill"), "w").write(text)
        rows.append((ns, pname, pos, expect, "run"))
with open(os.path.join(OUT, "manifest.tsv"), "w") as m:
    for r in rows:
        m.write("\t".join(r) + "\n")
print(len(rows), "programs")
