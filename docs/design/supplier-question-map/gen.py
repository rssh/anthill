#!/usr/bin/env python3
"""The supplier question as a matrix: one program per (operation shape, default?, supply
configuration, route). Within one row (shape, default, config) every route should give the
same answer (kernel-language §8.7, "Operation override"). Run from the repo root:
    python3 gen.py <out_dir>        writes the programs and a manifest.tsv
"""
import os, sys

OUT = sys.argv[1]
os.makedirs(OUT, exist_ok=True)

HEAD = """namespace probe.{ns}
  import anthill.cli.Main
  import anthill.prelude.Console.{{console, println, ConsoleOutput}}
  import anthill.prelude.Int64.{{to_string}}
  import anthill.prelude.{{List, String}}
"""

# The two shapes. `recv`: the spec operation takes the carrier (`describe(x: T)`);
# `nullary`: it takes nothing, so only a bracket names the carrier (`name()`).
SHAPES = {
    "recv": dict(op="describe", sig="(x: T)", own_sig="(x: Leaf)", bind_sig="(x: Leaf)"),
    "nullary": dict(op="name", sig="()", own_sig="()", bind_sig="()"),
}

# Supply configurations: what supplies the operation for the carrier `Leaf`.
# Each value: (Leaf's body, text after Leaf, expected answer when defaulted, when body-less)
def configs(s):
    op, own, bind = s["op"], s["own_sig"], s["bind_sig"]
    witness = f"""
  sort W
    provides Desc[T = Leaf]
    operation {op}{own} -> Int64 = 4
  end
"""
    bound = f"\n  operation other{bind} -> Int64 = 3\n"
    return {
        "default-only": ("    provides Desc[T = Leaf]\n", "", "1", "refused: backs no operation"),
        "own": (f"    provides Desc[T = Leaf]\n    operation {op}{own} -> Int64 = 2\n", "", "2", "2"),
        "binding-in-body": (f"    provides Desc[T = Leaf, {op} = other]\n", bound, "3", "3"),
        "binding-in-entry": ("",
                             bound + f"\n  namespace Leaf\n    provides Desc[T = Leaf, {op} = other]\n  end\n", "3", "3"),
        "binding-both": ("    provides Desc[T = Leaf]\n",
                         bound + f"\n  namespace Leaf\n    provides Desc[T = Leaf, {op} = other]\n  end\n", "3", "3"),
        "witness-only": ("", witness, "4", "4"),
        "own+binding": (f"    provides Desc[T = Leaf]\n    operation {op}{own} -> Int64 = 2\n",
                        bound + f"\n  namespace Leaf\n    provides Desc[T = Leaf, {op} = other]\n  end\n",
                        "refused: tie", "refused: tie"),
    }

# Routes: how the call is reached. Each: (extra declarations, the expression main prints,
# or None for a rule-body route answered by a query).
def routes(s):
    op = s["op"]
    if op == "describe":
        return {
            "by-name": ("", "Desc.describe(leaf())"),
            "dot": ("", "leaf().describe()"),
            "dictionary": ("  operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)\n",
                           "gen(leaf())"),
            "abstract-receiver": ("  operation viaShape(s: Shape) -> Int64 = Desc.describe(s)\n",
                                  "viaShape(leaf())"),
            "rule-body": ("  rule rq(?r) :- ?r <=> Desc.describe(leaf())\n", None),
        }
    return {
        "by-name": ("", "Desc.name[T = Leaf]()"),
        "dictionary": ("  operation gen[A]() -> Int64 requires Desc[T = A] = Desc.name[T = A]()\n",
                       "gen[A = Leaf]()"),
        "rule-body": ("  rule rq(?r) :- ?r <=> Desc.name[T = Leaf]()\n", None),
    }

rows = []
n = 0
for shape, s in SHAPES.items():
    for defaulted in (True, False):
        body = " = 1" if defaulted else ""
        for cfg, (leaf_body, after, exp_def, exp_bl) in configs(s).items():
            for route, (extra, expr) in routes(s).items():
                n += 1
                ns = f"s{n:03d}"
                text = HEAD.format(ns=ns)
                text += f"""
  sort Shape
    sort E = ?
  end

  sort Desc
    sort T = ?
    operation {s['op']}{s['sig']} -> Int64{body}
  end

  sort Leaf
    entity leaf
    provides Shape[E = Int64]
{leaf_body}  end
{after}
{extra}"""
                if expr is not None:
                    text += f"""
  sort Program
    requires anthill.cli.Main
    operation main(args: List[T = String]) -> Int64 effects {{ConsoleOutput}} =
      let _ = println(console(), to_string({expr}))
      0
  end
"""
                text += "end\n"
                path = os.path.join(OUT, f"{ns}.anthill")
                open(path, "w").write(text)
                rows.append((ns, shape, "defaulted" if defaulted else "body-less", cfg, route,
                             exp_def if defaulted else exp_bl, "query" if expr is None else "run"))
with open(os.path.join(OUT, "manifest.tsv"), "w") as m:
    for r in rows:
        m.write("\t".join(r) + "\n")
print(len(rows), "programs")
