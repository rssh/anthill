import itertools, os, sys
# WI-20261122-CXR5B, the P readers: ONE provider whose OWN provisions of a spec are at two
# applications that bind `Elem` apart (`P provides Sp[C = Self, Elem = Int64, …]` beside
# `[C = Self, Elem = String, …]`), written in both orders. A verdict that moves with the order
# is a reader taking the first written provision.
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
# spec shapes: (decl in Sp, member for Elem = {E}, binding name)
SPECS = {
  "res": ("    operation first(c: C) -> Elem", "operation m{E}(c: P) -> {E} = {v}"),
  "arg": ("    operation put(c: C, x: Elem) -> Int64", "operation m{E}(c: P, x: {E}) -> Int64 = {n}"),
}
VAL = {"Int64": ("1", "1"), "String": ('"two"', "2")}
# calls: (template per spec shape, extra declarations); `{I}` an Int64 answer, `{S}` a String one
CALLS = {
  "int":   ({"res": "Sp.first(p)", "arg": "Sp.put(p, 5)"}, ""),
  "str":   ({"res": "String.length(Sp.first(p))", "arg": 'Sp.put(p, "s")'}, ""),
  "brI":   ({"res": "Sp[Elem = Int64].first(p)", "arg": "Sp[Elem = Int64].put(p, 5)"}, ""),
  "brS":   ({"res": "String.length(Sp[Elem = String].first(p))", "arg": 'Sp[Elem = String].put(p, "s")'}, ""),
  "genI":  ({"res": "viaI(p)", "arg": "viaI(p)"},
            {"res": "  operation viaI[X](x: X) -> Int64 requires Sp[C = X, Elem = Int64] = Sp.first(x)\n",
             "arg": "  operation viaI[X](x: X) -> Int64 requires Sp[C = X, Elem = Int64] = Sp.put(x, 5)\n"}),
  "genS":  ({"res": "String.length(viaS(p))", "arg": "viaS(p)"},
            {"res": "  operation viaS[X](x: X) -> String requires Sp[C = X, Elem = String] = Sp.first(x)\n",
             "arg": '  operation viaS[X](x: X) -> Int64 requires Sp[C = X, Elem = String] = Sp.put(x, "s")\n'}),
  "reqS":  ({"res": "takes(p)", "arg": "takes(p)"},
            {"res": "  operation takes(i: P) -> Int64 requires Sp[C = P, Elem = String] = String.length(Sp.first(i))\n",
             "arg": '  operation takes(i: P) -> Int64 requires Sp[C = P, Elem = String] = Sp.put(i, "s")\n'}),
  "projI": ({"res": "getE(p)", "arg": "getE(p)"},
            {"res": "  operation getE(c: P) -> c.Elem = Sp.first(c)\n",
             "arg": "  operation getE(c: P) -> Int64 = useE(c, 5)\n  operation useE(c: P, x: c.Elem) -> Int64 = Sp.put(c, x)\n"}),
  "projS": ({"res": "String.length(getE(p))", "arg": "getE(p)"},
            {"res": "  operation getE(c: P) -> c.Elem = Sp.first(c)\n",
             "arg": '  operation getE(c: P) -> Int64 = useE(c, "s")\n  operation useE(c: P, x: c.Elem) -> Int64 = Sp.put(c, x)\n'}),
  "holdI": ({"res": "Hold.get(hold(p))", "arg": "Hold.get(hold(p))"},
            {"res": "  sort Hold\n    sort X = ?\n    requires Sp[C = X, Elem = Int64]\n    entity hold(x: X)\n    operation get(h: Self) -> Int64 = Sp.first(h.x)\n  end\n",
             "arg": "  sort Hold\n    sort X = ?\n    requires Sp[C = X, Elem = Int64]\n    entity hold(x: X)\n    operation get(h: Self) -> Int64 = Sp.put(h.x, 5)\n  end\n"}),
  # No provision at `Elem = Bool`: refused in either order, the view's left-out `Elem` read as
  # no provision at it.
  "genB":  ({"res": "viaB(p)", "arg": "viaB(p)"},
            {"res": "  operation viaB[X](x: X) -> Int64 requires Sp[C = X, Elem = Bool] = 4\n",
             "arg": "  operation viaB[X](x: X) -> Int64 requires Sp[C = X, Elem = Bool] = Sp.put(x, true)\n"}),
  "reqB":  ({"res": "takesB(p)", "arg": "takesB(p)"},
            {"res": "  operation takesB(i: P) -> Int64 requires Sp[C = P, Elem = Bool] = 4\n",
             "arg": "  operation takesB(i: P) -> Int64 requires Sp[C = P, Elem = Bool] = Sp.put(i, true)\n"}),
  "holdB": ({"res": "Hold.get(hold(p))", "arg": "Hold.get(hold(p))"},
            {"res": "  sort Hold\n    sort X = ?\n    requires Sp[C = X, Elem = Bool]\n    entity hold(x: X)\n    operation get(h: Self) -> Int64 = 4\n  end\n",
             "arg": "  sort Hold\n    sort X = ?\n    requires Sp[C = X, Elem = Bool]\n    entity hold(x: X)\n    operation get(h: Self) -> Int64 = Sp.put(h.x, true)\n  end\n"}),
  "brB":   ({"res": "Sp[Elem = Bool].first(p)", "arg": "Sp[Elem = Bool].put(p, true)"}, ""),
  "argB":  ({"res": "boolOf(Sp.first(p))", "arg": "Sp.put(p, true)"},
            {"res": "  operation boolOf(b: Bool) -> Int64 = 4\n", "arg": ""}),
}
STYLES = ["bound"]
def program(ns, order, spec, call):
    decl, member_t = SPECS[spec]
    provs, members = [], []
    for E in ["Int64", "String"]:
        v, n = VAL[E]
        opname = decl.split("operation ")[1].split("(")[0]
        provs.append(f"    provides Sp[C = Self, Elem = {E}, {opname} = P.m{E}]")
        members.append("    " + member_t.format(E=E, v=v, n=n))
    if order == "si":
        provs.reverse()
    tmpl, extra = CALLS[call]
    extra = extra[spec] if isinstance(extra, dict) else extra
    body = tmpl[spec]
    return f"""namespace own.{ns}
  import anthill.cli.Main
  import anthill.prelude.Console.{{console, println, ConsoleOutput}}
  import anthill.prelude.Int64.{{to_string}}
  import anthill.prelude.{{Int64, String, List, Error, Bool}}
  sort Sp
    sort C = ?
    sort Elem = ?
{decl}
  end
  sort P
    entity p
{provs[0]}
{provs[1]}
{members[0]}
{members[1]}
  end
{extra}  sort Program
    requires anthill.cli.Main
    operation main(args: List[T = String]) -> Int64
      effects {{ConsoleOutput, Error}}
    =
      let _ = println(console(), to_string({body}))
      0
  end
end
"""
n = 0
for spec, call in itertools.product(SPECS, CALLS):
    for order in ["is", "si"]:
        ns = f"{spec}_{call}_{order}"
        open(os.path.join(out, ns + ".anthill"), "w").write(program(ns, order, spec, call))
        n += 1
print(n)
