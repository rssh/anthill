import itertools, os, sys
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
# Sp[A, B] with op(c: A, x: B) -> Int64 and get(c: A) -> B
# providers: each (sort, binds A, binds B, entity?, op value, get value)
PAIRS = {
  # one provider at P (own at A), one witness at Foo
  "own_and_wit":   [("P", "Self", "Int64", "entity p", "1", "5"), ("W", "Foo", "Int64", "", "2", "6")],
  # two witnesses at Foo, B apart
  "two_wit_b":     [("W1", "Foo", "Int64", "", "1", "5"), ("W2", "Foo", "String", "", "2", "\"s\"")],
  # two own providers
  "two_own":       [("P", "Self", "Int64", "entity p", "1", "5"), ("Q", "Self", "Int64", "entity q", "2", "6")],
  # own provider binding A to itself, witness binding A to it as well (rival at P)
  "own_rival_wit": [("P", "Self", "Int64", "entity p", "1", "5"), ("W", "P", "Int64", "", "2", "6")],
}
CALLS = {
  "qual_p":    ("Sp.op(p, 1)", ""),
  "qual_foo":  ("Sp.op(foo, 1)", ""),
  "dot_p":     ("p.op(1)", ""),
  "generic_p": ("viaReq(p)", "  operation viaReq[X](x: X) -> Int64 requires Sp[A = X, B = Int64] = Sp.op(x, 1)\n"),
  "get_int":   ("Sp.get(foo) + 0", ""),
  "get_str":   ("String.length(Sp.get(foo))", ""),
  "bracket_w2":("String.length(Sp.get[Sp = W2](foo))", ""),
}
def sortblock(name, ba, bb, ent, opv, getv):
    A = name if ba == "Self" else ba
    Btype = name if bb == "Self" else bb
    lines = [f"  sort {name}"]
    if ent: lines.append(f"    {ent}")
    lines.append(f"    provides Sp[A = {ba}, B = {bb}]")
    lines.append(f"    operation op(c: {A}, x: {Btype}) -> Int64 = {opv}")
    lines.append(f"    operation get(c: {A}) -> {Btype} = {getv}")
    lines.append("  end")
    return "\n".join(lines)
def program(ns, order, pair, call):
    tv = ["    sort A = ?", "    sort B = ?"]
    if order == "ba": tv.reverse()
    expr, extra = CALLS[call]
    provs = "\n".join(sortblock(*p) for p in PAIRS[pair])
    return f"""namespace sw2.{ns}
  import anthill.cli.Main
  import anthill.prelude.Console.{{console, println, ConsoleOutput}}
  import anthill.prelude.Int64.{{to_string}}
  import anthill.prelude.{{Int64, String, List, Error}}
  sort Sp
{tv[0]}
{tv[1]}
    operation op(c: A, x: B) -> Int64
    operation get(c: A) -> B
  end
  sort Foo
    entity foo
  end
{provs}
{extra}  sort Program
    requires anthill.cli.Main
    operation main(args: List[T = String]) -> Int64
      effects {{ConsoleOutput, Error}}
    =
      let _ = println(console(), to_string({expr}))
      0
  end
end
"""
n=0
for pair, call in itertools.product(PAIRS, CALLS):
    for order in ["ab","ba"]:
        ns=f"{pair}_{call}_{order}"
        open(os.path.join(out, ns+".anthill"),"w").write(program(ns, order, pair, call)); n+=1
print(n)
