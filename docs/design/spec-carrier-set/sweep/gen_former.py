import itertools, os, sys
# WI-20261122-CXR5B — a FUNCTION-TYPED carrier: `Ap[F, R]` in both declaration orders (`_ab`: F
# first, `_ba`: R first), the call's argument at `F` a lambda or a named operation. A verdict that
# moves with the order is a reader taking the single carrier parameter.
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
OPS = """    operation run(f: F, r: R) -> Int64
    operation only(f: F) -> Int64
    operation tag(r: R) -> Int64"""
PROVIDERS = {
  # one provider, at F = (Int64) -> Int64, R = Foo
  "one": """  sort W
    provides Ap[F = (Int64) -> Int64, R = Foo]
    operation run(f: (Int64) -> Int64, r: Foo) -> Int64 = f(41)
    operation only(f: (Int64) -> Int64) -> Int64 = f(1)
    operation tag(r: Foo) -> Int64 = 3
  end""",
  # two providers at R = Foo that bind F apart
  "two": """  sort W1
    provides Ap[F = (Int64) -> Int64, R = Foo]
    operation run(f: (Int64) -> Int64, r: Foo) -> Int64 = f(41)
    operation only(f: (Int64) -> Int64) -> Int64 = f(1)
    operation tag(r: Foo) -> Int64 = 3
  end
  sort W2
    provides Ap[F = (String) -> Int64, R = Foo]
    operation run(f: (String) -> Int64, r: Foo) -> Int64 = f("s") + 100
    operation only(f: (String) -> Int64) -> Int64 = f("t") + 100
    operation tag(r: Foo) -> Int64 = 4
  end""",
}
CALLS = {
  "typed":    "Ap.run(lambda (x: Int64) -> x + 1, foo)",
  "typedS":   "Ap.run(lambda (x: String) -> 7, foo)",
  "unsaid":   "Ap.run(lambda x -> 1, foo)",
  "named":    "Ap.run(inc, foo)",
  "only_typed":  "Ap.only(lambda (x: Int64) -> x + 1)",
  "only_unsaid": "Ap.only(lambda x -> 5)",
  "bracket":  "Ap[F = (Int64) -> Int64].run(lambda x -> x + 1, foo)",
  "tag":      "Ap.tag(foo)",
}
def program(ns, order, prov, call):
    tv = ["    sort F = ?", "    sort R = ?"]
    if order == "ba":
        tv.reverse()
    return f"""namespace fm.{ns}
  import anthill.cli.Main
  import anthill.prelude.Console.{{console, println, ConsoleOutput}}
  import anthill.prelude.Int64.{{to_string}}
  import anthill.prelude.{{Int64, String, List, Error}}
  sort Ap
{tv[0]}
{tv[1]}
{OPS}
  end
  sort Foo
    entity foo
  end
{PROVIDERS[prov]}
  operation inc(x: Int64) -> Int64 = x + 1
  sort Program
    requires anthill.cli.Main
    operation main(args: List[T = String]) -> Int64
      effects {{ConsoleOutput, Error}}
    =
      let _ = println(console(), to_string({CALLS[call]}))
      0
  end
end
"""
n = 0
for prov, call in itertools.product(PROVIDERS, CALLS):
    for order in ["ab", "ba"]:
        ns = f"{prov}_{call}_{order}"
        open(os.path.join(out, ns + ".anthill"), "w").write(program(ns, order, prov, call))
        n += 1
print(n)
