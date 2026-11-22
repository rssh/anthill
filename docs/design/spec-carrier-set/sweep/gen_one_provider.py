import itertools, os, sys
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
# spec op shapes: (decl lines in Sp, member template for a provider at A=X,B=Y, call template)
SPECS = {
  "both":    ("    operation op(c: A, x: B) -> Int64", "operation {name}(c: {A}, x: {B}) -> Int64 = {val}", "Sp.op({a}, {b})"),
  "swapped": ("    operation op(x: B, c: A) -> Int64", "operation {name}(x: {B}, c: {A}) -> Int64 = {val}", "Sp.op({b}, {a})"),
  "resonly": ("    operation op(c: A) -> B",           "operation {name}(c: {A}) -> {B} = {bval}",          "Sp.op({a})"),
  "aonly":   ("    operation op(c: A) -> Int64",       "operation {name}(c: {A}) -> Int64 = {val}",         "Sp.op({a})"),
  "bonly":   ("    operation op(x: B) -> Int64",       "operation {name}(x: {B}) -> Int64 = {val}",         "Sp.op({b})"),
}
# provision kinds: the provider sort, its binding of A and B, and the values a call passes
KINDS = {
  "own_a":   dict(prov="P", A="P",    B="Int64", a="p", b="1", bval="5", ent="    entity p\n"),
  "own_b":   dict(prov="P", A="Int64", B="P",   a="1", b="p", bval="p", ent="    entity p\n"),
  "wit":     dict(prov="W", A="Foo",  B="Int64", a="foo", b="1", bval="5", ent=""),
  "wit_b":   dict(prov="W", A="Int64", B="Foo", a="1", b="foo", bval="foo", ent=""),
}
STYLES = ["member", "bound"]
EXPECT = {"resonly": "to_string", }
def program(ns, order, spec, kind, style):
    decl, member_t, call_t = SPECS[spec]
    k = KINDS[kind]
    A, B = k["A"], k["B"]
    tv = ["    sort A = ?", "    sort B = ?"]
    if order == "ba": tv.reverse()
    bind_a = "Self" if A == k["prov"] else A
    bind_b = "Self" if B == k["prov"] else B
    name = "op" if style == "member" else "impl"
    member = member_t.format(name=name, A=A, B=B, val="7", bval=k["bval"])
    opbind = "" if style == "member" else ", op = %s.impl" % k["prov"]
    call = call_t.format(a=k["a"], b=k["b"])
    if spec == "resonly":
        res = B
        if res == "Int64":
            body = "to_string(%s)" % call
        else:
            body = "to_string(use(%s))" % call
    else:
        body = "to_string(%s)" % call
    use = "  operation use(v: %s) -> Int64 = 3\n" % B if (spec == "resonly" and B != "Int64") else ""
    return f"""namespace sw.{ns}
  import anthill.cli.Main
  import anthill.prelude.Console.{{console, println, ConsoleOutput}}
  import anthill.prelude.Int64.{{to_string}}
  import anthill.prelude.{{Int64, String, List, Error}}
  sort Sp
{tv[0]}
{tv[1]}
{decl}
  end
  sort Foo
    entity foo
  end
  sort {k['prov']}
{k['ent']}    provides Sp[A = {bind_a}, B = {bind_b}{opbind}]
    {member}
  end
{use}  sort Program
    requires anthill.cli.Main
    operation main(args: List[T = String]) -> Int64
      effects {{ConsoleOutput, Error}}
    =
      let _ = println(console(), {body})
      0
  end
end
"""
n = 0
for spec, kind, style in itertools.product(SPECS, KINDS, STYLES):
    for order in ["ab", "ba"]:
        ns = f"{spec}_{kind}_{style}_{order}"
        open(os.path.join(out, ns + ".anthill"), "w").write(program(ns, order, spec, kind, style))
        n += 1
print(n)
