import sys, collections, re
S=sys.argv[1]   # the directory holding progs/ and verdicts.tsv
man={l.split("\t")[0]: l.rstrip("\n").split("\t") for l in open(S+"/progs/manifest.tsv")}
ver={l.split("\t")[0]: l.rstrip("\n").split("\t",1)[1] for l in open(S+"/verdicts.tsv", errors="replace")}
LAB=[("backs no operation","R:no-backing"),("two suppliers","R:tie"),("ambiguous","R:tie"),("operation has no body","R:no-body"),
     ("call-site type arguments","R:bracket-in-rule-body"),("type mismatch","R:type-mismatch"),("OperationBodyMissing","R:body-missing")]
def short(v):
    v=v.strip()
    if v.startswith("ERR"):
        labs=[]
        for part in v[5:].split("|"):
            if not part: continue
            lab=next((l for k,l in LAB if k in part), "R:"+part[:40])
            if lab not in labs: labs.append(lab)
        return "+".join(labs)
    m=re.search(r"\?r = (\S+)", v)
    if m: return m.group(1)
    if "solution" in v and "?r" not in v: return "no answer"
    return v
rows=collections.OrderedDict()
for ns,(ns_,shape,dflt,cfg,route,exp,mode) in man.items():
    rows.setdefault((shape,dflt,cfg,exp),{})[route]=(short(ver[ns]),ns)
for shape in ("recv","nullary"):
    rts=["by-name","dot","dictionary","abstract-receiver","rule-body"] if shape=="recv" else ["by-name","dictionary","rule-body"]
    print(f"\n== {shape}: " + " | ".join(rts))
    for (sh,d,c,e),r in rows.items():
        if sh!=shape: continue
        vals=[r.get(x,("",""))[0] for x in rts]
        cmp=[v for x,v in zip(rts,vals) if not (shape=="nullary" and x=="rule-body")]
        flag = "" if len(set(cmp))==1 else "   <-- differs"
        print(f"{d:9s} {c:17s} expect {e:14s} " + " | ".join(f"{v:14s}" for v in vals) + flag)
