import sys,collections,re
S=sys.argv[1]   # the directory holding progs/ and verdicts.tsv
man=[l.rstrip("\n").split("\t") for l in open(S+"/progs/manifest.tsv")]
ver={l.split("\t")[0]: l.rstrip("\n").split("\t",1)[1] for l in open(S+"/verdicts.tsv",errors="replace")}
def short(v):
    v=v.strip()
    if v.startswith("ERR"):
        part=v[5:].split("|")[0]
        m=re.search(r"type mismatch in \S*\s*\(([^)]*)\)",part)
        if m: return "no:"+m.group(1)
        return "no:"+part[:30]
    return v
pos=["argument","let","return","field","list-element","lambda-argument","provision","type-admits"]
rows=collections.OrderedDict()
for ns,p,po,e,_ in man: rows.setdefault((p,e),{})[po]=(short(ver[ns]),ns)
if len(sys.argv)>2:
    for (p,e),r in rows.items():
        for x in pos:
            if x in r: print(p,x,r[x][1],ver[r[x][1]][:300])
    sys.exit()
print(f"{'pair':25s} {'spec':4s} "+" | ".join(f"{x[:12]:12s}" for x in pos))
for (p,e),r in rows.items():
    print(f"{p:25s} {e:4s} "+" | ".join(f"{r.get(x,('',''))[0][:12]:12s}" for x in pos))
