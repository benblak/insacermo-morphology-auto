#!/usr/bin/env python3
"""Generate a single exact Lean checker test from real 736 Farkas data.
The 113-node tree and 9 higher-order constraints are taken from the
previous independent arithmetic proof guide; SciPy only *proposes* weights.
Lean checks the exact integer margin; no optimizer result is trusted.
"""
import runpy, pathlib, collections, itertools, os
import numpy as np
from scipy.optimize import linprog

base=pathlib.Path("labs/erdos302_736_full_lean/generate_filtered_branch_lean.py")
d=runpy.run_path(str(base))
core=d["vertices"]; ix=d["ix"]; A=d["A"]; b=d["b"]; C=d["C"]; K=d["K"]; comps=d["d"]["comps"]
tree=d["d"]["tree"]
fixed={}; node=tree
while node is not None:
    v,z,o=node;fixed[ix[v]]=0;node=z
bounds=[(fixed[i],fixed[i]) if i in fixed else (0,1) for i in range(len(core))]
res=linprog(np.ones(len(core)),A_ub=-A,b_ub=b,bounds=bounds,method="highs")
assert res.success and res.fun>102
weights=[(i,max(0,int(round(-float(y)*K)))) for i,y in enumerate(res.ineqlin.marginals)]
weights=[(i,w) for i,w in weights if w]
def edges_of(vs):
  st=set(vs)
  return [e for e in d["d"]["triples"] if set(e)<=st]
def cover_min(vs):
  ee=edges_of(vs)
  for k in range(len(vs)+1):
    for sub in itertools.combinations(vs,k):
      if all(set(sub)&set(e) for e in ee):
        return k
  raise AssertionError
small=[(part,cover_min(part)) for part in comps[1:]]
assert len(small)==18 and sum(m for v,m in small)==24
rows=[([core[v] for v in C[i][0]],C[i][1],w) for i,w in weights]+[(v,m,K) for v,m in small]
fixes={core[i]:bool(v) for i,v in fixed.items()}
coeff=collections.Counter()
rhs=0
for verts,m,w in rows:
  rhs+=m*w
  for v in verts:coeff[v]+=w
surplus=sum((c-K) if fixes.get(i,None) is True else (0 if fixes.get(i,None) is False else max(0,c-K)) for i,c in coeff.items())
margin=rhs - K*126 - surplus
assert margin>0,margin
def row_expr(vs,m,w):
  condition=" || ".join(f"i == {v}" for v in vs)
  return f"{{ coeff := fun i => if {condition} then 1 else 0, minimum := {m}, weight := {w} }}"
out=pathlib.Path(os.environ.get("ERDOS_DATA_OUT","/tmp/proof736/ConcreteLeaf.lean"))
out.parent.mkdir(parents=True,exist_ok=True)
s=["import CertificateKernel","open INSACERMO.Proof736","namespace INSACERMO.ConcreteLeaf",
   "def cert0 : List Row := [", ",\n".join(row_expr(*r) for r in rows),"]"]
s.append("def fixed0 (i : Nat) : Option Bool :=")
for i,v in fixes.items():
  s.append(f"  if i == {i} then some {'true' if v else 'false'} else")
s.append("  none")
s.append("""theorem certificate0_valid :
  (100000000 : Int) * (126 : Int) +
    sumOn (List.range 737)
      (fun i => slack (combined cert0 i) 100000000 (fixed0 i)) < rhs cert0 := by
  decide

end INSACERMO.ConcreteLeaf
""")
out.write_text("\n".join(s))
print("CONCRETE_LEAF_GENERATED",out.stat().st_size,"rows",len(rows),
      "small_components",len(small),"fixed",fixes,
      "margin",margin, "source",out)
