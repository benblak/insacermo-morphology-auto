#!/usr/bin/env python3
"""One-leaf Lean omega feasibility experiment: exact nontrusted scipy weights,
no theorem claim about all branches. Uses original exact 709 hyperedge
constraints plus nine derived valid small-group constraints.
"""
import runpy, collections, pathlib, os
import numpy as np
from scipy.optimize import linprog
p=pathlib.Path(__file__).with_name("generate_filtered_branch_lean.py")
d=runpy.run_path(str(p))
V=d["vertices"]; n=len(V); C=d["C"]; A=d["A"]; b=d["b"]; K=d["K"]; idx=d["ix"]; tree=d["d"]["tree"]
fixed={}; node=tree
while node is not None and node[0]:
   var,z,o=node; fixed[idx[var]]=0;node=z
bounds=[(fixed[i],fixed[i]) if i in fixed else (0,1) for i in range(n)]
res=linprog(np.ones(n),A_ub=-A,b_ub=b,bounds=bounds,method="highs")
assert res.success and res.fun>102
sel=[(i,max(0,int(round(-float(y)*K)))) for i,y in enumerate(res.ineqlin.marginals)]
sel=[(i,w) for i,w in sel if w]
coef=collections.Counter();rhs=0
for i,w in sel:
 vs,m=C[i];rhs+=w*m
 for v in vs:coef[V[v]]+=w
def sm(vs):return " + ".join(f"x {v}" for v in vs) or "0"
s=["import Lean","set_option maxRecDepth 131072","set_option maxHeartbeats 2000000000","namespace INSACERMO.OmegaProbe","theorem one_leaf (x : Nat → Nat)","  (hx : ∀ v, x v ≤ 1)"]
for j,(i,w) in enumerate(sel):
 vs,m=C[i];s.append(f"  (h{j} : {m} ≤ ({sm([V[v] for v in vs])}))")
for j,(v,q) in enumerate(fixed.items()):
 s.append(f"  (fix{j} : x {V[v]} = {q})")
s.append(f"  (budget : ({sm(V)}) ≤ 102) : False := by")
for j,(i,w) in enumerate(sel):
 vs,m=C[i];s.append(f"  have t{j} : ({w} * {m}) ≤ ({w} * ({sm([V[v] for v in vs])})) := Nat.mul_le_mul_left {w} h{j}")
weighted=" + ".join(f"({w} * ({sm([V[v] for v in C[i][0]])}))" for i,w in sel)
cf=" + ".join(f"({coef[v]} * x {v})" for v in sorted(coef))
s.append(f"  have hsum : {rhs} ≤ ({weighted}) := by omega")
s.append(f"  have hrearrange : ({weighted}) = ({cf}) := by omega")
# each coefficient x <= K*x+max(c-K,0) for binary x
ex=sum(max(0,coef[v]-K) for v in coef)
s.append(f"  have hupper : ({cf}) ≤ ({K} * ({sm(V)}) + {ex}) := by")
for v in sorted(coef):
 if coef[v]>K:s.append(f"    have b{v} := hx {v}")
s.append("    omega")
s.append("  omega")
s.append("end INSACERMO.OmegaProbe")
out=pathlib.Path("/tmp/erdos736-omega-one-leaf.lean");out.write_text("\n".join(s)+"\n")
print("OMEGA_SINGLE_LEAF",out.stat().st_size,len(sel),"weights", "rhs",rhs,"excess",ex, "n",len(V))
