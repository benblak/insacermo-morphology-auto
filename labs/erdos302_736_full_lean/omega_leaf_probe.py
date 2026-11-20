#!/usr/bin/env python3
"""One certificate leaf encoded as exact integer inequalities in Lean omega.
This tests feasibility of formalizing source-derived Farkas arithmetic
without invoking a global SAT search. One leaf is not a global proof.
"""
import collections, json, pathlib
root=pathlib.Path("labs/erdos302_736_full_lean")
# Retrieve pinned historical certificate from the original branch via ZIP in workflow.
D=json.loads(pathlib.Path("/tmp/erdos736-source/tree_certificate.json").read_text())
rows=[(tuple(t),1) for t in D["core_triples"]]+[(tuple(g["verts"]),g["value"]) for g in D["groups"]]
core=sorted(D["core_vertices"]); K=D["scale"]
fixed={};node=D["tree"]
while "split" in node:
 fixed[node["split"]]=0;node=node["zero"]
selected=node["dual"]
coefficient=collections.Counter();rhs=0
for i,w in selected:
 vs,m=rows[i];rhs+=w*m
 for v in vs:coefficient[v]+=w
def sm(vs):return " + ".join(f"x {v}" for v in vs) or "0"
s=["import Lean","set_option maxHeartbeats 2000000000","set_option maxRecDepth 131072",
"namespace INSACERMO.OmegaLeaf","theorem first_leaf (x : Nat → Nat)","  (hx : ∀ v, x v ≤ 1)"]
for j,(i,w) in enumerate(selected):
 vs,m=rows[i];s.append(f"  (h{j} : {m} ≤ ({sm(vs)}))")
for j,(v,q) in enumerate(fixed.items()):
 s.append(f"  (fix{j} : x {v} = {q})")
s.append(f"  (budget : ({sm(core)}) ≤ 102) : False := by")
for j,(i,w) in enumerate(selected):
 vs,m=rows[i];s.append(f"  have t{j} : ({w} * {m}) ≤ ({w} * ({sm(vs)})) := Nat.mul_le_mul_left {w} h{j}")
weighted=" + ".join(f"({w} * ({sm(rows[i][0])}))" for i,w in selected)
coef_sum=" + ".join(f"({coefficient[v]} * x {v})" for v in sorted(coefficient))
s.append(f"  have hsum : {rhs} ≤ ({weighted}) := by omega")
s.append(f"  have hrearrange : ({weighted}) = ({coef_sum}) := by omega")
excess=sum(max(0,coefficient[v]-K) for v in coefficient if v not in fixed)
s.append(f"  have hupper : ({coef_sum}) ≤ ({K} * ({sm(core)}) + {excess}) := by")
for v in sorted(coefficient):
 if coefficient[v]>K and v not in fixed:s.append(f"    have b{v} := hx {v}")
s.append("    omega")
s.append("  omega")
s.append("end INSACERMO.OmegaLeaf")
out=pathlib.Path("/tmp/erdos736-OmegaLeaf.lean");out.write_text("\n".join(s)+"\n")
print("OMEGA_LEAF_SOURCE bytes",out.stat().st_size,"selected",len(selected),"fixed",fixed,"excess",excess)
