#!/usr/bin/env python3
"""Generate Lean 4 source proving Erdős302 N=736 bound by 57 preverified
LP-based branch choices, with *only* original forbidden-triple predicates
used as SAT hypotheses. The nontrusted dual selector merely chooses a
smaller subset of valid source clauses at each branch leaf. Lean's
bv_decide proves their logical sufficiency; no LP numeric result trusted.
"""
from pathlib import Path
import runpy,collections,os
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

# Existing generator supplies 742 triples, 19 components and 113-node branch
# split tree. That guide is not assumed true; it controls by_cases splits only.
path=Path(__file__).with_name("generate_guided_branch_proof.py")
d=runpy.run_path(str(path))
OUT=Path(os.environ.get("ERDOS_GUIDED_OUT","/tmp/erdos736-guided"))
base=(OUT/"Erdos736Guided.lean").read_text()
core=d['comps'][0]
vertices=list(core)
ix={v:i for i,v in enumerate(vertices)}
E=[tuple(ix[v] for v in e) for e in d['core_edges']]
G=[
 ([8,12,16,24,48],[[8,24,12],[16,48,12],[16,24,48]]),
 ([33,36,44,99,132,396],[[33,44,132],[33,36,396],[396,99,132]]),
 ([32,40,45,160,288,360],[[32,40,160],[40,360,45],[160,288,360]]),
 ([58,87,116,174,348],[[58,174,87],[116,348,87],[116,174,348]]),
 ([64,96,128,192,384],[[64,96,192],[96,384,128],[128,384,192]]),
 ([102,153,204,306,612],[[153,306,102],[612,153,204],[612,306,204]]),
 ([75,90,126,175,315,450],[[90,315,126],[450,90,75],[450,126,175]]),
 ([171,228,252,399,532,684],[[228,532,399],[684,171,228],[684,252,399]]),
 ([297,300,540,550,660,675],[[297,540,660],[660,300,550],[675,300,540]]),
]
edges=[tuple(e) for e in d["core_edges"]]
edge_map={tuple(sorted(e)):i for i,e in enumerate(edges)}
for verts,tes in G:
  assert len(tes)==3 and all(tuple(sorted(t)) in edge_map for t in tes)
C=[(tuple(e),1) for e in E]
C.extend((tuple(ix[v] for v in vs),2) for vs,es in G)
rr=[i for i,(vs,k) in enumerate(C) for v in vs]
cc=[v for vs,k in C for v in vs]
A=coo_matrix((np.ones(len(rr)),(rr,cc)),shape=(len(C),len(vertices))).tocsr()
b=-np.array([k for vs,k in C])
K=100000000

leaves=[]
def visit(tree,fixed):
 if tree is None:
  bounds=[(fixed[i],fixed[i]) if i in fixed else (0,1) for i in range(len(vertices))]
  res=linprog(np.ones(len(vertices)),A_ub=-A,b_ub=b,bounds=bounds,method='highs')
  assert res.success and res.fun>102,(res.message,res.fun)
  weights=[(i,max(0,int(round(-float(y)*K))))
          for i,y in enumerate(res.ineqlin.marginals)]
  weights=[(i,w) for i,w in weights if w]
  coeff=[0]*len(vertices);rhs=0
  for i,w in weights:
   vs,k=C[i]
   rhs+=w*(k-sum(fixed.get(v,-1)==1 for v in vs))
   for v in vs:
    if v not in fixed:coeff[v]+=w
  excess=sum(max(0,c-K) for c in coeff)
  margin=K*sum(v==1 for v in fixed.values())+rhs-excess-102*K
  assert margin>0,('nonvalidated Farkas margin',margin)
  selected=set()
  for i,w in weights:
   if i<len(E): selected.add(i)
   else:
    for e in G[i-len(E)][1]:
     selected.add(edge_map[tuple(sorted(e))])
  leaves.append((sorted(selected),margin,len(fixed)))
  return
 v,z,o=tree
 visit(z,{**fixed,ix[v]:0})
 visit(o,{**fixed,ix[v]:1})
visit(d['tree'],{})
assert len(leaves)==57

def bit(v):return f"(x.getLsbD {v-1})"
def cover(name,edges):
 return 'def '+name+' (x : BitVec 736) : Bool :=\n  '+'\n  && '.join('('+bit(a)+' || '+bit(b)+' || '+bit(c)+')' for a,b,c in edges)+'\n\n'

helper=''
for j,(indices,margin,depth) in enumerate(leaves):
 ee=[edges[i] for i in indices]
 helper+=cover(f"selectedCovered{j}",ee)
 helper+=f'''theorem coreToSelected{j} (x : BitVec 736)
  (h : compCovered0 x = true) : selectedCovered{j} x = true := by
  unfold compCovered0 at h
  unfold selectedCovered{j}
  bv_decide (config := {{ timeout := 30 }})

'''
counter=[0]
def guided(node,depth):
 if node is None:
  j=counter[0];counter[0]+=1
  pre='  '*depth
  return [pre+f"replace h : selectedCovered{j} x = true := coreToSelected{j} x h",
      pre+f"unfold selectedCovered{j} at h",
      pre+"unfold compExcluded0",
      pre+"bv_decide (config := { timeout := 120 })"]
 v,z,o=node;pre='  '*depth
 n=counter[0]
 lines=[pre+f"by_cases hbranch_{v}_{depth}_{n} : x.getLsbD {v-1} = true",pre+'·']
 lines+=guided(o,depth+1)
 lines.append(pre+'·')
 lines+=guided(z,depth+1)
 return lines
# The dual-selector leaf order is zero-first; Lean branch proof emits one-first.
# Use path keyed by (variable, bool) rather than relying on traversal order.
paths=d['paths']
lookup={tuple(path):j for j,path in enumerate(paths)}
def guided2(node,depth,steps=()):
 if node is None:
  j=lookup[steps];pre='  '*depth
  return [pre+f"replace h : selectedCovered{j} x = true := coreToSelected{j} x h",
      pre+f"unfold selectedCovered{j} at h",pre+"unfold compExcluded0",
      pre+"bv_decide (config := { timeout := 120 })"]
 v,z,o=node;pre='  '*depth
 name=f"hbranch_{v}_{depth}_{len(steps)}"
 lines=[pre+f"by_cases {name} : x.getLsbD {v-1} = true",pre+'·']
 lines+=guided2(o,depth+1,steps+((v,True),))
 lines.append(pre+'·')
 lines+=guided2(z,depth+1,steps+((v,False),))
 return lines

# Inject helpers after compExcluded0 and before old compBound0.
begin=base.index("theorem compBound0 ")
end=base.index("def compCovered1 ",begin)
repl="theorem compBound0 (x : BitVec 736)\n"
repl+="    (h : compCovered0 x = true) :\n"
repl+="    ((compExcluded0 x) < (103 : BitVec 10)) = false := by\n"
repl+="\n".join(guided2(d['tree'],1))+"\n\n"
new=base[:begin]+helper+repl+base[end:]
out=OUT/"Erdos736Filtered.lean"
out.write_text(new)
print("GENERATED_FILTERED_FULL_LEAN",out.stat().st_size,
      "leaves",len(leaves),"selected_edges_range",
      (min(len(i[0]) for i in leaves),max(len(i[0]) for i in leaves)),
      "minimum_integer_margin",min(i[1] for i in leaves),
      "not_trusting_external_LP_optimization_claims")
