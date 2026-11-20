#!/usr/bin/env python3
"""Lean SAT theorem decomposed by the 339 connected components of Erdős 302.
Same unconditional global claim f(736)<=609.
No engine modifications, no solver-optimality assumptions.
"""
import collections, itertools, os
from pathlib import Path
OUT=Path(os.environ.get("ERDOS_COMPONENT_OUT","/tmp/erdos736-components"))
OUT.mkdir(parents=True,exist_ok=True)
N=736
triples=[(a,b,c) for c in range(2,N+1) for b in range(1,c)
 if (b*c)%(b+c)==0 for a in [b*c//(b+c)] if 0<a<b]
assert len(triples)==742
parent=list(range(N+1))
def find(i):
 while parent[i]!=i:
  parent[i]=parent[parent[i]];i=parent[i]
 return i
for a,b,c in triples:
 for v in (a,b):parent[find(v)]=find(c)
cs=collections.defaultdict(list)
for v in range(1,N+1):cs[find(v)].append(v)
comps=sorted((v for v in cs.values() if len(v)>1),key=lambda z:(-len(z),z))
assert len(comps)==19 and len(comps[0])==344
assert sum(map(len,comps))==416
assert sorted(len(v) for v in comps)==sorted([344]+[3]*12+[5]*3+[7]*3)
def covered(vs):
 st=set(vs)
 return [e for e in triples if set(e)<=st]
def count_min(vs,ee):
 for k in range(len(vs)+1):
  for sub in itertools.combinations(vs,k):
   if all(set(e)&set(sub) for e in ee):return k
 raise AssertionError
counts=[count_min(v,covered(v)) for v in comps[1:]]
assert sum(counts)==24,counts
source='''import Lean

/-!
INSACERMO -- exact full upper-bound n=736, by 19 components.
Core component: 344 vertices, 709 edges; other 18 force 24 removals.
Global predicate: every 736-bit assignment covering all 742 forbidden triples
requires >=127 omitted positions. No C3 core modification.
-/
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000000
namespace INSACERMO.Erdos736ByComponents

'''
def bit(i):return f"(x.getLsbD {i-1})"
def cover_def(name,ee):
 return "def "+name+" (x : BitVec 736) : Bool :=\n  " + "\n  && ".join("("+bit(a)+" || "+bit(b)+" || "+bit(c)+")" for a,b,c in ee)+"\n\n"
def count_def(name,vs):
 return "def "+name+" (x : BitVec 736) : BitVec 10 :=\n  "+ "\n  + ".join(["(0 : BitVec 10)"]+[f"(if {bit(v)} then (1 : BitVec 10) else 0)" for v in vs]) + "\n\n"
source+=cover_def("allCovered",triples)
active=sorted({v for e in triples for v in e})
source+=count_def("activeExcluded",active)
for i,vs in enumerate(comps):
 m=103 if i==0 else counts[i-1]
 ee=covered(vs)
 source+=cover_def(f"compCovered{i}",ee)
 source+=count_def(f"compExcluded{i}",vs)
 source+=f'''theorem compBound{i} (x : BitVec 736)
    (h : compCovered{i} x = true) :
    ((compExcluded{i} x) < ({m} : BitVec 10)) = false := by
  unfold compCovered{i} at h
  unfold compExcluded{i}
  bv_decide (config := {{ timeout := 600 }})

'''
for i,vs in enumerate(comps):
 source+=f'''theorem allToComponent{i} (x : BitVec 736)
    (h : allCovered x = true) : compCovered{i} x = true := by
  unfold allCovered at h
  unfold compCovered{i}
  bv_decide (config := {{ timeout := 180 }})

'''
args=" ".join(f'(h{i} : ((compExcluded{i} x) < ({103 if i==0 else counts[i-1]} : BitVec 10)) = false)' for i in range(len(comps)))
source+=f'''theorem combinedExcludedLowerBound (x : BitVec 736)
  {args} :
  ((activeExcluded x) < (127 : BitVec 10)) = false := by
  unfold activeExcluded
'''
for i in range(len(comps)):source+=f"  unfold compExcluded{i} at h{i}\n"
source+="  bv_decide (config := { timeout := 180 })\n\n"
source+="""theorem full_736_upper_bound (x : BitVec 736)
  (h : allCovered x = true) :
  ((activeExcluded x) < (127 : BitVec 10)) = false := by
"""
for i in range(len(comps)):
 source+=f"  have hcov{i} := allToComponent{i} x h\n"
 source+=f"  have hmin{i} := compBound{i} x hcov{i}\n"
source+="  exact combinedExcludedLowerBound x " + " ".join(f"hmin{i}" for i in range(len(comps)))+"\n\n"
source+="end INSACERMO.Erdos736ByComponents\n"
out=OUT/"Erdos736Components.lean";out.write_text(source)
print("GENERATOR_SUCCESS bytes",out.stat().st_size,
      "core_edges",len(covered(comps[0])),
      "small_total_removals",sum(counts))
