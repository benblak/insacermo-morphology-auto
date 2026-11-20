#!/usr/bin/env python3
"""Lean full upper bound n=736, using an external branch tree as UNTRUSTED GUIDE.
No Farkas weights, MILP optimum, numerical source, or Python certificate
are trusted: every leaf uses Lean bv_decide; Lean checks binary split coverage.
The 113-node prefix represents branch choices only, not an assumed theorem.
"""
from pathlib import Path
import itertools,collections,os
OUT=Path(os.environ.get('ERDOS_GUIDED_OUT','/tmp/erdos736-guided'))
OUT.mkdir(parents=True,exist_ok=True)
n=736
triples=[(a,b,c) for c in range(2,n+1) for b in range(1,c)
    if (b*c)%(b+c)==0 for a in [b*c//(b+c)] if 0<a<b]
assert len(triples)==742
parent=list(range(n+1))
def root(v):
 while parent[v]!=v:parent[v]=parent[parent[v]];v=parent[v]
 return v
for a,b,c in triples:
 for v in (a,b):parent[root(v)]=root(c)
parts=collections.defaultdict(list)
for v in range(1,n+1):parts[root(v)].append(v)
comps=sorted([v for v in parts.values() if len(v)>1],key=lambda z:(-len(z),z))
assert len(comps)==19 and len(comps[0])==344
core=set(comps[0])
core_edges=[t for t in triples if set(t)<=core]
assert len(core_edges)==709
def ec(verts):
 s=set(verts)
 return [t for t in triples if set(t)<=s]
def minimum_cover(vs,edges):
 for k in range(len(vs)+1):
  for ss in itertools.combinations(vs,k):
   if all(set(e)&set(ss) for e in edges):return k
 raise AssertionError
minima=[minimum_cover(v,ec(v)) for v in comps[1:]]
assert sum(minima)==24
raw='84 90 0 30 144 180 0 0 180 0 120 0 0 180 0 168 0 120 0 144 0 420 0 0 60 120 42 0 0 90 0 30 132 0 0 36 48 0 0 144 42 0 0 42 0 156 0 0 120 30 0 126 0 42 0 144 0 48 0 0 30 180 140 0 0 36 144 0 0 140 144 0 0 48 0 80 132 0 0 0 180 140 24 0 0 0 168 90 0 0 140 126 0 144 0 48 0 24 0 0 36 42 0 0 24 0 42 0 144 0 48 0 0'
words=list(map(int,raw.split()))
assert len(words)==113 and sum(bool(x) for x in words)==56
pos=0
def parse():
 global pos
 v=words[pos];pos+=1
 if v==0:return None
 assert v in core
 z=parse();o=parse()
 return (v,z,o)
tree=parse();assert pos==len(words)
def to_leaves(node,levels=[],dest=[]):
 if node is None:
  dest.append(list(levels))
  return dest
 v,z,o=node
 to_leaves(z,levels+[(v,False)],dest)
 to_leaves(o,levels+[(v,True)],dest)
 return dest
paths=to_leaves(tree,[],[])
assert len(paths)==57
def bit(v):return f"(x.getLsbD {v-1})"
def cover(name,edges):
 return 'def '+name+' (x : BitVec 736) : Bool :=\n  '+'\n  && '.join('('+bit(a)+' || '+bit(b)+' || '+bit(c)+')' for a,b,c in edges)+'\n\n'
def count(name,vs):
 return 'def '+name+' (x : BitVec 736) : BitVec 10 :=\n  ' + '\n  + '.join(['(0 : BitVec 10)']+[f'(if {bit(v)} then (1 : BitVec 10) else 0)' for v in vs])+'\n\n'
s='''import Lean

/-!
Erdos 302 736 full upper bound, compiled with bv_decide and 113-node
branch guide. All leaf conclusions are verified by Lean SAT/LRAT,
not assumed from Python or external MILP. Count is based on all 736
integers and 742 exact rational-equality forbidden triples.
-/
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000000
namespace INSACERMO.Erdos736BranchGuided

'''
s+=cover('allCovered',triples)
s+=count('activeExcluded',sorted(set(v for t in triples for v in t)))
for i,vs in enumerate(comps):
 s+=cover(f'compCovered{i}',ec(vs))
 s+=count(f'compExcluded{i}',vs)
 if i==0:
  s+='''theorem compBound0 (x : BitVec 736)
    (h : compCovered0 x = true) :
    ((compExcluded0 x) < (103 : BitVec 10)) = false := by
'''
  def tree_lines(node,depth,count):
   if node is None:
    pre='  '*depth
    return [pre+'unfold compCovered0 at h',pre+'unfold compExcluded0',
        pre+'bv_decide (config := { timeout := 120 })']
   v,z,o=node
   p='  '*depth
   lines=[p+f'by_cases hsplit{count[0]} : x.getLsbD {v-1} = true']
   count[0]+=1
   lines.append(p+'·')
   lines+=tree_lines(o,depth+1,count)
   lines.append(p+'·')
   lines+=tree_lines(z,depth+1,count)
   return lines
  s+='\n'.join(tree_lines(tree,1,[0]))+'\n\n'
 else:
  s+=f'''theorem compBound{i} (x : BitVec 736)
    (h : compCovered{i} x = true) :
    ((compExcluded{i} x) < ({minima[i-1]} : BitVec 10)) = false := by
  unfold compCovered{i} at h
  unfold compExcluded{i}
  bv_decide

'''
for i in range(len(comps)):
 s+=f'''theorem allToComponent{i} (x : BitVec 736)
    (h : allCovered x = true) : compCovered{i} x = true := by
  unfold allCovered at h
  unfold compCovered{i}
  bv_decide

'''
args=' '.join(f'(h{i} : ((compExcluded{i} x) < ({103 if i==0 else minima[i-1]} : BitVec 10)) = false)' for i in range(len(comps)))
s+=f'''theorem combinedExcludedLowerBound (x : BitVec 736)
  {args} :
  ((activeExcluded x) < (127 : BitVec 10)) = false := by
  unfold activeExcluded
'''
for i in range(len(comps)):s+=f'  unfold compExcluded{i} at h{i}\n'
s+='  bv_decide (config := { timeout := 120 })\n\n'
s+='''theorem full_736_upper_bound (x : BitVec 736)
    (h : allCovered x = true) :
    ((activeExcluded x) < (127 : BitVec 10)) = false := by
'''
for i in range(len(comps)):
 s+=f'  have hcov{i} := allToComponent{i} x h\n'
 s+=f'  have hmin{i} := compBound{i} x hcov{i}\n'
s+='  exact combinedExcludedLowerBound x '+' '.join(f'hmin{i}' for i in range(len(comps)))+'\n\n'
s+='end INSACERMO.Erdos736BranchGuided\n'
o=OUT/'Erdos736Guided.lean';o.write_text(s)
print('GUIDED_GENERATOR_SUCCESS',
    'bytes',o.stat().st_size,'nodes',len(words),
    'leaves',len(paths),'max_depth',max(map(len,paths)),
    'small_lower',sum(minima),'core_min',103)
