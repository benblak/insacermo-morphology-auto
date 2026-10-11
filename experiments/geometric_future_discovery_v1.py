"""Independent finite graph search for INSACERMO future-safe decisions.
6 grid vertices, seven undirected edges. All simple present/future paths.
No trained model and no asserted mathematical novelty.
"""
from itertools import combinations
from collections import deque
import json

EDGES=((0,3),(0,1),(1,4),(1,2),(2,5),(3,4),(4,5))
PRESENT=(0,1)
FUTURE=(0,2)
WORLDS=(1<<0,1<<5)

def paths(start,end):
    adj=[[] for _ in range(6)]
    for k,(a,b) in enumerate(EDGES):
        adj[a].append((b,k));adj[b].append((a,k))
    found=[]
    def visit(v,visited,mask):
        if v==end:
            found.append(mask);return
        for nxt,k in adj[v]:
            if nxt not in visited:visit(nxt,visited|{nxt},mask|(1<<k))
    visit(start,{start},0)
    return tuple(sorted(set(found),key=lambda x:(x.bit_count(),x)))

P=paths(*PRESENT)
F=paths(*FUTURE)
def good(fault,path):
    return not (fault&path) and any(not (f&(fault|path)) for f in F)
def possible(faults):
    return any(all(good(w,p) for w in faults) for p in P)
def solve(worlds,depth,budget):
    worlds=tuple(sorted(set(worlds)))
    for p in P:
        if all(good(w,p) for w in worlds):return ('ACT',p)
    if depth==0:return None
    for edge in range(7):
        no=tuple(w for w in worlds if not(w&(1<<edge)))
        yes=tuple(w for w in worlds if w&(1<<edge))
        if budget>=1 and no and yes:
            a=solve(no,depth-1,budget-1);b=solve(yes,depth-1,budget-1)
            if a and b:return ('PROBE',edge,a,b)
    if budget>=2:
        for edge in range(7):
            after=tuple(w&~(1<<edge) for w in worlds)
            t=solve(after,depth-1,budget-2)
            if t:return ('REPAIR',edge,t)
    return None

def verify(tree,worlds,depth,budget):
    worlds=tuple(sorted(set(worlds)))
    if tree is None:return False
    if tree[0]=='ACT':
        return tree[1] in P and all(good(w,tree[1]) for w in worlds)
    if depth==0:return False
    if tree[0]=='PROBE':
        _,e,no,yes=tree
        if budget<1:return False
        return verify(no,[w for w in worlds if not(w&(1<<e))],depth-1,budget-1) and verify(yes,[w for w in worlds if w&(1<<e)],depth-1,budget-1)
    if tree[0]=='REPAIR':
        _,e,t=tree
        return budget>=2 and verify(t,[w&~(1<<e) for w in worlds],depth-1,budget-2)
    return False

def main():
    counts={str(b):bool(solve(WORLDS,3,b)) for b in range(6)}
    tree=solve(WORLDS,3,3)
    assert counts['0']==counts['1']==counts['2']==False
    assert counts['3']==True and verify(tree,WORLDS,3,3)
    assert not possible(WORLDS)
    assert not any(possible(tuple(w&~(1<<e) for w in WORLDS)) for e in range(7))
    assert not any(possible(group) for group in (WORLDS,))
    assert len(P)==3 and len(F)==4
    result={"edges":EDGES,"present":PRESENT,"future":FUTURE,
      "present_paths":P,"future_paths":F,"fault_masks":WORLDS,
      "probe_cost":1,"repair_cost":2,"minimum_certified_finite_budget":3,
      "feasible_budget":counts,"policy":tree,
      "scope":"finite graph, declared faults, destructive present paths, bounded 3 operations"}
    print(json.dumps(result,indent=2))
if __name__=="__main__":main()
