#!/usr/bin/env python3
"""INSACERMO V7 — exact adaptive sensing for contract reachability.

NO machine learning. Actual graph data: pinned OpenFlights. Existing V3 samples
are reused unchanged (240 reachable pairs + 240 directly linked pairs).
This planner applies to the binary ACT/REFUSE contract, at most TWO failed
directed edges, and perfect binary individual-edge probes.

A graph algorithm derives minimal cuts and the exact P2 decision quotient.
The policy is computed independently by minimax Bellman on observation fibers.
It is NOT the complete INSACERMO MAX TOTAL runtime or a Lean kernel proof.
"""
import json,os,random
from functools import lru_cache
from openflights_failure_budget_min_probes_v3 import load,samples
from openflights_blind_dual_failure_v2 import derive,path

def basis_of(d):
    cuts=[frozenset((e,)) for e in d["singles"]]
    cuts += [frozenset(p) for p in d["minimal_pairs"]]
    b=tuple(sorted(set().union(*cuts))) if cuts else ()
    return cuts,b

def quotient(cuts,basis):
    m=len(basis)
    emap={e:i for i,e in enumerate(basis)}
    cuts_as_masks=tuple(sum(1<<emap[x] for x in cut) for cut in cuts)
    masks=(0,)+tuple(1<<i for i in range(m))+tuple(
        (1<<i)|(1<<j) for i in range(m) for j in range(i+1,m))
    labels=tuple(any((mask & c)==c for c in cuts_as_masks) for mask in masks)
    return masks,labels

def policy(masks, labels, m):
    n=len(masks); full=(1<<n)-1
    down=[sum(1<<j for j,w in enumerate(masks) if w & (1<<i)) for i in range(m)]
    failures=sum(1<<j for j,a in enumerate(labels) if a)
    picked={}
    @lru_cache(None)
    def bellman(S):
        if not(S & failures) or not(S & (full ^ failures)):return 0
        best=m+1
        candidate=None
        for p in range(m):
            d=S&down[p]; u=S&(full^down[p])
            if not d or not u:continue
            v=1+max(bellman(d),bellman(u))
            if v<best:best=v;candidate=p
        if candidate is None:raise AssertionError("UNSEPARABLE")
        picked[S]=candidate
        return best
    depth=bellman(full)
    def tree(S):
        if bellman(S)==0:
            yes=bool(S & failures)
            assert not(yes and (S & (full ^ failures)))
            return {"decision":"REFUSE" if yes else "ACT"}
        p=picked[S]
        return {"probe":p,"up":tree(S&(full ^down[p])),"down":tree(S&down[p])}
    result=tree(full)
    return depth,result,bellman.cache_info().currsize

def execute(tree,failed_mask):
    depth=0
    while "probe" in tree:
        tree=tree["down"] if failed_mask & (1<<tree["probe"]) else tree["up"]
        depth+=1
    return tree["decision"],depth

def own_oracle_small():
    randomizer=random.Random(841)
    count=0
    for m in range(1,5):
        masks=tuple(range(1<<m))
        for _ in range(35):
            labels=tuple(bool(randomizer.getrandbits(1)) for _ in masks)
            depth,t,_=policy(masks,labels,m)
            @lru_cache(None)
            def feasible(worldindices,budget):
                if len({labels[i] for i in worldindices})<=1:return True
                if budget==0:return False
                for p in range(m):
                    a=tuple(i for i in worldindices if masks[i]&(1<<p))
                    b=tuple(i for i in worldindices if not(masks[i]&(1<<p)))
                    if a and b and feasible(a,budget-1) and feasible(b,budget-1):
                        return True
                return False
            W=tuple(range(len(masks)))
            assert feasible(W,depth)
            assert depth==0 or not feasible(W,depth-1)
            for mask,label in zip(masks,labels):
                assert (execute(t,mask)[0]=="REFUSE")==label
            count+=1
    return count

def main():
    selftests=own_oracle_small()
    edges,adj,rows,digest=load()
    rng=random.Random(840212)
    groups=samples(adj,edges)
    out={
        "experiment":"INSACERMO_OPENFLIGHTS_ADAPTIVE_SENSING_V7",
        "status":"PASS",
        "run_commit":os.getenv("GITHUB_SHA","not-github"),
        "data_sha256":digest,
        "contract":"ACT iff reachable, else REFUSE, under zero to two directed edge outages",
        "observations":"perfect individual binary edge-status, adaptive probes",
        "proof":"Bellman recursion over finite observation fibers computes exact minimax worst-case depth; independent depth-limited decision-tree oracle verifies small random problems",
        "small_independent_feasibility_oracle_tests":selftests,
        "cohorts":{}}
    for name,cohort in groups.items():
        outcomes=[]
        samplesout=[]
        total_oracles=0
        max_states=0
        for s,t in cohort:
            d=derive(adj,s,t)
            assert d is not None
            cuts,b=basis_of(d)
            m=len(b)
            masks,labels=quotient(cuts,b)
            depth,tree,states=policy(masks,labels,m)
            assert depth<=m,(s,t,depth,m)
            max_states=max(max_states,states)
            for mask,label in zip(masks,labels):
                predicted,used=execute(tree,mask)
                assert (predicted=="REFUSE")==label
                assert used<=depth
                down=frozenset(e for i,e in enumerate(b) if mask&(1<<i))
                assert (path(adj,s,t,down) is None)==label
                total_oracles+=1
            fs=[frozenset(),*cuts]
            for _ in range(24):
                k=rng.randrange(3)
                fs.append(frozenset(rng.sample(edges,k)))
            for F in fs:
                mask=sum(1<<i for i,e in enumerate(b) if e in F)
                predicted,_=execute(tree,mask)
                assert (predicted=="REFUSE")==(path(adj,s,t,F) is None)
                total_oracles+=1
            row={"source":s,"target":t,"fixed_minimum":m,
                 "adaptive_minimax":depth,"saving":m-depth,
                 "minimal_cut_1":len(d["singles"]),
                 "minimal_cut_2":len(d["minimal_pairs"])}
            outcomes.append(row)
            if (len(samplesout)<8 and m>depth):
                samplesout.append({**row,
                    "probe_basis":[f"{a}->{z}" for a,z in b],
                    "optimal_tree":tree})
        n=len(outcomes)
        out["cohorts"][name]={
            "contracts_tested":n,
            "fixed_probe_total":sum(row["fixed_minimum"] for row in outcomes),
            "adaptive_worstcase_probe_total":sum(row["adaptive_minimax"] for row in outcomes),
            "mean_fixed_probes":sum(row["fixed_minimum"] for row in outcomes)/n,
            "mean_adaptive_worstcase":sum(row["adaptive_minimax"] for row in outcomes)/n,
            "contracts_strictly_improved":sum(row["saving"]>0 for row in outcomes),
            "contracts_unimproved":sum(row["saving"]==0 for row in outcomes),
            "max_saving":max(row["saving"] for row in outcomes),
            "max_bellman_states":max_states,
            "independent_full_graph_oracle_checks":total_oracles,
            "example_improvements":samplesout}
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("INSACERMO_OPENFLIGHTS_ADAPTIVE_SENSING_V7.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":main()
