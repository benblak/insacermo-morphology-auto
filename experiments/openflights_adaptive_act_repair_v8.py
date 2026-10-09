#!/usr/bin/env python3
"""V8 exact adaptive sensing with deterministic ACT / REPAIR decisions.

Historical OpenFlights real directed graph, max 2 failed edges (0,1,2).
Cut-based structural adapter yields the exact relevant probe basis.
Full graph semantics independently yields an optimal (minimum count) repair
action in each world, with lexical tie-break. A domain-agnostic Bellman
minimax optimizer chooses next probe until the action is uniquely determined.

IMPORTANT: not the complete INSACERMO MAX TOTAL planner; no Lean proof here.
"""
import json,os,random,itertools
from functools import lru_cache
from openflights_failure_budget_min_probes_v3 import load,samples
from openflights_adaptive_sensing_v7 import basis_of, quotient
from openflights_blind_dual_failure_v2 import derive, path

def action(adj,s,t,failed):
    if path(adj,s,t,failed) is not None:
        return "ACT"
    failed=tuple(sorted(failed))
    for n in range(1,len(failed)+1):
        for repairs in itertools.combinations(failed,n):
            remaining=frozenset(e for e in failed if e not in repairs)
            if path(adj,s,t,remaining) is not None:
                return "REPAIR:"+",".join(f"{a}->{b}" for a,b in repairs)
    return "REFUSE"

def optimize(masks,actions,nprobes):
    count=len(masks);full=(1<<count)-1
    probe_yes=[sum(1<<i for i,w in enumerate(masks) if w & (1<<k)) for k in range(nprobes)]
    # bitmask of each action class
    groups={}
    for i,act in enumerate(actions):
        groups[act]=groups.get(act,0)|(1<<i)
    classes=tuple(groups.values())
    picks={}
    @lru_cache(None)
    def cost(S):
        if any(S & C==S for C in classes):return 0
        best=nprobes+1
        chosen=None
        for p,Y in enumerate(probe_yes):
            down=S&Y; up=S&(full^Y)
            if not down or not up:continue
            c=1+max(cost(down),cost(up))
            if c<best:
                chosen=p;best=c
        if chosen is None:
            raise AssertionError("IMPOSSIBLE_TO_DISTINGUISH")
        picks[S]=chosen
        return best
    root=cost(full)
    def build(S):
        if cost(S)==0:
            i=(S & -S).bit_length()-1
            label=actions[i]
            assert all(actions[j]==label for j in range(count) if S&(1<<j))
            return {"action":label}
        k=picks[S]
        return {"probe":k,"down":build(S&probe_yes[k]),
                "up":build(S&(full^probe_yes[k]))}
    return root,build(full),cost.cache_info().currsize

def replay(tree,mask):
    k=0
    while "probe" in tree:
        p=tree["probe"];k+=1
        tree=tree["down"] if mask&(1<<p) else tree["up"]
    return tree["action"],k

def independent_small_oracle():
    rng=random.Random(20261009)
    checked=0
    for m in range(1,5):
        masks=tuple(range(1<<m))
        for _ in range(35):
            actions=tuple(rng.randrange(4) for _ in masks)
            depth,tree,_=optimize(masks,actions,m)
            @lru_cache(None)
            def possible(worlds,budget):
                if len({actions[i] for i in worlds})==1:return True
                if budget==0:return False
                for p in range(m):
                    down=tuple(i for i in worlds if masks[i]&(1<<p))
                    up=tuple(i for i in worlds if not(masks[i]&(1<<p)))
                    if down and up and possible(down,budget-1) and possible(up,budget-1):
                        return True
                return False
            W=tuple(range(len(masks)))
            assert possible(W,depth) and (depth==0 or not possible(W,depth-1))
            assert all(replay(tree,mask)[0]==lab for mask,lab in zip(masks,actions))
            checked+=1
    return checked

def run():
    small=independent_small_oracle()
    edges,adj,rows,sha=load()
    rng=random.Random(88022)
    cohorts=samples(adj,edges)
    out={
      "experiment":"INSACERMO_OPENFLIGHTS_ADAPTIVE_ACT_REPAIR_V8",
      "status":"PASS",
      "sha256":sha,
      "contract":"At most two distinct route failures; guarantee binary connectivity by ACT if connected, otherwise repair a minimum-cardinality set of actually failed edges with deterministic lexicographic tie-break, then ACT",
      "cost":"Minimize worst-case number of perfect one-edge probes, contingent on required repair action; repair actions use unit edge count",
      "small_independent_depth_oracle_cases":small,
      "run_sha":os.getenv("GITHUB_SHA","unknown"),
      "cohorts":{}
    }
    for name,contracts in cohorts.items():
        records=[];improved=[];global_checks=0;worst_states=0
        for s,t in contracts:
            d=derive(adj,s,t)
            assert d is not None
            cuts,b=basis_of(d)
            masks,_=quotient(cuts,b)
            labels=tuple(action(adj,s,t,frozenset(e for i,e in enumerate(b) if M & (1<<i)))
                         for M in masks)
            depth,tree,states=optimize(masks,labels,len(b))
            assert depth<=len(b)
            worst_states=max(worst_states,states)
            for M,label in zip(masks,labels):
                actual,steps=replay(tree,M)
                assert actual==label and steps<=depth
                global_checks+=1
            # Cut-signature semantics is independently checked in the ORIGINAL
            # graph on every cut + 24 random global failure worlds.
            fs=[frozenset(),*cuts]
            for _ in range(24):
                fs.append(frozenset(rng.sample(edges,rng.randrange(3))))
            for F in fs:
                mask=sum(1<<i for i,e in enumerate(b) if e in F)
                predicted,_=replay(tree,mask)
                verified=action(adj,s,t,F)
                assert predicted==verified,(s,t,F,predicted,verified)
                global_checks+=1
            record={"source":s,"target":t,"fixed_probes":len(b),
                    "adaptive_minimax_probes":depth,
                    "saving":len(b)-depth,
                    "observed_action_count":len(set(labels)),
                    "minimal_single_cuts":len(d["singles"]),
                    "minimal_double_cuts":len(d["minimal_pairs"])}
            records.append(record)
            if depth<len(b) and len(improved)<6:
                improved.append({**record,"basis":[f"{a}->{z}" for a,z in b],"policy":tree})
        out["cohorts"][name]={
            "contracts":len(contracts),
            "fixed_minimal_probe_total":sum(x["fixed_probes"] for x in records),
            "adaptive_minimax_probe_total":sum(x["adaptive_minimax_probes"] for x in records),
            "strictly_improved_contracts":sum(x["saving"]>0 for x in records),
            "largest_saving":max(x["saving"] for x in records),
            "max_bellman_states":worst_states,
            "independent_original_graph_checks":global_checks,
            "examples":improved}
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("INSACERMO_OPENFLIGHTS_ADAPTIVE_ACT_REPAIR_V8.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":run()
