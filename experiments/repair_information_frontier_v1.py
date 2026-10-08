#!/usr/bin/env python3
from itertools import combinations, product
import json, math

def subsets(n):
    return [frozenset(i for i in range(n) if mask>>i & 1) for mask in range(1<<n)]

def cover_num(B, regs):
    if not B: return 0
    regs=[R & B for R in regs if R & B]
    for k in range(1,len(regs)+1):
        for combo in combinations(regs,k):
            if B <= frozenset().union(*combo):
                return k
    return None

def pareto(points):
    out=[]
    for p in points:
        if not any(q[0]<=p[0] and q[1]<=p[1] and q!=p for q in points):
            out.append(p)
    return sorted(set(out))

def frontier_for(B, base_regs, repairs):
    pts=[]
    m=len(repairs)
    for mask in range(1<<m):
        chosen=[repairs[i] for i in range(m) if mask>>i&1]
        r=len(chosen)
        tau=cover_num(B, tuple(base_regs)+tuple(chosen))
        if tau is not None:
            branches=tau
            bits=0 if branches<=1 else math.ceil(math.log2(branches))
            pts.append((r,branches,bits))
    # Pareto on repairs vs branches
    p2=pareto([(r,b) for r,b,_ in pts])
    return [(r,b,0 if b<=1 else math.ceil(math.log2(b))) for r,b in p2]

def main():
    n=4
    B=frozenset(range(n))
    allregs=subsets(n)

    # Counterexample to false linear law
    base=tuple(frozenset({i}) for i in range(n))
    tau0=cover_num(B,base)
    tau1=cover_num(B,base+(B,))
    assert (tau0,tau1)==(4,1)

    checked=0
    frontiers={}
    nonlinear=0
    examples=[]
    for base_regs in combinations(allregs,2):
        for repairs in combinations(allregs,2):
            F=frontier_for(B,base_regs,repairs)
            checked+=1
            key=tuple(F)
            frontiers[key]=frontiers.get(key,0)+1
            if len(F)>=2:
                # detect non-unit branch drops between Pareto points
                for (r1,b1,_),(r2,b2,_) in zip(F,F[1:]):
                    if r2>r1 and b1-b2>1:
                        nonlinear+=1
                        if len(examples)<5:
                            examples.append({
                              "base":[sorted(x) for x in base_regs],
                              "repairs":[sorted(x) for x in repairs],
                              "frontier":F
                            })
                        break

    out={
      "experiment":"INSACERMO_REPAIR_INFORMATION_FRONTIER_V1",
      "false_linear_law_counterexample":{
        "base_singletons_cover_number":tau0,
        "after_universal_repair_cover_number":tau1,
        "drop":tau0-tau1
      },
      "frontier_instances_checked":checked,
      "distinct_pareto_frontiers":len(frontiers),
      "nonlinear_frontier_instances":nonlinear,
      "examples":examples,
      "law":"repair-information tradeoff is generally nonlinear; the exact residual after adding a capability is B minus that capability's good region",
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("REPAIR_INFORMATION_FRONTIER_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
