#!/usr/bin/env python3
from __future__ import annotations
import itertools, json, sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from insacermo_actionability_engine_v1 import FiniteContract, audit_observation

HERE=Path(__file__).resolve().parent
T=json.loads((HERE/"tablet.json").read_text())
N=T["n"]; V=tuple(range(N)); TARGET=T["target"]

def ce(a,b): return (a,b) if a<b else (b,a)

def auts(edges):
    E={ce(*e) for e in edges}
    out=[]
    for p in itertools.permutations(V):
        ok=True
        for a in range(N):
            for b in range(a+1,N):
                if ((a,b) in E) != (ce(p[a],p[b]) in E):
                    ok=False; break
            if not ok: break
        if ok: out.append(p)
    return out

def local_sig(edges,v):
    E={ce(*e) for e in edges}
    nbr={x:set() for x in V}
    for a,b in E:
        nbr[a].add(b); nbr[b].add(a)
    return (len(nbr[v]), tuple(sorted(len(nbr[u]) for u in nbr[v])))

def connected(edges):
    nbr={x:set() for x in V}
    for a,b in map(lambda e:ce(*e),edges):
        nbr[a].add(b); nbr[b].add(a)
    seen={0}; stack=[0]
    while stack:
        x=stack.pop()
        for y in nbr[x]-seen:
            seen.add(y); stack.append(y)
    return len(seen)==N

def engine_status(A):
    worlds=tuple(range(len(A)))
    actions=V
    c=FiniteContract(
        worlds=worlds,
        actions=actions,
        available=frozenset(actions),
        admissible_pairs=frozenset((i,A[i][TARGET]) for i in worlds)
    )
    audit=audit_observation(c,{i:"tablet" for i in worlds})
    common=list(audit.fibers[0].common_actions)
    return audit.status,common

def main():
    edges=[tuple(e) for e in T["edges"]]
    A=auts(edges)
    orbit=sorted({p[TARGET] for p in A})
    status,common=engine_status(A)

    sig=local_sig(edges,TARGET)
    local_lookalikes=[v for v in V if local_sig(edges,v)==sig]

    damage=tuple(T["frozen_damage_remove"])
    damaged=[e for e in edges if ce(*e)!=ce(*damage)]
    if not connected(damaged):
        raise RuntimeError("Frozen damage disconnected tablet")
    AD=auts(damaged)
    orbitD=sorted({p[TARGET] for p in AD})
    statusD,commonD=engine_status(AD)

    critical=[]
    for e in edges:
        d=[x for x in edges if ce(*x)!=ce(*e)]
        if not connected(d): continue
        aa=auts(d)
        oo=sorted({p[TARGET] for p in aa})
        if len(oo)>1:
            critical.append({"removed_edge":list(e),"aut_count":len(aa),"target_orbit":oo})

    result={
      "protocol":"INSACERMO BLACK TABLET V1",
      "vertices":N,
      "edges":len(edges),
      "automorphism_count":len(A),
      "target_orbit":orbit,
      "engine_intact_status":status,
      "engine_intact_common_actions":common,
      "target_local_signature":[sig[0],list(sig[1])],
      "local_lookalikes":local_lookalikes,
      "frozen_damage":{"remove":list(damage),"automorphism_count":len(AD),
                       "target_orbit":orbitD,"engine_status":statusD,
                       "common_actions":commonD},
      "single_edge_critical_relations":critical,
      "pass": (
        len(A)>1 and orbit==[TARGET] and len(local_lookalikes)>=3
        and status=="ACT" and len(orbitD)>1 and statusD=="REFUSE"
        and len(critical)>=1
      )
    }
    (HERE/"results.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")

    art=[
      "INSACERMO BLACK TABLET V1",
      "",
      "Transmit only seven anonymous marks and these twelve undirected relations:",
      "",
      "0--2  0--4  0--5  0--6",
      "1--2  1--3  1--5",
      "2--4  2--6",
      "3--4  3--6",
      "4--5",
      "",
      "The numerals above are printing conveniences only; the object is the unlabeled graph.",
      "",
      f"Exact automorphisms: {len(A)}",
      f"Target orbit: {orbit}",
      f"Local lookalikes of target by degree+neighbor-degree signature: {local_lookalikes}",
      f"Engine on intact tablet: {status}",
      "",
      f"Delete relation {damage}: target orbit becomes {orbitD}; engine => {statusD}.",
      "",
      "Interpretation: the referent is globally fixed even though full decoding is not unique",
      "and local cues do not isolate it. One critical missing relation destroys that guarantee.",
      ""
    ]
    (HERE/"BLACK_TABLET.txt").write_text("\n".join(art))

    print(json.dumps(result,sort_keys=True))
    if not result["pass"]: raise SystemExit(1)

if __name__=="__main__": main()
