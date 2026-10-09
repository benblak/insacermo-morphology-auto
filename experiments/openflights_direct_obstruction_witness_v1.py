#!/usr/bin/env python3
import csv, io, json, hashlib, urllib.request
from collections import defaultdict, deque

COMMIT="7d1a611e070295dba776d6afb86e57d0d1aa1cef"
URL=f"https://raw.githubusercontent.com/jpatokal/openflights/{COMMIT}/data/routes.dat"

def fetch():
    raw=urllib.request.urlopen(URL,timeout=60).read()
    return raw,hashlib.sha256(raw).hexdigest()

def build(raw):
    adj=defaultdict(set)
    rows=0
    for r in csv.reader(io.StringIO(raw.decode("utf-8",errors="replace"))):
        if len(r)<6: continue
        s,d=r[2],r[4]
        if s and d and s!="\\N" and d!="\\N" and s!=d:
            adj[s].add(d); rows+=1
    return adj,rows

def reachable(adj,s,t,removed=None):
    removed=removed or set()
    q=deque([s]); seen={s}
    while q:
        u=q.popleft()
        for v in adj.get(u,()):
            if (u,v) in removed: continue
            if v==t:return True
            if v not in seen:
                seen.add(v);q.append(v)
    return s==t

def main():
    raw,sha=fetch()
    adj,rows=build(raw)

    witness=None
    # Structural O(E) candidate generation:
    # s has exactly one outgoing neighbor u and u has exactly one outgoing neighbor v.
    # Then e1=(s,u) and e2=(u,v) are both unavoidable on any s->v path.
    for s in sorted(adj):
        if len(adj[s])!=1: continue
        u=next(iter(adj[s]))
        if len(adj.get(u,set()))!=1: continue
        v=next(iter(adj[u]))
        if v==s: continue
        e1=(s,u); e2=(u,v)
        # Explicitly verify the two criticality claims on the real graph.
        base=reachable(adj,s,v)
        cut1=reachable(adj,s,v,{e1})
        cut2=reachable(adj,s,v,{e2})
        repair1_world1=reachable(adj,s,v,set())  # restore e1 in world e1-down
        repair1_world2=reachable(adj,s,v,{e2})   # fixed repair e1, but world e2-down
        repair2_world1=reachable(adj,s,v,{e1})   # fixed repair e2, but world e1-down
        repair2_world2=reachable(adj,s,v,set())  # restore e2 in world e2-down
        if base and not cut1 and not cut2 and repair1_world1 and repair2_world2 and not repair1_world2 and not repair2_world1:
            witness={
              "source":s,"middle":u,"target":v,
              "critical_edge_1":f"{s}->{u}",
              "critical_edge_2":f"{u}->{v}",
              "base_reachable":base,
              "world_e1_down_reachable":cut1,
              "world_e2_down_reachable":cut2,
              "fixed_repair_e1_guarantees_both_worlds":False,
              "fixed_repair_e2_guarantees_both_worlds":False,
              "adaptive_policy":{
                "probe":f"is {s}->{u} down?",
                "if_yes":f"repair {s}->{u}; ACT",
                "if_no":f"infer {u}->{v} down; repair {u}->{v}; ACT"
              }
            }
            break

    out={
      "experiment":"INSACERMO_OPENFLIGHTS_DIRECT_OBSTRUCTION_WITNESS_V1",
      "data":{"commit":COMMIT,"sha256":sha,"route_rows":rows,
              "note":"Real OpenFlights directed route topology; the two failure worlds are synthetic single-edge failures."},
      "method":"Direct structural search for two serial unavoidable edges; no planner, no exhaustive failure search.",
      "witness":witness,
      "status":"PASS" if witness else "NO_WITNESS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("OPENFLIGHTS_DIRECT_OBSTRUCTION_WITNESS_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
