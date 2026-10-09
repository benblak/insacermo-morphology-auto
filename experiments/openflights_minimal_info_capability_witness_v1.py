#!/usr/bin/env python3
import csv, io, json, hashlib, urllib.request
from collections import deque

COMMIT="7d1a611e070295dba776d6afb86e57d0d1aa1cef"
URL=f"https://raw.githubusercontent.com/jpatokal/openflights/{COMMIT}/data/routes.dat"
AIRPORTS=("CDG","ORY","NTE","RNS","BES","BOD","TLS","LIL","LYS","MPL","NCE","SXB","BIQ","CFE","PIS","LRT","MRS","GVA","BRU","LUX")

def fetch():
    raw=urllib.request.urlopen(URL,timeout=60).read()
    return raw,hashlib.sha256(raw).hexdigest()

def graph(raw):
    adj={a:set() for a in AIRPORTS}
    for r in csv.reader(io.StringIO(raw.decode("utf-8",errors="replace"))):
        if len(r)<6: continue
        s,d=r[2],r[4]
        if s in adj and d in adj and s!=d:
            adj[s].add(d)
    return adj

def reachable(adj,s,t,down=frozenset()):
    q=deque([s]);seen={s}
    while q:
        u=q.popleft()
        if u==t:return True
        for v in adj[u]:
            if (u,v) in down:continue
            if v not in seen:
                seen.add(v);q.append(v)
    return False

def one_path(adj,s,t,down=frozenset()):
    q=deque([s]);prev={s:None}
    while q:
        u=q.popleft()
        if u==t:break
        for v in sorted(adj[u]):
            if (u,v) in down or v in prev:continue
            prev[v]=u;q.append(v)
    if t not in prev:return None
    p=[];x=t
    while x is not None:
        p.append(x);x=prev[x]
    return list(reversed(p))

def all_edges(adj):
    return sorted((u,v) for u in adj for v in adj[u])

def main():
    raw,sha=fetch();adj=graph(raw);edges=all_edges(adj)
    witnesses=[]
    for s in AIRPORTS:
        for t in AIRPORTS:
            if s==t or not reachable(adj,s,t):continue
            critical=[e for e in edges if not reachable(adj,s,t,frozenset([e]))]
            if len(critical)<2:continue
            # smallest lexicographic pair, fixed deterministic choice
            e1,e2=critical[0],critical[1]
            worlds=[frozenset([e1]),frozenset([e2])]

            probe_only_impossible=all(not reachable(adj,s,t,w) for w in worlds)

            # fixed one-edge repair must choose a single edge before observation
            fixed_repairs=[]
            for r in (e1,e2):
                ok=all(reachable(adj,s,t,frozenset(set(w)-{r})) for w in worlds)
                if ok:fixed_repairs.append(r)
            repair_only_impossible=(len(fixed_repairs)==0)

            # contingent policy: probe e1. If DOWN repair e1; if UP, exact-one-failure
            # contract identifies world e2, so repair e2.
            branch_down=reachable(adj,s,t,frozenset())
            branch_up=reachable(adj,s,t,frozenset())
            mixed_succeeds=branch_down and branch_up

            if probe_only_impossible and repair_only_impossible and mixed_succeeds:
                witnesses.append({
                    "source":s,"target":t,
                    "critical_edges":[f"{e1[0]}->{e1[1]}",f"{e2[0]}->{e2[1]}"],
                    "baseline_path":one_path(adj,s,t),
                    "worlds":[f"DOWN {e1[0]}->{e1[1]}",f"DOWN {e2[0]}->{e2[1]}"],
                    "probe_only":"IMPOSSIBLE",
                    "repair_only":"IMPOSSIBLE",
                    "mixed_policy":[
                        f"PROBE {e1[0]}->{e1[1]}",
                        f"if DOWN: REPAIR {e1[0]}->{e1[1]} then ACT",
                        f"if UP: infer {e2[0]}->{e2[1]} DOWN, REPAIR it, then ACT"
                    ],
                    "mixed_result":"GUARANTEED"
                })

    out={
      "experiment":"INSACERMO_OPENFLIGHTS_MINIMAL_INFO_CAPABILITY_WITNESS_V1",
      "data":{"commit":COMMIT,"sha256":sha,"airports":AIRPORTS,
              "note":"Real OpenFlights topology; failure worlds are synthetic exactly-one-edge failures."},
      "criterion":"Two distinct source-target critical directed edges. Worlds are exactly one of those two edges down.",
      "theory":{
        "probe_only":"fails because each world is physically disconnected",
        "repair_only":"fails because a fixed repair can restore at most one of the two distinct failed edges",
        "mixed":"probe one edge; repair it if down, otherwise infer and repair the other"
      },
      "witness_count":len(witnesses),
      "first_witness":witnesses[0] if witnesses else None,
      "top10":witnesses[:10],
      "status":"PASS" if witnesses else "NO_WITNESS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    open("OPENFLIGHTS_MINIMAL_INFO_CAPABILITY_WITNESS_V1.json","w").write(json.dumps(out,indent=2,sort_keys=True))

if __name__=="__main__":main()
