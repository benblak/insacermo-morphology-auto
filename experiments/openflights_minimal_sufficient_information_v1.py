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
    edges=set()
    rows=0
    for r in csv.reader(io.StringIO(raw.decode("utf-8",errors="replace"))):
        if len(r)<6: continue
        s,d=r[2],r[4]
        if s and d and s!="\\N" and d!="\\N" and s!=d:
            adj[s].add(d); edges.add((s,d)); rows+=1
    return adj,tuple(sorted(edges)),rows

def reachable(adj,s,t,removed=frozenset()):
    if s==t:return True
    q=deque([s]);seen={s}
    while q:
        u=q.popleft()
        for v in adj.get(u,()):
            if (u,v) in removed:continue
            if v==t:return True
            if v not in seen:
                seen.add(v);q.append(v)
    return False

def forced_chain(adj,start):
    out=[start];seen={start};cur=start
    while len(adj.get(cur,set()))==1:
        nxt=next(iter(adj[cur]))
        if nxt in seen:break
        out.append(nxt);seen.add(nxt);cur=nxt
    return tuple(out)

def main():
    raw,sha=fetch();adj,edges,rows=build(raw)

    # Stage 1: blindly rediscover the strongest forced-chain witness.
    cands=[]
    for s in sorted(adj):
        c=forced_chain(adj,s)
        if len(c)>=3:cands.append(c)
    cands.sort(key=lambda c:(len(c),c),reverse=True)

    chosen=None
    for c in cands:
        s,t=c[0],c[-1]
        ce=tuple(zip(c[:-1],c[1:]))
        if reachable(adj,s,t) and all(not reachable(adj,s,t,frozenset([e])) for e in ce):
            chosen=(c,ce);break

    if chosen is None:
        out={"status":"NO_WITNESS"}
    else:
        chain,chain_edges=chosen
        s,t=chain[0],chain[-1]

        # Stage 2: universe is EVERY unique real route as the exactly-one failed edge.
        # Compute the contract-relevant obstruction basis directly:
        # an edge matters iff its single failure breaks s->t reachability.
        critical=[]
        for e in edges:
            if not reachable(adj,s,t,frozenset([e])):
                critical.append(e)

        # For individual edge-status probes, every critical edge is necessary:
        # if e is never probed, world "e down" and a world with an irrelevant edge down
        # produce identical observations on all other critical probes but require
        # different decisions (REPAIR e vs ACT). All critical probes are sufficient:
        # if one is down repair it; if all are up, the unique failed edge is irrelevant.
        k=len(critical)
        irrelevant=len(edges)-k
        exact_min_probes=k if irrelevant>0 else max(0,k-1)

        chain_set=set(chain_edges)
        all_chain_critical=chain_set.issubset(set(critical))

        out={
          "experiment":"INSACERMO_OPENFLIGHTS_MINIMAL_SUFFICIENT_INFORMATION_V1",
          "data":{
            "commit":COMMIT,
            "sha256":sha,
            "route_rows":rows,
            "unique_directed_edges":len(edges),
            "failure_universe":"exactly one unique directed route is down"
          },
          "blind_discovery":{
            "selected_source":s,
            "selected_target":t,
            "forced_chain":chain,
            "forced_chain_edges":[f"{a}->{b}" for a,b in chain_edges],
            "candidate_forced_chains":len(cands)
          },
          "contract":"Guarantee source-to-target reachability; ACT if the failed edge is irrelevant, otherwise repair the failed critical edge then ACT.",
          "derived_minimal_information":{
            "critical_edge_count":k,
            "critical_edges":[f"{a}->{b}" for a,b in critical],
            "irrelevant_failure_edges":irrelevant,
            "all_discovered_chain_edges_are_critical":all_chain_critical,
            "minimum_individual_edge_status_probes_worst_case":exact_min_probes,
            "sufficiency_reason":"Probe every critical edge. If one is down, repair it; if all are up, the unique failure is outside the critical basis and ACT is safe.",
            "necessity_reason":"Omitting any critical edge makes its failure indistinguishable, on the remaining critical probes, from some irrelevant-edge failure that requires ACT instead of repairing that critical edge."
          },
          "compression":{
            "raw_possible_failure_edges":len(edges),
            "contract_relevant_edges":k,
            "fraction_relevant": (k/len(edges)) if edges else None,
            "compression_factor_edges_per_relevant_probe": (len(edges)/k) if k else None
          },
          "no_ml":{
            "training":False,
            "fitted_parameters":False,
            "labels":False,
            "statistical_generalization":False,
            "method":"exact contract-relative obstruction discovery and proof of probe necessity/sufficiency"
          },
          "status":"PASS" if k>=2 and all_chain_critical else "CHECK"
        }

    print(json.dumps(out,indent=2,sort_keys=True))
    with open("OPENFLIGHTS_MINIMAL_SUFFICIENT_INFORMATION_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
