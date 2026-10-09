#!/usr/bin/env python3
"""INSACERMO V6: declared raw-data contract -> semantic evaluation -> automatic
one-hot probe discovery -> independent generic-world action certificate.

No pre-identified critical edges or stored action labels are accepted as input.
Requires an explicit domain interpretation for 'reachability' (BFS below).
The generic information-price verifier is unchanged.
"""
from __future__ import annotations
from collections import defaultdict, deque
import csv
import hashlib
import io
import json
import os
import pathlib
import sys
import urllib.request

from generic_onehot_contract_optimizer_v1 import solve, verify_lower_bound, exhaustive_selftest
from information_price_runtime_v1 import verify_certificate

DATA_URL="https://raw.githubusercontent.com/jpatokal/openflights/7d1a611e070295dba776d6afb86e57d0d1aa1cef/data/routes.dat"
DATA_HASH="bd373706238134f619c624c606dccc74c05c2582a977c489c81de501735f2390"

def read_edges():
    raw=urllib.request.urlopen(DATA_URL,timeout=60).read()
    sha=hashlib.sha256(raw).hexdigest()
    if sha!=DATA_HASH:raise ValueError("DATA_HASH_MISMATCH:"+sha)
    edges=set()
    rows=0
    for row in csv.reader(io.StringIO(raw.decode("utf-8",errors="replace"))):
        if len(row)<6:continue
        s,t=row[2],row[4]
        if s and t and s!=r"\N" and t!=r"\N" and s!=t:
            edges.add((s,t));rows+=1
    edges=tuple(sorted(edges))
    adj=defaultdict(list)
    for s,t in edges:adj[s].append(t)
    return edges,adj,rows,sha

def eval_relation_closure(relation, source, target, removed):
    """Fixed-point evaluator for transitive closure of a binary relation.

    Not a specialized minimum-cut/critical-edge solver. It is a deliberate
    domain-semantic built-in required to interpret a reachability contract.
    """
    if source==target:return True
    q=deque([source]);seen={source}
    while q:
        x=q.popleft()
        for y in relation.get(x,()):
            if (x,y) in removed:continue
            if y==target:return True
            if y not in seen:
                seen.add(y);q.append(y)
    return False

def contract_actions(contract,edges,adj):
    assert contract["semantics"]=="directed_transitive_closure"
    assert contract["failure_budget"]==1
    assert contract["failure_quantifier"]=="exactly"
    assert contract["observer"]=="perfect_individual_edge_failure"
    assert contract["decision_rule"]=="ACT_IF_REACHABLE_ELSE_REPAIR_FAILED_EDGE"
    s,t=contract["source"],contract["target"]
    if not eval_relation_closure(adj,s,t,frozenset()):
        raise ValueError("CONTRACT_UNSAT_BASELINE")
    actions=[]
    for edge in edges:
        failed=frozenset((edge,))
        if eval_relation_closure(adj,s,t,failed):
            actions.append("ACT")
        else:
            # This is a property of the declared one-edge failure world:
            # repairing that failed edge restores the baseline graph.
            assert eval_relation_closure(adj,s,t,frozenset())
            actions.append("REPAIR:"+edge[0]+"->"+edge[1])
    return tuple(actions)

def check_contract(contract, edges, adj):
    actions=contract_actions(contract,edges,adj)
    chosen=solve(edges,actions)   # NO candidate probes supplied
    assert verify_lower_bound(edges,actions,chosen)
    observed=lambda probe,world: probe==world
    lookup=dict(zip(edges,actions))
    required=lambda world:lookup[world]
    critical_idx=[i for i,a in enumerate(actions) if a!="ACT"]
    act_idx=next((i for i,a in enumerate(actions) if a=="ACT"),None)
    checked=[]
    for i in ([act_idx] if act_idx is not None else [])+critical_idx:
        world=edges[i]
        signature=tuple(observed(p,world) for p in chosen.probes)
        verdict=verify_certificate(edges,i,chosen.probes,observed,required,
                         claimed_action=actions[i],claimed_outcomes=signature,
                         claimed_price=chosen.minimum_count)
        assert verdict.valid,(contract,world,verdict)
        checked.append({"failed_edge":f"{world[0]}->{world[1]}",
                        "action":actions[i],"certificate":"PASS"})
    # The generic verifier rejects every omitted necessary observation
    # via a counterexample. The lower bound comes from one-hot classes.
    for p in chosen.probes:
        idx=edges.index(p)
        less=tuple(x for x in chosen.probes if x!=p)
        vr=verify_certificate(edges,idx,less,observed,required)
        assert not vr.valid,(contract,p,"DELETED_NECESSARY_PROBE_STILL_ACCEPTED")
    # Domain-semantic confirmation that the automatically selected
    # edges are exactly the ones causing a contract violation.
    for e in chosen.probes:
        assert not eval_relation_closure(adj,contract["source"],contract["target"],frozenset((e,)))
    return {
        "contract":contract,"worlds":len(edges),"action_classes":chosen.distinct_actions,
        "discovered_minimal_fixed_probes":[f"{a}->{b}" for a,b in chosen.probes],
        "minimum_fixed_per_edge_probes":chosen.minimum_count,
        "maximum_unobserved_equivalent_world_class":chosen.largest_action_class,
        "independent_generic_certificate_checks":checked,
        "each_indispensable_probe_deletion_refused":True,
        "status":"PASS"
    }

def main():
    source=pathlib.Path(sys.argv[1] if len(sys.argv)>1 else
                       "experiments/openflights_raw_contracts_v6.json")
    doc=json.loads(source.read_text(encoding="utf-8"))
    if doc.get("protocol")!="INSACERMO_DECLARED_RELATION_CONTRACT_V6":
        raise ValueError("BAD_PROTOCOL")
    # User-declared source-target contracts are pinned before examining
    # their failure sensitivity. STZ is a historical regression case,
    # other cases were chosen ahead of the test.
    cases=doc["contracts"]
    assert len(cases)>=4 and len({(c["source"],c["target"]) for c in cases})==len(cases)
    small=exhaustive_selftest()
    edges,adj,rows,sha=read_edges()
    assert len(edges)==37594
    results=[]
    for c in cases:
        results.append(check_contract(c,edges,adj))
    out={
        "experiment":"INSACERMO_RAW_CONTRACT_TO_CERTIFICATES_V6",
        "status":"PASS",
        "run_sha":os.getenv("GITHUB_SHA","unavailable"),
        "data":{"url":DATA_URL,"sha256":sha,"raw_rows":rows,"unique_edges":len(edges)},
        "engine_steps":["read_and_hash_raw_dataset","interpret_declared_binary_relation",
            "enumerate_exactly_one_failed_edge","evaluate_transitive_closure",
            "derive_action_table","discover_minimal_onehot_fixed_probes",
            "prove_class_count_lower_bound","check_generic_action_certificates",
            "tamper_test_every_indispensable_probe"],
        "generic_optimizer_exhaustive_small_case_tests":small,
        "results":results,
        "limitations":[
            "the declared domain-semantic transitive closure is a graph operator",
            "the one-hot observation grammar is part of the given contract",
            "only exactly one failure; no unseen-failure statistical generalization",
            "no inference of the correct action rule from arbitrary natural language",
            "generic Python verifier, not complete INSACERMO MAX TOTAL or Lean certificate"
        ]
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("INSACERMO_RAW_CONTRACT_TO_CERTIFICATES_V6.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":main()
