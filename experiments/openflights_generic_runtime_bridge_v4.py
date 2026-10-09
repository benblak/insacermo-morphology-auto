#!/usr/bin/env python3
"""INSACERMO V4: actual generic information-price runtime on OpenFlights contracts.

NOT the complete MAX TOTAL engine. Uses unmodified information_price_runtime_v1.py
to classify, issue per-world certificates, and check adversarial tampering.

A graph-specialized oracle supplies candidate probes and a contract-preserving
quotient for <=2 outages; the generic engine does NOT discover probes directly
from all 37,594 edges. No ML, and no new Lean proof is claimed.
"""
import itertools
import json
import os
import random

from openflights_failure_budget_min_probes_v3 import load
from openflights_blind_dual_failure_v2 import derive, path
from information_price_runtime_v1 import (
    classify_with_certificate, verify_certificate
)

def fmt(e):
    return f"{e[0]}->{e[1]}"

def action_for_failures(adj, source, target, failed):
    """Fully specified zero/one/two-repair policy, unit repair cost.

    Choose the lexicographically first cheapest repair set among failed edges.
    ACT iff still connected. REFUSE only when no repair can restore connectivity
    (should not arise for <=2 outages in initially reachable graphs).
    """
    if path(adj, source, target, failed) is not None:
        return "ACT"
    for size in range(1, len(failed)+1):
        for repair in itertools.combinations(sorted(failed), size):
            rest = failed.difference(repair)
            if path(adj, source, target, frozenset(rest)) is not None:
                return "REPAIR:" + ",".join(map(fmt, repair))
    return "REFUSE"

def check_cert(worlds, i, library, observe, action, expected_action):
    ans=classify_with_certificate(worlds, i, library, observe, action)
    assert ans["verdict"]=="ACT",ans
    assert ans["action"]==expected_action,(ans,expected_action)
    cert=ans["certificate"]
    assert verify_certificate(
        worlds,i,cert.probes,observe,action,
        cert.action,cert.outcomes,cert.price).valid
    assert not verify_certificate(
        worlds,i,cert.probes,observe,action,
        cert.action,cert.outcomes,cert.price+1).valid
    assert not verify_certificate(
        worlds,i,cert.probes,observe,action,
        "FORGED_ACTION",cert.outcomes,cert.price).valid
    for p in cert.probes:
        trial=tuple(x for x in cert.probes if x!=p)
        assert not verify_certificate(worlds,i,trial,observe,action).valid
    return {"action":cert.action,"proof_price":cert.price,
            "probes":[fmt(p) for p in cert.probes],
            "outcomes":list(cert.outcomes)}

def one_failure_contract(adj, all_edges):
    source,target="STZ","BSB"
    d=derive(adj,source,target)
    assert d is not None
    critical=tuple(d["singles"])
    assert len(critical)==4,[fmt(x) for x in critical]
    assert set(map(fmt,critical))=={
        "STZ->SXO","SXO->GRP","GRP->MQH","MQH->BSB"}
    worlds=list(all_edges) # exactly one edge fails
    outside=next(e for e in worlds if e not in critical)
    targets=[outside,*critical]
    index={e:i for i,e in enumerate(worlds)}
    observe=lambda p,e: (e==p)
    action=lambda e: ("REPAIR:"+fmt(e)) if e in critical else "ACT"
    successes=[]
    for e in targets:
        ans=check_cert(worlds,index[e],critical,observe,action,action(e))
        successes.append({"failed":fmt(e),**ans})
        assert ans["proof_price"]==(4 if e==outside else 1)
    refusal=classify_with_certificate(worlds,index[outside],critical[:-1],observe,action)
    assert refusal["verdict"]=="REFUSE"
    return {
        "source":source,"target":target,"worlds_explicit":len(worlds),
        "actions":5,"critical_probes":[fmt(e) for e in critical],
        "certificates":successes,
        "intentionally_missing_probe_gives":refusal["verdict"],
        "status":"PASS"
    }

def two_failure_contract(adj, all_edges, s, t):
    d=derive(adj,s,t)
    assert d is not None
    one=set(d["singles"])
    cuts=[frozenset(c) for c in d["minimal_pairs"]]
    library=tuple(sorted(one.union(*(set(c) for c in cuts))))
    assert library and len(library)<=12,(s,t,len(library))
    # The adapter derives P2, the union of all minimal cuts of size <=2.
    # The decision quotient uses all signatures on P2 with <=2 failed bits.
    # The mathematical cut lemma (NOT Lean verified here) establishes that
    # every global failure set F with |F|<=2 has the same reachability and
    # minimum unit-repair decision as F intersect P2.
    worlds=[frozenset(c) for k in range(3) for c in itertools.combinations(library,k)]
    observe=lambda p,F:p in F
    action=lambda F:action_for_failures(adj,s,t,F)
    successes=[];count_action=0;count_repair=0;maxprice=0
    for i,F in enumerate(worlds):
        expected=action(F)
        cert=check_cert(worlds,i,library,observe,action,expected)
        maxprice=max(maxprice,cert["proof_price"])
        count_action+=expected=="ACT"
        count_repair+=expected.startswith("REPAIR:")
        if (expected.startswith("REPAIR:") or i==0) and len(successes)<8:
            successes.append({"failed":[fmt(e) for e in sorted(F)],**cert})
    assert count_action>0 and count_repair>0
    # Independently check predicted actions from P2 on random global 0..2
    # failures. Also cover EVERY detected 1- and 2-cut directly.
    rng=random.Random(65008+sum(map(ord,s+t)))
    test_failures=[frozenset(),*(frozenset((e,)) for e in one),*cuts]
    for _ in range(256):
        j=rng.randrange(3)
        test_failures.append(frozenset(rng.sample(all_edges,j)))
    for F in test_failures:
        measured=action_for_failures(adj,s,t,F)
        predicted=action_for_failures(adj,s,t,frozenset(F.intersection(library)))
        assert measured==predicted,(s,t,F,measured,predicted)
    # Deliberately withhold the entire probe library for a cut world.
    bad_idx=next(i for i,F in enumerate(worlds) if action(F).startswith("REPAIR:"))
    denied=classify_with_certificate(worlds,bad_idx,(),observe,action)
    assert denied["verdict"]=="REFUSE"
    return {
        "source":s,"target":t,
        "at_most_two_outages_in_full_graph":True,
        "full_universe_not_explicitly_enumerated":True,
        "quotient_worlds":len(worlds),
        "candidate_probes_from_graph_adapter":[fmt(e) for e in library],
        "fixed_probe_basis_cardinality":len(library),
        "binary_reachability_minimal_cut_counts":{"single":len(one),"double":len(cuts)},
        "generic_runtime_valid_certificates":len(worlds),
        "verified_act_states":count_action,
        "verified_repair_states":count_repair,
        "largest_irredundant_per_world_certificate":maxprice,
        "global_policy_sampled_checks":len(test_failures),
        "witnesses":successes,
        "missing_probes_verdict":denied["verdict"],
        "status":"PASS"
    }

def main():
    edges,adj,rows,sha=load()
    assert len(edges)==37594
    out={
        "experiment":"INSACERMO_OPENFLIGHTS_GENERIC_INFORMATION_RUNTIME_BRIDGE_V4",
        "status":"PASS",
        "engine":"information_price_runtime_v1.py (existing module unchanged)",
        "NOT_VERIFIED":"Full INSACERMO MAX TOTAL engine and Lean proof-carrying runtime not invoked",
        "proof_scope":"Python generic-world certificate checker plus structural graph quotient (theory not Lean certified)",
        "dataset":{"sha256":sha,"routes":len(edges),"raw_rows":rows},
        "commit":os.getenv("GITHUB_SHA","unknown"),
        "no_ml":True,
        "exactly_one_outage":one_failure_contract(adj,edges),
        "up_to_two_outages":[
            two_failure_contract(adj,edges,"YZY","YKA"),
            two_failure_contract(adj,edges,"YIK","SYX"),
            two_failure_contract(adj,edges,"BEU","BVI"),
            two_failure_contract(adj,edges,"AWD","FTA")
        ]
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("INSACERMO_OPENFLIGHTS_GENERIC_RUNTIME_BRIDGE_V4.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
