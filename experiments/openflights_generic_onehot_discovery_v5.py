#!/usr/bin/env python3
"""V5: automatic probe discovery, exact proof of minimality and generic runtime bridge."""
import json,hashlib,random,sys
from generic_onehot_contract_optimizer_v1 import solve,verify_lower_bound,exhaustive_selftest
from openflights_failure_budget_min_probes_v3 import load
from openflights_blind_dual_failure_v2 import path
from information_price_runtime_v1 import verify_certificate

def main():
    cases=exhaustive_selftest()
    edges,adj,rows,digest=load()
    s,t="STZ","BSB"
    assert path(adj,s,t) is not None
    # NO preselected critical edges. Domain oracle computes the CONTRACT action
    # for every world; independent generic optimizer discovers probes from labels.
    worlds=tuple(edges)
    actions=[]
    for e in worlds:
        actions.append("ACT" if path(adj,s,t,frozenset((e,))) is not None else "REPAIR:"+e[0]+"->"+e[1])
    answer=solve(worlds,actions)
    assert verify_lower_bound(worlds,actions,answer)
    assert answer.minimum_count==4
    observe=lambda p,w:p==w
    action_lookup=dict(zip(worlds,actions))
    action_of=lambda w:action_lookup[w]
    ids=[next(i for i,a in enumerate(actions) if a=="ACT")]
    ids+= [i for i,a in enumerate(actions) if a!="ACT"]
    checks=[]
    for i in ids:
        cert=verify_certificate(worlds,i,answer.probes,observe,action_of,
                claimed_action=actions[i],
                claimed_outcomes=tuple(observe(p,worlds[i]) for p in answer.probes),
                claimed_price=len(answer.probes))
        assert cert.valid,cert
        checks.append({"failure":f"{worlds[i][0]}->{worlds[i][1]}",
                       "decision":actions[i],"valid":cert.valid})
    assert len(checks)==5
    # Every omitted critical probe makes the policy fail in a contrasting world.
    for p in answer.probes:
        pp=tuple(z for z in answer.probes if z!=p)
        i=worlds.index(p)
        assert not verify_certificate(worlds,i,pp,observe,action_of).valid
    out={"experiment":"INSACERMO_GENERIC_ONEHOT_CONTRACT_DISCOVERY_V5",
         "data_sha256":digest,"source":s,"target":t,
         "world_count":len(worlds),
         "input_to_generic_optimizer":"all world IDs and all contract-required actions; no preselected critical probes",
         "generic_observation_model":"perfect one-hot observation: is this particular edge the failed edge?",
         "discovered_probes":[f"{u}->{v}" for u,v in answer.probes],
         "minimum_number_proven":answer.minimum_count,
         "largest_action_class":answer.largest_action_class,
         "number_of_distinct_actions":answer.distinct_actions,
         "proof":"For one-hot observations, unprobed worlds must share an action, hence the omitted set cannot be larger than the biggest action class. Probing all other worlds attains bound.",
         "exhaustive_optimizer_small_case_tests":cases,
         "existing_generic_runtime_certificate_checks":checks,
         "tampered_missing_probe_rejected":True,
         "scope_limitations":["graph-specific reachability oracle supplies action labels",
          "one-hot single-failure model only","no Lean verification",
          "not the full INSACERMO MAX TOTAL runtime"],
         "status":"PASS"}
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("INSACERMO_GENERIC_ONEHOT_CONTRACT_DISCOVERY_V5.json","w") as f:json.dump(out,f,indent=2,sort_keys=True)
if __name__=="__main__":main()
