#!/usr/bin/env python3

def subsets(n):
    for mask in range(1<<n):
        yield frozenset(i for i in range(n) if mask>>i & 1)

def minobs(n,facets):
    def face(S): return any(S<=F for F in facets)
    out=[]
    for S in subsets(n):
        if face(S): continue
        if all(face(S-{x}) for x in S):
            out.append(S)
    return set(out)

def relevant(obs, future_conflicts):
    rel=[]
    masked=[]
    for O in obs:
        if any(P <= O for P in future_conflicts):
            masked.append(O)
        else:
            rel.append(O)
    return set(rel),set(masked)

def main():
    # 3 worlds. Capabilities are exactly the three pair-facets.
    # Thus the unique minimal action obstruction is {0,1,2}.
    n=3
    facets={frozenset({0,1}),frozenset({0,2}),frozenset({1,2})}
    obs=minobs(n,facets)
    assert obs=={frozenset({0,1,2})}

    strict_conflicts={frozenset({0,1})}
    loose_conflicts=set()

    rel_strict,masked_strict=relevant(obs,strict_conflicts)
    rel_loose,masked_loose=relevant(obs,loose_conflicts)

    assert rel_strict==set()
    assert masked_strict==obs
    assert rel_loose==obs
    assert masked_loose==set()

    import json
    out={
      "experiment":"INSACERMO_CONTRACT_MASKING_REVEAL_V1",
      "action_minimal_obstructions":[sorted(x) for x in obs],
      "strict_contract_future_conflicts":[sorted(x) for x in strict_conflicts],
      "strict_relevant_action_obstructions":[sorted(x) for x in rel_strict],
      "strict_masked_action_obstructions":[sorted(x) for x in masked_strict],
      "loose_contract_future_conflicts":[],
      "loose_relevant_action_obstructions":[sorted(x) for x in rel_loose],
      "law":"Relaxing the future contract can reveal a higher-order action obstruction that was previously redundant because it contained a smaller future-conflict pair.",
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("CONTRACT_MASKING_REVEAL_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
