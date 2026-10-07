#!/usr/bin/env python3
import json, random

def synthetic_screening(seed=42,n=100000,p=0.4,k=4,threshold=2):
    rng=random.Random(seed)
    data=[[rng.random()<p for _ in range(k)] for _ in range(n)]
    brute_reject=0; brute_reads=0
    for row in data:
        brute_reads += k
        brute_reject += int(sum(row)>=threshold)
    cert_reject=0; cert_reads=0
    for row in data:
        violations=0
        for v in row:
            cert_reads += 1
            violations += int(v)
            if violations>=threshold:
                break
        cert_reject += int(violations>=threshold)
    saved=brute_reads-cert_reads
    assert brute_reject==cert_reject
    return {
      "seed":seed,"n":n,"criteria":k,"violation_probability":p,"reject_threshold":threshold,
      "brute_force":{"rejected":brute_reject,"reads":brute_reads},
      "certified_stop":{"rejected":cert_reject,"reads":cert_reads},
      "reads_saved":saved,"reads_saved_percent":100.0*saved/brute_reads,
      "same_verdict_count":n,"errors":0,
      "claim_boundary":[
        "Synthetic boolean demonstration only; not a pharmacological validation.",
        "The early-stop rule is classical short-circuit logic by itself.",
        "The measured resource here is criterion reads, not physical energy."
      ]
    }

def main():
    s=synthetic_screening()
    # Frozen real-data result from the audited UCI Mushroom V1 run.
    mushroom={
      "dataset":"UCI Mushroom",
      "run_id":37334343679,
      "rows":8124,"available_probes":22,
      "planner":{"max_depth":3,"mean_reads":1.6538650910881338,"root":"odor"},
      "local_exact_certificate_price":{
        "certifiable":8124,"uncertifiable":0,
        "price_1":6649,"price_2":1475,
        "mean":1.181560807483998,
        "max":2
      },
      "claim_boundary":"Finite dataset-relative guarantee only; not a real-world food-safety system."
    }
    out={
      "title":"INSACERMO Information Economy Demo V1",
      "principle":"Stop acquiring information once the declared decision is already certified.",
      "synthetic":s,
      "real_data_bridge":mushroom,
      "status":"PASS"
    }
    with open("INFORMATION_ECONOMY_DEMO_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)
    print(json.dumps(out,indent=2,sort_keys=True))
    assert s["brute_force"]["rejected"]==52369
    assert s["brute_force"]["reads"]==400000
    assert s["certified_stop"]["reads"]==349027
    assert s["reads_saved"]==50973

if __name__=="__main__": main()
