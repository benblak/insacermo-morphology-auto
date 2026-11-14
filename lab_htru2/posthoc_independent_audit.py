#!/usr/bin/env python3
"""POST-HOC independent sanity check of preregistered HTRU2 results.
Does NOT refit any policy or alter the holdout results.
Enumerates all 8! fixed probe orders independently of the original DP.
"""
import json
import itertools
import sys
from pathlib import Path

d=json.loads(Path(sys.argv[1]).read_text())
h=d["reference_histogram"]
assert len(h)==256
total=sum(a+b for a,b in h)
assert total==14318

pure_neg=sum(a>0 and b==0 for a,b in h)
pure_pos=sum(a==0 and b>0 for a,b in h)
mixed=sum(a>0 and b>0 for a,b in h)
assert pure_neg==143 and pure_pos==0 and mixed==36

unresolved=[]
for mask in range(256):
    cells={}
    for sig,(n0,n1) in enumerate(h):
        if not n0+n1: continue
        x=sig&mask
        v=cells.setdefault(x,[0,0,False])
        v[0]+=n0
        v[1]+=n1
        if (n0==0)!=(n1==0):
            v[2]=True
    unresolved.append(sum(n0+n1 for n0,n1,has_pure in cells.values()
                          if n0 and n1 and has_pure))
best=None
best_order=None
tie_count=0
for order in itertools.permutations(range(8)):
    mask=0
    cost=0
    for j in order:
        cost+=unresolved[mask]
        mask|=1<<j
    if best is None or cost<best:
        best=cost; best_order=order;tie_count=1
    elif cost==best:
        tie_count+=1
assert best==d["results"]["training_best_fixed"]["probes"]==86237
assert abs(best/total-d["strategy"]["train_opt_fixed_probes"])<1e-12

a=d["results"]["holdout_adaptive"]
f=d["results"]["holdout_best_fixed"]
assert a["n"]==f["n"]==3580
assert a["acted"]==f["acted"]==521
assert a["action_errors"]==f["action_errors"]==1
assert a["act_0"]==f["act_0"]==521
assert a.get("act_1",0)==f.get("act_1",0)==0
assert a["missed_pulsar"]==1 and a.get("false_pulsar",0)==0
assert a["probes"]==19174 and f["probes"]==21508
saved=f["probes"]-a["probes"]
rate=100*saved/f["probes"]
assert abs(rate-10.851776083317832)<1e-8
print("INDEPENDENT FIXED ORDER BRUTE FORCE: 40320 permutations")
print(f"best_fixed_train_total_probes={best}, tied_optimal_orders={tie_count}")
print(f"pure_negative_reference_signatures={pure_neg}, pure_positive={pure_pos}, mixed={mixed}")
print(f"holdout_actions={a['acted']}, positive_actions={a.get('act_1',0)}, missed_true_pulsars={a['missed_pulsar']}")
print(f"holdout_probe_savings={saved} ({rate:.4f}%) vs optimal fixed order")
print("CLOSED_REFERENCE_CERTAINTY=PASS")
print("UNSEEN_CERTAINTY=FALSE (one false negative)")
print("PULSAR_DISCOVERY_SUCCESS=FALSE (zero positive detections)")
print("INDEPENDENT SANITY CHECK: PASS")
