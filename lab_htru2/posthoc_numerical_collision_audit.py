#!/usr/bin/env python3
"""POST-HOC diagnostic ONLY. No model adjustment and no new performance claims.

Compare full numerical 8-dimensional radio-pulsar measurements for the
21 candidates sharing signature 11100001 in the pre-registered HTRU2 protocol.
Print counts and show whether information was lost when converting numerical
features to 8 binary median tests.
"""
import random
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"lab_htru2"))
from htru2_certified_probes import load_dataset,compute_model,bin_sig
SEED=20261114
rows,labels,metadata=load_dataset(sys.argv[1])
ids=list(range(len(rows)))
random.Random(SEED).shuffle(ids)
train=ids[:len(ids)*4//5]
held=ids[len(ids)*4//5:]
medians,hist=compute_model(rows,labels,train)
target=225
train_candidates=[ix for ix in train if bin_sig(rows[ix],medians)==target]
test_candidates=[ix for ix in held if bin_sig(rows[ix],medians)==target]
errors=[ix for ix in test_candidates if labels[ix]==1]
all_candidates=train_candidates+test_candidates
identical_raw_records=len(set(rows[ix] for ix in all_candidates))
conflicting_raw={}
for ix in all_candidates:
    conflicting_raw.setdefault(rows[ix],set()).add(labels[ix])
contradictions=sum(len(v)>1 for v in conflicting_raw.values())
assert hist[target]==[20,0],hist[target]
assert 1528 in errors and labels[1528]==1
print(f"signature=11100001; 20 reference non-pulsars and {len(test_candidates)} holdout records share this signature")
print(f"heldout positives with that signature: {len(errors)}; includes misclassified row 1528")
print(f"distinct FULL 8-dimensional numeric vectors across train+holdout in this signature: {identical_raw_records}/{len(all_candidates)}")
print(f"identical FULL numeric vectors with opposite labels: {contradictions}")
print(f"error_row_1528_full_numeric={rows[1528]}")
if contradictions:
    print("INFORMATION LIMIT: even exact numeric equality exists across contrary labels")
else:
    print("IMPORTANT: no conflicting exact numeric twins found here; impossibility proven only for median-binary observations")
print("NO_TUNING_PERFORMED=TRUE")

# One-sided exact Clopper-Pearson upper confidence bound from the frozen holdout,
# assuming i.i.d. exchangeable candidates and a policy frozen before test labels.
# It is a probability bound, NOT a logical guarantee for any unseen world.
n=521;k=1
def prob_at_most_one_error(p):
    return (1-p)**n + n*p*(1-p)**(n-1)
lo,hi=0.0,1.0
for _ in range(90):
    mid=(lo+hi)/2
    if prob_at_most_one_error(mid)>0.05:lo=mid
    else:hi=mid
assert 0.008 < hi < 0.010
print(f"one-sided_95pct_CP_upper_conditional_action_error={hi:.8f} (i.i.d. assumption, not certainty)")
