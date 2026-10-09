#!/usr/bin/env python3
"""Independent blind audit on 3,823 UCI optdigits.tra images that were never
in the 1,797-row scikit-learn/UCI optdigits.tes catalogue.

NO training, prediction model, weights, or parameter fitting.
Labels of 3823 unknown images are used ONLY AFTER the sealed policy has
emitted its per-image ACT, PROBE, or REFUSE verdict for statistical audit.
"""
import csv
import hashlib
import io
import json
import urllib.request
from collections import Counter
from pathlib import Path

import numpy as np
from sklearn.datasets import load_digits  # dataset reader ONLY, no ML call

SOURCE = "https://raw.githubusercontent.com/leolanggeng/assgn3_bagging_svm/main/optdigits.tra"
SOURCE_GIT_BLOB_SHA1 = "188f5d214829554b61c9ac3ed529fca918f7c910"
SELECTED = (19, 21, 29, 30, 33, 50, 51)
OUTPUT = Path("audit_result.json")

def fetch_heldout():
    with urllib.request.urlopen(SOURCE, timeout=40) as reply:
        raw = reply.read()
    blob = ("blob " + str(len(raw)) + "\0").encode() + raw
    assert hashlib.sha1(blob).hexdigest() == SOURCE_GIT_BLOB_SHA1, "source changed!"
    rows = [list(map(int, r)) for r in csv.reader(io.StringIO(raw.decode())) if r]
    assert len(rows) == 3823 and all(len(r)==65 for r in rows)
    X = np.array([r[:64] for r in rows], dtype=np.uint8)
    y = np.array([r[64]==0 for r in rows], dtype=np.bool_)
    assert np.all(X<=16)
    return raw, X, y

def audit():
    raw, X, y = fetch_heldout()
    dataset = load_digits()
    R = dataset.data.astype(np.uint8)
    labels = (dataset.target == 0)
    assert R.shape==(1797,64)
    assert int(labels.sum()) == 178
    assert int(y.sum()) == 376
    assert tuple(SELECTED) == (19,21,29,30,33,50,51)
    # Check original radius-one separation on the claimed seven pixels.
    Z = R[labels][:, SELECTED]
    N = R[~labels][:, SELECTED]
    for i in range(len(Z)):
        assert np.all(np.count_nonzero(N != Z[i], axis=1) >= 3)
    source_sha = hashlib.sha256(raw).hexdigest()
    R7 = R[:, SELECTED]
    count = Counter()
    accepted = []
    unsafe_candidate_false = []
    first_evidence = {}
    probe_tallies = []
    # fixed deterministic observation order, not tuned on external data.
    remaining = tuple(i for i in range(64) if i not in SELECTED)
    for rowid, x in enumerate(X):
        d7 = np.count_nonzero(R7 != x[list(SELECTED)], axis=1)
        compatible = np.flatnonzero(d7<=1)
        count["total"] += 1
        if compatible.size == 0:
            count["REFUSE_after_7"] += 1
            probe_tallies.append(7)
            continue
        # Naive use of the seven pixels without proving admissibility:
        pred = bool(labels[compatible[0]])
        assert np.all(labels[compatible] == pred), "contradicts radius-one theorem"
        count["naive_7_candidate"] += 1
        if pred == bool(y[rowid]):
            count["naive_7_correct_unlicensed"] += 1
        else:
            count["naive_7_wrong_unlicensed"] += 1
            if len(unsafe_candidate_false)<5:
                unsafe_candidate_false.append({
                  "heldout_index":rowid,"true_is_zero":bool(y[rowid]),
                  "naive_is_zero":pred,"selected_readings":x[list(SELECTED)].tolist()
                })
        # Gate using the EXACT set of possible radius-one reference origins.
        # A reference survives only if <=1 mismatch on ALL observed sensors.
        c = compatible
        diff = d7[c].astype(np.uint8)
        observed = len(SELECTED)
        verdict = "PROBE"
        for p in remaining:
            diff += (R[c,p]!=x[p]).astype(np.uint8)
            ok = diff<=1
            c = c[ok]
            diff = diff[ok]
            observed += 1
            if c.size==0:  # >=2 observed contradictions vs every reference.
                verdict = "REFUSE"
                break
            # With <=1 unobserved coordinate, an EXACT match to a reference
            # already proves that EVERY completion lies in that radius-one ball.
            if (64-observed)<=1 and np.any(diff == 0):
                verdict = "ACT"
                break
            if observed == 64 and c.size:
                verdict = "ACT"
                break
        assert verdict != "PROBE"
        probe_tallies.append(observed)
        count[verdict] += 1
        if verdict == "ACT":
            lbl = bool(labels[c[0]])
            assert np.all(labels[c] == lbl)
            accepted.append({"heldout_index":rowid,"true_is_zero":bool(y[rowid]),
              "certified_is_zero":lbl, "observed_pixels":observed,
              "supporting_reference_index":int(c[0])})
            assert lbl==bool(y[rowid]), "Unexpected real label discrepancy"
        elif "first_refused_after_probe" not in first_evidence:
            first_evidence["first_refused_after_probe"] = {
               "heldout_index":rowid,"observed_pixels":observed,
               "all_reference_candidates_rejected":True
            }
    assert count["total"]==3823
    assert (count["REFUSE_after_7"]+count["REFUSE"]+count["ACT"])==3823
    count["ACT_correct"] = sum(x["true_is_zero"] == x["certified_is_zero"] for x in accepted)
    results = {
      "reference_samples":1797,
      "heldout_samples":3823,
      "heldout_zero_count":int(y.sum()),
      "reference_source":"scikit-learn 1797 UCI optdigits.tes copy",
      "heldout_source":SOURCE,
      "heldout_git_blob_sha1":SOURCE_GIT_BLOB_SHA1,
      "heldout_sha256":source_sha,
      "selected_7_pixels":SELECTED,
      "predeclared_radius":1,
      "audit_policy":"First 7, then ascending unseen coordinate; certify membership before ACT",
      "counts":dict(count),
      "accepted_examples":accepted[:30],
      "unlicensed_false_examples":unsafe_candidate_false,
      "witnesses":first_evidence,
      "pixels_observed_min":min(probe_tallies),
      "pixels_observed_max":max(probe_tallies),
      "pixels_observed_mean":round(sum(probe_tallies)/len(probe_tallies),3),
      "fraction_ACT":round(count["ACT"]/3823,6),
      "no_machine_learning":True,
      "no_statistics_training":True,
      "caveat":"An external digit outside the predeclared radius-one union is REFUSE, never an automatic universal recognition."
    }
    OUTPUT.write_text(json.dumps(results,sort_keys=True,indent=2))
    print("INDEPENDENT_HELDOUT_AUDIT_SUCCESS")
    print(json.dumps(results,sort_keys=True,indent=2))
if __name__=="__main__":
    audit()
