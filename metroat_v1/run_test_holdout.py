#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path

from run_train_mechanics import build_split, train_report

def sha256_file(path):
    h=hashlib.sha256()
    with open(path,"rb") as f:
        for chunk in iter(lambda:f.read(1024*1024),b""):
            h.update(chunk)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",required=True)
    ap.add_argument("--frozen-train",required=True)
    ap.add_argument("--out",required=True)
    a=ap.parse_args()

    frozen=Path(a.frozen_train)
    tpath=frozen/"TRAIN_THRESHOLDS.json"
    fpath=frozen/"FEATURE_ORDER.json"
    if not tpath.exists() or not fpath.exists():
        raise RuntimeError("Frozen TRAIN thresholds/order missing")

    thresholds=json.loads(tpath.read_text())
    features=json.loads(fpath.read_text())

    m,test_features,cats=build_split(a.root)

    if set(test_features)!=set(features):
        missing=sorted(set(features)-set(test_features))
        extra=sorted(set(test_features)-set(features))
        raise RuntimeError(f"TEST feature schema mismatch missing={missing} extra={extra}")
    if list(features)!=list(sorted(features,key=lambda x: hashlib.sha256(x.encode()).hexdigest())):
        raise RuntimeError("Frozen TRAIN feature order is not SHA256 order")
    if set(thresholds)!=set(features):
        raise RuntimeError("Frozen TRAIN threshold keys do not match frozen feature order")

    # Critical anti-retuning invariant: no threshold fitting call exists in this runner.
    rep=train_report(m,features,thresholds)
    rep["provenance"]={
        "threshold_source":"FROZEN_TRAIN_ARTIFACT",
        "feature_order_source":"FROZEN_TRAIN_ARTIFACT",
        "retuned_on_test":False,
        "train_thresholds_sha256":sha256_file(tpath),
        "train_feature_order_sha256":sha256_file(fpath),
        "test_schema_feature_set_matches_train":True
    }

    out=Path(a.out); out.mkdir(parents=True,exist_ok=True)
    (out/"TEST_CATEGORY_RECEIPT.json").write_text(json.dumps(cats,indent=2))
    (out/"TEST_HOLDOUT_REPORT.json").write_text(json.dumps(rep,indent=2))
    print(json.dumps(rep,indent=2))

if __name__=="__main__":
    main()
