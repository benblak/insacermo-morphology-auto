#!/usr/bin/env python3
"""Independent arithmetic witness for the sealed INSACERMO airfoil laboratory.

Recomputes predictions from archived source + sealed formula and validates the
precommitted transfer threshold. Emits an exact finite Nat-sum Lean 4 proof.
This does NOT prove the learned physical law or the floating-point calculations:
Lean certifies the exact integer residual bounds and their logical implication.
"""
from __future__ import annotations
import hashlib, json, math, urllib.request
from pathlib import Path
import numpy as np

DATA_URL = ("https://raw.githubusercontent.com/rupakc/UCI-Data-Analysis/"
            "b2937bc0f36f570b5a6bb4049656f5239a1f334c/"
            "Airfoil%20Dataset/airfoil_self_noise.dat")
SHA256 = "10ee06e6cfb27dae6b44213d421d217012fb1f9b697592e73a4e4016b52d425f"
GIT_BLOB = "9f6fdafab6a323514c2a0407dea680fcb23d6795"
PREREG = "08efec5710224a45069da2ee1375e750142bf52b"
OUTCOME = Path("labs/airfoil_results_20261117/audit.json")
SEALED = Path("labs/airfoil_results_20261117/sealed_model_before_holdout.json")
SCALE=1000
RIDGE=1.0

def gitblob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def basis(x,mu,sd,i):
    z = [(float(x[j])-mu[j])/sd[j] for j in range(5)]
    if i<5: val=z[i]
    elif i<10:
        j=i-5
        val= math.log1p(max(float(x[j]),0)) if j==1 else math.log(max(float(x[j]),1e-12))
    elif i<15: val=z[i-10]**2
    elif i<25:
        pairs=[(j,k) for j in range(5) for k in range(j+1,5)]
        j,k=pairs[i-15];val=z[j]*z[k]
    else:
        j=(i-25)//3
        threshold=(-.5,0.,.5)[(i-25)%3]
        val=max(0.,z[j]-threshold)
    return max(-100.,min(100.,val))

def readdata():
    request=urllib.request.Request(DATA_URL,headers={"User-Agent":"INSACERMO-lean-airfoil-replay"})
    with urllib.request.urlopen(request,timeout=90) as r:
        raw=r.read()
    assert hashlib.sha256(raw).hexdigest()==SHA256, "ORIGINAL_SOURCE_SHA256_MISMATCH"
    assert gitblob(raw)==GIT_BLOB,"ORIGINAL_SOURCE_GIT_BLOB_MISMATCH"
    rows=np.asarray([[float(v) for v in row.split()] for row in
          raw.decode().splitlines() if row.strip()],dtype=float)
    assert rows.shape==(1503,6)
    return rows

def run(folder):
    out=Path(folder)
    out.mkdir(parents=True,exist_ok=True)
    model=json.loads(SEALED.read_text())
    original=json.loads(OUTCOME.read_text())
    assert model["prereg_commit"]==PREREG
    assert model["dataset_git_blob"]==GIT_BLOB
    assert original["transfer_accepted"] is True
    raw=readdata();X=raw[:,:5];y=raw[:,5]
    unknown=np.flatnonzero(np.isclose(X[:,3],31.7)).tolist()
    assert unknown==model["holdout_row_ids"] and len(unknown)==281
    known=np.flatnonzero(~np.isclose(X[:,3],31.7)).tolist()
    assert len(known)==1222
    known.sort(key=lambda i:hashlib.sha256(f"20261117:airfoil:{i}".encode()).digest())
    discovery=known[:int(.6*len(known))]
    pool=known[int(.6*len(known)):]
    assert discovery==model["discovery_indices"] and len(discovery)==733
    challenge=model["challenge_indices"]
    assert len(challenge)==40 and len(set(challenge))==40
    assert set(challenge).issubset(pool)
    assert set(challenge).isdisjoint(discovery)
    assert set(challenge).isdisjoint(unknown)
    train=discovery+challenge
    mu=np.mean(X[discovery],axis=0)
    sd=np.std(X[discovery],axis=0)
    sd[sd<1e-8]=1
    assert np.allclose(mu,model["mean"],atol=1e-11,rtol=0)
    assert np.allclose(sd,model["std"],atol=1e-11,rtol=0)
    idx=model["selected_indices"]
    c=model["coefficients"]
    assert len(idx)==len(c)-1 and len(idx)<=7
    assert len(set(idx))==len(idx)
    # Reimplementation independent of the trained grammar() and pred().
    p=[]
    for i in unknown:
        features=[basis(X[i],mu,sd,j) for j in idx]
        p.append(c[0]+sum(a*b for a,b in zip(c[1:],features)))
    p=np.asarray(p,float)
    # Independent linear benchmark: augmented-matrix QR least-squares ridge.
    Z=np.clip((X-mu)/sd,-100,100)
    D=np.column_stack([np.ones(len(train)),Z[train]])
    penalty=np.zeros((5,6))
    penalty[:,1:]=np.eye(5)*math.sqrt(RIDGE)
    A=np.vstack([D,penalty])
    b=np.concatenate([y[train],np.zeros(5)])
    linearcoef=np.linalg.lstsq(A,b,rcond=None)[0]
    linear=np.column_stack([np.ones(len(unknown)),Z[unknown]])@linearcoef
    actual=y[unknown]
    e=np.abs(actual-p)
    baseline_e=np.abs(actual-linear)
    rmse=math.sqrt(np.mean(e**2))
    linear_rmse=math.sqrt(np.mean(baseline_e**2))
    assert math.isclose(rmse,original["holdout_rmse_dB"],rel_tol=0,abs_tol=1e-6),(rmse,original["holdout_rmse_dB"])
    assert math.isclose(linear_rmse,original["linear_rmse_dB"],rel_tol=0,abs_tol=1e-6),(linear_rmse,original["linear_rmse_dB"])
    # Deliberately outward rounded intervals (10^-8 dB slack per prediction).
    # For a given true residual e, model abs(e) <= upper[i]/1000,
    # and baseline abs(e)>=lower[i]/1000, conditional on replay's float values.
    upper=np.ceil((e+1e-8)*SCALE).astype(np.int64).tolist()
    lower=np.maximum(0,np.floor((baseline_e-1e-8)*SCALE)).astype(np.int64).tolist()
    assert all(a/SCALE>=v for a,v in zip(upper,e))
    assert all(b/SCALE<=v for b,v in zip(lower,baseline_e))
    hi=sum(v*v for v in upper)
    lo=sum(v*v for v in lower)
    limit=25*len(unknown)*SCALE*SCALE
    assert hi < limit,(hi,limit)
    assert 100*hi<81*lo,(hi,lo)
    expected=((1-rmse/linear_rmse)*100)
    assert expected>=10 and rmse<=5
    # The generated list is part of the proof term: the integer certificate is
    # NOT accepted merely because some independent Python asserts passed.
    array_upper=", ".join(str(x) for x in upper)
    array_lower=", ".join(str(x) for x in lower)
    lean=f"""import Lean

/-!
INSACERMO AIRFOIL - EXACT FINITE ARITHMETIC CERTIFICATE
Source pinned SHA256: {SHA256}
Sealed coefficients and split: labs/airfoil_results_20261117/
Generated by an independent Python replay from 281 held-out responses.

The two lists are per-row upper bounds of candidate absolute errors and
lower bounds of linear-baseline absolute errors, in thousandths of a dB.
They are generated from floating-point recomputation; Lean does NOT prove
that the physical dataset, rounding steps, model selection or features
obey the claimed interpretation. Lean kernel proves only finite integer
claims conditional on those witnessed per-row bounds.
-/

namespace InsacermoAirfoil
def candidateUpperMilli : List Nat :=
  [{array_upper}]

def baselineLowerMilli : List Nat :=
  [{array_lower}]

def candidateSseUpper : Nat :=
  candidateUpperMilli.foldl (fun t x => t + x*x) 0
def linearSseLower : Nat :=
  baselineLowerMilli.foldl (fun t x => t + x*x) 0

theorem record_count :
  candidateUpperMilli.length = 281 ∧ baselineLowerMilli.length = 281 := by
  decide

theorem numeric_candidate_sse : candidateSseUpper = {hi} := by
  decide
theorem numeric_baseline_sse : linearSseLower = {lo} := by
  decide

theorem below_five_db_squared :
  candidateSseUpper < 25 * 281 * 1000000 := by
  decide

/- Since RMSE squares are averages over equal-sized groups,
   (RMSE candidate / RMSE baseline) < 0.90 follows from
   100*candidate SSE < 81*baseline SSE, using nonnegative square roots. -/
theorem ten_percent_lower_rmse_squared :
  100 * candidateSseUpper < 81 * linearSseLower := by
  decide

/- Error propagation is verified for ANY nonnegative integer squared-error
   totals sandwiched by the certified bounds. -/
theorem finite_interval_soundness
    (observedCandidateSse observedBaselineSse : Nat)
    (hUpper : observedCandidateSse ≤ candidateSseUpper)
    (hLower : linearSseLower ≤ observedBaselineSse) :
    observedCandidateSse < 25 * 281 * 1000000 ∧
    100 * observedCandidateSse < 81 * observedBaselineSse := by
  constructor
  · exact lt_of_le_of_lt hUpper below_five_db_squared
  · have hM : 100 * observedCandidateSse ≤ 100 * candidateSseUpper :=
      Nat.mul_le_mul_left 100 hUpper
    have hL : 81 * linearSseLower ≤ 81 * observedBaselineSse :=
      Nat.mul_le_mul_left 81 hLower
    exact lt_of_le_of_lt hM (lt_of_lt_of_le ten_percent_lower_rmse_squared hL)

end InsacermoAirfoil
"""
    (out/"AirfoilArithmeticCertificate.lean").write_text(lean)
    report=dict(
        verdict="NUMERIC_CRITERIA_CERTIFIED_CONDITIONALLY_ON_REPLAY",
        source_sha256=SHA256,git_blob=GIT_BLOB,preregistration=PREREG,
        number_of_holdout_residuals=len(unknown),
        calculated_model_rmse=rmse,calculated_linear_rmse=linear_rmse,
        model_rmse_from_original_audit=original["holdout_rmse_dB"],
        linear_rmse_from_original_audit=original["linear_rmse_dB"],
        actual_relative_improvement_pct=expected,
        model_sse_upper_in_micro_db2=hi,
        baseline_sse_lower_in_micro_db2=lo,
        absolute_5db_sse_limit_in_micro_db2=limit,
        ratio_left=100*hi,ratio_right=81*lo,
        candidate_residual_milli_upper=upper,
        linear_residual_milli_lower=lower,
        sources_and_split_crosschecked=True,
        limits=["Lean kernel proves only exact integer arithmetic, interval implication, and record count.",
                "Python externally recomputes all floating predictions and quantized residuals.",
                "No Lean theorem establishes data authenticity, source code correctness or the actual aerodynamics.",
                "Historical INSACERMO C3 and Lean files are not modified."])
    (out/"independent_source_replay.json").write_text(json.dumps(report,indent=2)+"\n")
    print("AIRFOIL_BOUND_WITNESS",json.dumps({
        "rows":len(unknown),"upper_sse":hi,"lower_sse":lo,
        "threshold_5db":limit,"ratio_lhs":100*hi,"ratio_rhs":81*lo,
        "replay_rmse":rmse,"replay_linear":linear_rmse},sort_keys=True),flush=True)

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_airfoil_lean")
