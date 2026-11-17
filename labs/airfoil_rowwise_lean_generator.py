#!/usr/bin/env python3
"""INSACERMO independent 281-row Lean fixed-point witness.

No imports from the original model learner. Data bytes are pinned; the
previously sealed coefficients and split are checked and not refitted.
Lean will independently calculate 281 model and baseline squared-error
bounds from 281 measured targets, 7+5 fixed-point basis values, and
fixed-point model coefficients. Source authenticity, floating point,
transcendental features (log) and interval bridge remain external checks.
"""
from __future__ import annotations
import hashlib, json, math, urllib.request
from decimal import Decimal
from pathlib import Path
import numpy as np

URL=("https://raw.githubusercontent.com/rupakc/UCI-Data-Analysis/"
     "b2937bc0f36f570b5a6bb4049656f5239a1f334c/"
     "Airfoil%20Dataset/airfoil_self_noise.dat")
SOURCE_SHA="10ee06e6cfb27dae6b44213d421d217012fb1f9b697592e73a4e4016b52d425f"
SOURCE_BLOB="9f6fdafab6a323514c2a0407dea680fcb23d6795"
PRED_COEFF_SCALE=10**6
FEATURE_SCALE=10**6
RESIDUAL_DENOM=10**9
WIDTH=281
BOUNDSLACK_MILLI=2
FEATURE_NAMES=("frequency","attack_angle","chord","wind_speed","displacement_thickness")
PREREG_COMMIT="08efec5710224a45069da2ee1375e750142bf52b"
SEALED=Path("labs/airfoil_results_20261117/sealed_model_before_holdout.json")
OLD_REPORT=Path("labs/airfoil_results_20261117/audit.json")

def git_blob(raw):
    return hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()

def design(x, mu, sd):
    z=(x-mu)/sd
    items=[]; names=[]
    def add(a,n):
        items.append(np.clip(a,-100,100)); names.append(n)
    for j,n in enumerate(FEATURE_NAMES):add(z[:,j],n)
    for j,n in enumerate(FEATURE_NAMES):
        v=np.log1p(np.maximum(x[:,j],0)) if j==1 else np.log(np.maximum(x[:,j],1e-12))
        add(v,n+":log")
    for j,n in enumerate(FEATURE_NAMES):add(z[:,j]**2,n+":square")
    for j in range(5):
        for k in range(j+1,5):add(z[:,j]*z[:,k],FEATURE_NAMES[j]+"*"+FEATURE_NAMES[k])
    for j,n in enumerate(FEATURE_NAMES):
        for threshold in (-.5,0.,.5):
            add(np.maximum(0,z[:,j]-threshold),n+":hinge"+str(threshold))
    return np.column_stack(items),names

def ridge_linear(z, y):
    a=np.column_stack([np.ones(len(z)),z])
    penalty=np.eye(a.shape[1]);penalty[0,0]=0.
    return np.linalg.solve(a.T@a+penalty,a.T@y)

def fixedpoint_row(y_milli, basis_model, basis_linear, selected_int, base_int):
    def f_prediction(coeff,feature):
        return coeff[0]*FEATURE_SCALE+sum(ci*fi for ci,fi in zip(coeff[1:],feature))
    m_pred=f_prediction(selected_int,basis_model)
    b_pred=f_prediction(base_int,basis_linear)
    actual=y_milli*RESIDUAL_DENOM
    m_abs=abs(actual-m_pred)
    b_abs=abs(actual-b_pred)
    # Outward bounds with 0.002 dB slack around the integer feature approximation.
    upper=(m_abs+RESIDUAL_DENOM-1)//RESIDUAL_DENOM+BOUNDSLACK_MILLI
    lower=max(0,b_abs//RESIDUAL_DENOM-BOUNDSLACK_MILLI)
    return int(upper),int(lower),int(m_pred),int(b_pred)

def run(output):
    out=Path(output);out.mkdir(parents=True,exist_ok=True)
    request=urllib.request.Request(URL,headers={"User-Agent":"INSACERMO-Rowwise-Lean-Audit"})
    with urllib.request.urlopen(request,timeout=120) as resp: raw=resp.read()
    assert hashlib.sha256(raw).hexdigest()==SOURCE_SHA
    assert git_blob(raw)==SOURCE_BLOB
    text=raw.decode()
    source_lines=[line.strip().split() for line in text.splitlines() if line.strip()]
    assert len(source_lines)==1503 and all(len(line)==6 for line in source_lines)
    vals=np.asarray([[float(v) for v in line] for line in source_lines],float)
    x,y=vals[:,:5],vals[:,5]
    target_milli=[int(Decimal(line[-1])*1000) for line in source_lines]
    assert all(abs(y[i]*1000-target_milli[i])<1e-7 for i in range(len(y)))

    sealed=json.loads(SEALED.read_text()); prev=json.loads(OLD_REPORT.read_text())
    assert sealed["prereg_commit"]==PREREG_COMMIT
    assert sealed["dataset_git_blob"]==SOURCE_BLOB
    assert prev["source_sha256"]==SOURCE_SHA
    assert prev["transfer_accepted"] is True
    discovery=sealed["discovery_indices"]
    challenge=sealed["challenge_indices"]
    hold=sealed["holdout_row_ids"]
    assert len(discovery)==733 and len(challenge)==40 and len(hold)==WIDTH
    assert len(set(discovery+challenge+hold))==len(discovery)+len(challenge)+len(hold)
    assert np.all(np.isclose(x[hold,3],31.7))
    assert all(not np.isclose(x[i,3],31.7) for i in discovery+challenge)
    known=[i for i in range(1503) if not np.isclose(x[i,3],31.7)]
    known.sort(key=lambda i:hashlib.sha256(f"20261117:airfoil:{i}".encode()).digest())
    assert discovery==known[:733] and set(challenge).issubset(set(known[733:]))
    assert hold==[int(v) for v in np.flatnonzero(np.isclose(x[:,3],31.7))]

    mu=np.asarray(sealed["mean"]);sd=np.asarray(sealed["std"])
    assert np.allclose(mu,np.mean(x[discovery],axis=0),rtol=0,atol=1e-10)
    assert np.allclose(sd,np.std(x[discovery],axis=0),rtol=0,atol=1e-10)
    z,names=design(x,mu,sd)
    chosen=sealed["selected_indices"]
    assert len(chosen)==7 and [names[i] for i in chosen]==sealed["expressions"]
    c=np.asarray(sealed["coefficients"])
    assert len(c)==8
    train=discovery+challenge
    linear_coeff=ridge_linear(z[train,:5],y[train])
    model_pred=c[0]+z[hold][:,chosen]@c[1:]
    baseline_pred=linear_coeff[0]+z[hold,:5]@linear_coeff[1:]
    model_rmse=float(np.sqrt(np.mean((y[hold]-model_pred)**2)))
    base_rmse=float(np.sqrt(np.mean((y[hold]-baseline_pred)**2)))
    assert abs(model_rmse-prev["holdout_rmse_dB"])<1e-7
    assert abs(base_rmse-prev["linear_rmse_dB"])<1e-7

    select_i=np.rint(c*PRED_COEFF_SCALE).astype(np.int64).tolist()
    linear_i=np.rint(linear_coeff*PRED_COEFF_SCALE).astype(np.int64).tolist()
    rows=[];upper_total=0;lower_total=0;max_approx_error=0.
    for j,i in enumerate(hold):
        ya=target_milli[i]
        f=np.rint(z[i,chosen]*FEATURE_SCALE).astype(np.int64).tolist()
        g=np.rint(z[i,:5]*FEATURE_SCALE).astype(np.int64).tolist()
        upper,lower,m_num,b_num=fixedpoint_row(ya,f,g,select_i,linear_i)
        predicted_fixed=m_num/(FEATURE_SCALE*PRED_COEFF_SCALE)
        base_fixed=b_num/(FEATURE_SCALE*PRED_COEFF_SCALE)
        delta=max(abs(predicted_fixed-model_pred[j]),abs(base_fixed-baseline_pred[j]))
        max_approx_error=max(max_approx_error,delta)
        assert delta<.001,("BAD_FIXED_POINT_BRIDGE",i,delta)
        exact_m=abs(y[i]-model_pred[j])*1000
        exact_b=abs(y[i]-baseline_pred[j])*1000
        assert exact_m <= upper,("MODEL_INTERVAL_FAIL",i,upper,exact_m)
        assert exact_b >= lower,("BASELINE_INTERVAL_FAIL",i,lower,exact_b)
        upper_total+=upper*upper
        lower_total+=lower*lower
        rows.append((ya,f,g))
    assert len(rows)==WIDTH
    five_bound=25*WIDTH*1000000
    assert upper_total < five_bound
    assert 100*upper_total < 81*lower_total,(upper_total,lower_total)
    assert all(len(f)==7 and len(g)==5 for _,f,g in rows)

    input_lines=[]
    for ya,f,g in rows:
        sf=", ".join(str(int(v)) for v in f)
        sg=", ".join(str(int(v)) for v in g)
        input_lines.append(f"  ({ya}, ([{sf}], [{sg}])),")
    fmt=lambda arr:", ".join(str(int(v)) for v in arr)
    # Every one of the 281 rows is explicitly part of the Lean proof term.
    # The kernel independently performs all Int dot-products, subtractions,
    # outward-rounded error bounds, Nat squares, totals and decisions.
    lean="""-- INSACERMO independent per-observation integer receipt (281 actual acoustic measurements)
-- Archived public source SHA256: %s
-- Original frozen formula commit: %s
-- For every row, stored y = actual dB*1000, basis values = feature*10^6.
-- Coefficients = parameter*10^6. Resulting dot-product units are 10^12 dB.
-- Lean directly recomputes integer predictions, residual bounds, and squared sums.
-- The 0.002 dB per-residual slack and numerical feature conversion are audited
-- outside Lean by Python. No claims of formalizing logarithms, IEEE floating
-- arithmetic, original CSV cryptography, generalization or acoustic physics.
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace InsacermoAirfoilRows
abbrev Observation := Int × (List Int × List Int)
def featureScale : Int := 1000000
def actualMilliToPrediction : Int := 1000000000
def modelIntercept : Int := %s
def modelCoefficients : List Int := [%s]
def baselineIntercept : Int := %s
def baselineCoefficients : List Int := [%s]

def observations : List Observation := [
%s
]

def dot (coeff values : List Int) : Int :=
  (List.zip coeff values).foldl (fun acc pair => acc + pair.1 * pair.2) 0

def prediction (intercept : Int) (coeff values : List Int) : Int :=
  intercept * featureScale + dot coeff values

def modelUpperMilli (r : Observation) : Nat :=
  ((r.1 * actualMilliToPrediction -
    prediction modelIntercept modelCoefficients r.2.1).natAbs +
    999999999) / 1000000000 + 2

def baselineLowerMilli (r : Observation) : Nat :=
  ((r.1 * actualMilliToPrediction -
    prediction baselineIntercept baselineCoefficients r.2.2).natAbs /
    1000000000) - 2

def modelSseUpper : Nat :=
  observations.foldl (fun acc r => acc + (modelUpperMilli r)^2) 0

def baselineSseLower : Nat :=
  observations.foldl (fun acc r => acc + (baselineLowerMilli r)^2) 0

theorem all_281_rows : observations.length = 281 := by decide
theorem seven_model_five_baseline_features :
  observations.all (fun r => r.2.1.length == 7 && r.2.2.length == 5) = true := by
  decide

theorem independently_computed_sums :
  modelSseUpper = %s ∧ baselineSseLower = %s := by
  decide

theorem certified_five_db_gate :
  modelSseUpper < 25 * 281 * 1000000 := by
  decide

theorem certified_ten_percent_gate :
  100 * modelSseUpper < 81 * baselineSseLower := by
  decide

theorem any_squared_errors_inside_certified_intervals
    (trueModel trueBaseline : Nat)
    (hm : trueModel ≤ modelSseUpper)
    (hb : baselineSseLower ≤ trueBaseline) :
    trueModel < 25 * 281 * 1000000 ∧
    100 * trueModel < 81 * trueBaseline := by
  constructor
  · calc
      trueModel ≤ modelSseUpper := hm
      _ < 25 * 281 * 1000000 := certified_five_db_gate
  · calc
      100 * trueModel ≤ 100 * modelSseUpper := Nat.mul_le_mul_left 100 hm
      _ < 81 * baselineSseLower := certified_ten_percent_gate
      _ ≤ 81 * trueBaseline := Nat.mul_le_mul_left 81 hb

end InsacermoAirfoilRows
""" % (SOURCE_SHA,PREREG_COMMIT,select_i[0],fmt(select_i[1:]),
        linear_i[0],fmt(linear_i[1:]),"\n".join(input_lines),
        upper_total,lower_total)
    lean_path=out/"Airfoil281RowCertificate.lean"
    lean_path.write_text(lean)
    receipt=dict(
       study="INSACERMO_AIRFOIL_ROW_WISE_FIXEDPOINT_LEAN",
       source_sha256=SOURCE_SHA,source_git_blob=SOURCE_BLOB,
       preregistration_commit=PREREG_COMMIT,
       holdout_records=WIDTH,model_terms=sealed["expressions"],
       model_coefficients_millionths=select_i,
       baseline_coefficients_millionths=linear_i,
       actual_model_rmse_dB=model_rmse,actual_baseline_rmse_dB=base_rmse,
       max_fixedpoint_prediction_deviation_dB=max_approx_error,
       per_row_absolute_prediction_bridge_limit_dB=.001,
       outward_residual_slack_millidB=BOUNDSLACK_MILLI,
       model_sse_upper_millidB2=upper_total,
       baseline_sse_lower_millidB2=lower_total,
       mathematical_5db_test=upper_total<five_bound,
       mathematical_10pct_test=100*upper_total<81*lower_total,
       worst_case_improvement_percent=100*(1-math.sqrt(upper_total/lower_total)),
       proof_source_sha256=hashlib.sha256(lean.encode()).hexdigest(),
       trust_boundary=[
          "Lean proves exact integer predictions and residual bounds from 281 encoded rows, basis coefficients, and fixed-point features.",
          "The mapping of feature vectors and acoustic labels to the original archived CSV is checked externally by Python and pinned SHA256.",
          "Transcendental log feature extraction and real-valued coefficients are not formally certified by Lean.",
          "The pre-registered empirical validation is on one unseen condition, not a universally proven physical law.",
          "The frozen historical INSACERMO C3 kernel remains completely untouched."])
    (out/"rowwise_receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print("AIRFOIL_281_RECORDS_FIXED_POINT",json.dumps({
        "n":WIDTH,"model_sse_upper":upper_total,"baseline_sse_lower":lower_total,
        "mean_rmse":model_rmse,"baseline_rmse":base_rmse,
        "worst_improvement_percent":receipt["worst_case_improvement_percent"],
        "max_bridge_error":max_approx_error,
        "proof_sha256":receipt["proof_source_sha256"]
    },sort_keys=True),flush=True)

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_airfoil_rowwise")
