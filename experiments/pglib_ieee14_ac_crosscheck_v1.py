# INSACERMO — PGLib IEEE-14 AC cross-check of DC order-7 witness V1
#
# Purpose:
#   Challenge the DC hidden-bundle result with nonlinear AC optimal power flow.
#   This is a numerical cross-check, NOT a formal AC infeasibility certificate.
#
# Witness inherited from the exhaustive DC audit:
#   outage branch index 0 (bus 1--2)
#   future load bundle {2,3,4,6,10,13,14}
#
# Test:
#   - AC-OPF feasibility before outage for the full bundle;
#   - AC-OPF after outage for all 126 non-empty proper subbundles;
#   - AC-OPF after outage for the full bundle;
#   - restored-line AC-OPF.
#
# Each outage solve is warm-started from the corresponding intact-network AC-OPF
# solution when available. A solver failure is reported as NUMERICAL_INCONCLUSIVE,
# not silently promoted to a mathematical proof of infeasibility.

from __future__ import annotations
import hashlib, itertools, re, urllib.request
import numpy as np
from pypower.api import runopf, ppoption

URL = "https://raw.githubusercontent.com/power-grid-lib/pglib-opf/master/api/pglib_opf_case14_ieee__api.m"
WITNESS_BUSES = (2,3,4,6,10,13,14)
OUTAGE_INDEX = 0

def download(url):
    req=urllib.request.Request(url,headers={"User-Agent":"INSACERMO/1.0"})
    with urllib.request.urlopen(req,timeout=120) as r: return r.read()

def parse_matrix(text,name):
    m=re.search(rf"mpc\.{re.escape(name)}\s*=\s*\[(.*?)\];",text,re.S)
    if not m: raise RuntimeError("missing matrix "+name)
    rows=[]
    for raw in m.group(1).splitlines():
        raw=raw.split("%",1)[0].strip().rstrip(";").strip()
        if raw: rows.append([float(x) for x in raw.split()])
    return np.array(rows,dtype=float)

def parse_scalar(text,name):
    m=re.search(rf"mpc\.{re.escape(name)}\s*=\s*([0-9eE+\-.]+)\s*;",text)
    if not m: raise RuntimeError("missing scalar "+name)
    return float(m.group(1))

def make_case(base,bus0,gen0,branch0,gencost0,served,outage=None,warm=None):
    bus=bus0.copy(); gen=gen0.copy(); branch=branch0.copy(); gencost=gencost0.copy()
    served=set(served)
    # Preserve bus topology/shunts/voltage bounds, but capability contract includes
    # only the selected loads. Both P and Q demand of unselected buses are zeroed.
    for i in range(bus.shape[0]):
        bid=int(bus[i,0])
        if bid not in served:
            bus[i,2]=0.0
            bus[i,3]=0.0
    if outage is not None:
        branch[outage,10]=0.0
    if warm is not None:
        # Warm start from intact-network OPF voltages and generation.
        try:
            bus[:,7]=warm["bus"][:,7]  # VM
            bus[:,8]=warm["bus"][:,8]  # VA
            gen[:,1]=warm["gen"][:,1]  # PG
            gen[:,2]=warm["gen"][:,2]  # QG
        except Exception:
            pass
    return {"version":"2","baseMVA":base,"bus":bus,"gen":gen,"branch":branch,"gencost":gencost}

OPT=ppoption(VERBOSE=0,OUT_ALL=0,OPF_ALG=560)

def solve(case, warm_candidates=None):
    """Try several initializations. Failure remains numerical, not a proof."""
    attempts=[]
    candidates=[None]
    if warm_candidates:
        candidates += [w for w in warm_candidates if w is not None]
    count=0
    for warm in candidates:
        test={
            "version":case["version"],
            "baseMVA":case["baseMVA"],
            "bus":case["bus"].copy(),
            "gen":case["gen"].copy(),
            "branch":case["branch"].copy(),
            "gencost":case["gencost"].copy(),
        }
        if warm is not None:
            try:
                test["bus"][:,7]=warm["bus"][:,7]
                test["bus"][:,8]=warm["bus"][:,8]
                test["gen"][:,1]=warm["gen"][:,1]
                test["gen"][:,2]=warm["gen"][:,2]
            except Exception:
                pass
        try:
            res=runopf(test,OPT)
            count += 1
            if bool(res.get("success",False)):
                return True,res,None,count
            attempts.append("unsuccessful")
        except Exception as e:
            count += 1
            attempts.append(type(e).__name__+": "+str(e))
    return False,None," | ".join(attempts[:4]),count

def main():
    raw=download(URL); sha=hashlib.sha256(raw).hexdigest()
    text=raw.decode("utf-8",errors="replace")
    base=parse_scalar(text,"baseMVA")
    bus=parse_matrix(text,"bus"); gen=parse_matrix(text,"gen")
    branch=parse_matrix(text,"branch"); gencost=parse_matrix(text,"gencost")
    original_load={int(r[0]):(float(r[2]),float(r[3])) for r in bus}

    masks=range(1,1<<len(WITNESS_BUSES))
    fullmask=(1<<len(WITNESS_BUSES))-1
    records={}
    failures=[]

    for mask in masks:
        served=tuple(WITNESS_BUSES[i] for i in range(len(WITNESS_BUSES)) if mask&(1<<i))
        basecase=make_case(base,bus,gen,branch,gencost,served,None,None)
        ok0,res0,err0,n0=solve(basecase)
        if not ok0:
            records[mask]=(False,False,"BASELINE_FAIL",err0,n0)
            failures.append(("baseline",mask,err0))
            continue
        outagecase=make_case(base,bus,gen,branch,gencost,served,OUTAGE_INDEX,None)
        ok1,res1,err1,n1=solve(outagecase,[res0])
        records[mask]=(True,ok1,"OK" if ok1 else "OUTAGE_FAIL",err1,n1)

    proper=[m for m in masks if m!=fullmask]
    proper_base=sum(1 for m in proper if records[m][0])
    proper_after=sum(1 for m in proper if records[m][1])
    full=records[fullmask]

    # Restore branch == intact case; solve once more from flat/original start.
    fullset=set(WITNESS_BUSES)
    restore_ok,_,restore_err,_=solve(make_case(base,bus,gen,branch,gencost,fullset,None,None))

    print("INSACERMO_PGLIB_AC_CROSSCHECK_V1")
    print("STATUS NUMERICAL_AC_OPF_STRESS_TEST")
    print("SOURCE_URL",URL)
    print("SOURCE_SHA256",sha)
    print("MODEL NONLINEAR_AC_OPF_PYPOWER")
    print("MATHEMATICAL_INFEASIBILITY_CERTIFICATE 0")
    print("WITNESS_OUTAGE_BRANCH_INDEX",OUTAGE_INDEX)
    print("WITNESS_OUTAGE_BRANCH",int(branch[OUTAGE_INDEX,0]),int(branch[OUTAGE_INDEX,1]))
    print("WITNESS_BUNDLE_BUSES"," ".join(map(str,WITNESS_BUSES)))
    print("WITNESS_BUNDLE_P_MW",f"{sum(original_load[b][0] for b in WITNESS_BUSES):.6f}")
    print("WITNESS_BUNDLE_Q_MVAR",f"{sum(original_load[b][1] for b in WITNESS_BUSES):.6f}")
    print("PROPER_SUBBUNDLES_TOTAL",len(proper))
    print("PROPER_SUBBUNDLES_AC_FEASIBLE_BASELINE",proper_base)
    print("PROPER_SUBBUNDLES_AC_FEASIBLE_AFTER_OUTAGE",proper_after)
    print("FULL_BUNDLE_AC_FEASIBLE_BASELINE",int(full[0]))
    print("FULL_BUNDLE_AC_FEASIBLE_AFTER_OUTAGE",int(full[1]))
    print("FULL_BUNDLE_AC_FEASIBLE_AFTER_RESTORE",int(restore_ok))
    unresolved_masks=[m for m in masks if records[m][0] and not records[m][1]]
    print("NUMERICAL_OUTAGE_NONCONVERGENCES",len(unresolved_masks))
    for m in unresolved_masks:
        buses=[WITNESS_BUSES[i] for i in range(len(WITNESS_BUSES)) if m&(1<<i)]
        print("OUTAGE_NONCONVERGENT_SUBBUNDLE",len(buses)," ".join(map(str,buses)))
    # Numerical minimality scan. A clean numerical obstruction requires all
    # non-empty proper subbundles to converge successfully after the outage.
    numerical_minimal=[]
    for m in masks:
        if not records[m][0] or records[m][1]:
            continue
        proper_ok=True
        sub=(m-1)&m
        while sub:
            if not records[sub][1]:
                proper_ok=False
                break
            sub=(sub-1)&m
        if proper_ok:
            numerical_minimal.append(m)

    if numerical_minimal:
        numerical_minimal.sort(key=lambda m:(m.bit_count(),m))
        min_order=numerical_minimal[0].bit_count()
        max_order=max(m.bit_count() for m in numerical_minimal)
        print("AC_NUMERICAL_MINIMAL_OBSTRUCTIONS",len(numerical_minimal))
        print("AC_MIN_CONFIRMED_NUMERICAL_OBSTRUCTION_ORDER",min_order)
        print("AC_MAX_CONFIRMED_NUMERICAL_OBSTRUCTION_ORDER",max_order)
        for m in numerical_minimal:
            if m.bit_count()==min_order:
                buses=[WITNESS_BUSES[i] for i in range(len(WITNESS_BUSES)) if m&(1<<i)]
                print("AC_MIN_ORDER_WITNESS_BUSES"," ".join(map(str,buses)))
                break
    else:
        print("AC_NUMERICAL_MINIMAL_OBSTRUCTIONS",0)
        print("AC_MIN_CONFIRMED_NUMERICAL_OBSTRUCTION_ORDER","NONE")

    if full[0] and proper_after==len(proper) and not full[1] and restore_ok:
        print("AC_ORDER7_PATTERN_REPRODUCED_NUMERICALLY 1")
        print("INTERPRETATION all_126_proper_subbundles_converged_but_full_bundle_did_not")
    else:
        print("AC_ORDER7_PATTERN_REPRODUCED_NUMERICALLY 0")
        print("INTERPRETATION DC_witness_not_confirmed_as_clean_order7_under_this_AC_solver")
    print("LIMITATION AC_OPF_nonconvex_solver_failure_is_not_proof_of_infeasibility")
    if full[3]: print("FULL_OUTAGE_SOLVER_ERROR",full[3])
    if restore_err: print("RESTORE_SOLVER_ERROR",restore_err)
    print("RESULT COMPLETE")

if __name__=="__main__": main()
