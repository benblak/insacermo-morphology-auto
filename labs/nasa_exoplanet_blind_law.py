#!/usr/bin/env python3
"""NASA exoplanets: limited-label retrospective equation search, no ML training.

No physical experiment is performed: querying a withheld orbital period is a
retrospective observation of the NASA catalogue. The possible polynomial laws
are a PREDECLARED family. On many rows semi-major axes are themselves derived
from orbital periods, so reproducing the relation is not independent physical
confirmation. Frozen C3 is not modified.
"""
import csv,hashlib,io,json,math,random,statistics,urllib.parse,urllib.request
from pathlib import Path

SEED=20261116
COLS=["pl_name","hostname","pl_orbper","pl_orbsmax","st_mass","sy_snum",
      "cb_flag","discoverymethod","disc_year","pl_orbperlim","pl_orbsmaxlim"]
QUERY=("select "+",".join(COLS)+" from pscomppars where pl_orbper > 0"
       " and pl_orbsmax > 0 and st_mass > 0")
URL="https://exoplanetarchive.ipac.caltech.edu/TAP/sync?"+urllib.parse.urlencode(
    {"query":QUERY,"format":"csv"})
EXPONENTS=[(a/2,b/2) for a in range(0,7) for b in range(-3,4)]
BUDGET=12
BASELINE_REPEATS=60

def load():
    request=urllib.request.Request(URL,headers={"User-Agent":"INSACERMO-independent-scientific-lab/1.0"})
    with urllib.request.urlopen(request,timeout=100) as r:
        raw=r.read()
    assert 1000<len(raw)<20_000_000 and raw.startswith(b"pl_name,")
    obj=list(csv.DictReader(io.StringIO(raw.decode("utf-8-sig"))))
    if not obj:raise RuntimeError("NASA_EMPTY_DATA")
    rows=[]
    for d in obj:
        try:
            if str(d["sy_snum"])!="1" or str(d["cb_flag"])!="0":continue
            if d["discoverymethod"] not in ("Transit","Radial Velocity"):continue
            if d["pl_orbperlim"] not in ("","0") or d["pl_orbsmaxlim"] not in ("","0"):continue
            p=float(d["pl_orbper"]);a=float(d["pl_orbsmax"]);m=float(d["st_mass"])
            if not (0.1<m<3. and .003<a<8 and .1<p<12000):continue
            rows.append(dict(name=d["pl_name"],host=d["hostname"],p=p,a=a,m=m,
                x=math.log(a),z=math.log(m),y=math.log(p/365.25),
                method=d["discoverymethod"]))
        except (TypeError,ValueError,KeyError):continue
    assert len(rows)>=100,("TOO_FEW_USABLE_ROWS",len(rows))
    rows.sort(key=lambda r:r["name"])
    assert len({r["name"] for r in rows})==len(rows)
    return raw,rows,len(obj)

def split(rows):
    hosts=sorted({r["host"] for r in rows})
    random.Random(SEED).shuffle(hosts)
    n=round(len(hosts)*.35)
    hold=set(hosts[:n])
    pool=[r for r in rows if r["host"] not in hold]
    test=[r for r in rows if r["host"] in hold]
    assert len(pool)>=50 and len(test)>=50
    return pool,test,len(hosts)

def fitting(samples):
    best=None
    for a,b in EXPONENTS:
        residuals=[r["y"]-a*r["x"]-b*r["z"] for r in samples]
        c=statistics.median(residuals)
        err=sum(min((r-c)**2,1.) for r in residuals)/len(residuals)
        # simple deterministic tie-break smaller absolute exponent
        key=(err,abs(a)+abs(b),a,b)
        if best is None or key<best[0]:best=(key,(a,b,c))
    return best[1],best[0][0]

def fit_candidates(samples):
    ranked=[]
    for a,b in EXPONENTS:
        c=statistics.median(r["y"]-a*r["x"]-b*r["z"] for r in samples)
        score=sum(min((r["y"]-a*r["x"]-b*r["z"]-c)**2,1.) for r in samples)/len(samples)
        ranked.append((score,a,b,c))
    ranked.sort()
    return ranked

def choose(pool,selected):
    """Query selection uses only public input features x,z; never unseen y."""
    seen={r["name"] for r in selected}
    candidates=fit_candidates(selected)[:8]
    values=[]
    for r in pool:
        if r["name"] in seen:continue
        ys=[a*r["x"]+b*r["z"]+c for _,a,b,c in candidates]
        disagreement=max(ys)-min(ys)
        # penalize outlying feature leverage (avoid extreme extrapolation)
        utility=disagreement
        values.append((utility,hashlib.sha256(r["name"].encode()).hexdigest(),r))
    assert values
    return min(values,key=lambda v:(-v[0],v[1]))[2]

def evaluate(formula,test):
    a,b,c=formula
    rel=[abs(math.exp(a*r["x"]+b*r["z"]+c-r["y"])-1) for r in test]
    logerr=[abs(a*r["x"]+b*r["z"]+c-r["y"]) for r in test]
    return dict(n=len(test),median_relative_error=statistics.median(rel),
        fraction_below_10_percent=sum(e<=.1 for e in rel)/len(rel),
        fraction_below_20_percent=sum(e<=.2 for e in rel)/len(rel),
        p90_relative_error=sorted(rel)[int(.9*(len(rel)-1))],
        median_log_error=statistics.median(logerr))

def run(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    raw,rows,n_raw=load()
    digest=hashlib.sha256(raw).hexdigest()
    (out/"nasa_pscomppars_snapshot.csv").write_bytes(raw)
    pool,test,n_hosts=split(rows)
    candidates=sorted(pool,key=lambda x:hashlib.sha256(
        ("initial-"+str(SEED)+":"+x["name"]).encode()).hexdigest())
    selected=candidates[:4]
    experiments=[]
    while len(selected)<BUDGET:
        formula,score=fitting(selected)
        x=choose(pool,selected)
        experiments.append(dict(n_before=len(selected),query_planet=x["name"],query_host=x["host"],
            previous_candidate_exponents=formula[:2],
            new_period_days=x["p"]))
        selected.append(x)
    formula,train_loss=fitting(selected)
    holdout=evaluate(formula,test)
    random_models=[]
    for rep in range(BASELINE_REPEATS):
        picks=random.Random(SEED+rep+1).sample(pool,BUDGET)
        f,_=fitting(picks)
        e=evaluate(f,test)
        random_models.append(dict(seed=SEED+rep+1,exponents=list(f[:2]),
            holdout_median_error=e["median_relative_error"],
            holdout_below_20_percent=e["fraction_below_20_percent"]))
    average_random=statistics.mean(x["holdout_median_error"] for x in random_models)
    count_active_better=sum(holdout["median_relative_error"]<x["holdout_median_error"] for x in random_models)
    # Hardest counterexample (no re-tuning after test)
    pred=lambda r:math.exp(formula[0]*r["x"]+formula[1]*r["z"]+formula[2])
    worst=sorted(test,key=lambda r:abs(pred(r)*365.25/r["p"]-1),reverse=True)[:8]
    top=[dict(name=r["name"],observed_period_days=r["p"],
        predicted_period_days=pred(r)*365.25,relative_error=abs(pred(r)*365.25/r["p"]-1),
        distance_au=r["a"],star_mass=r["m"]) for r in worst]
    report=dict(dataset="NASA Exoplanet Archive PSCompPars",source_url=URL,
        source_doi="10.26133/NEA13",raw_snapshot_sha256=digest,
        n_raw=n_raw,n_filtered=len(rows),n_unique_hosts=n_hosts,
        pool_size=len(pool),host_disjoint_holdout_size=len(test),
        discovery_budget=BUDGET,initial_observations=4,
        additional_active_queries=8,exponent_family_size=len(EXPONENTS),
        active_formula=dict(alpha=formula[0],beta=formula[1],log_scale=formula[2],
            period_years_scale=math.exp(formula[2])),
        active_holdout=holdout,random_baseline_mean_median_error=average_random,
        random_baseline_repeats=BASELINE_REPEATS,
        random_baseline_beaten=count_active_better,
        counterexamples_worst_holdout=top,
        limitations=[
            "Real astronomical catalogue; 'queries' reveal archival records, not new telescope experiments",
            "Some semi-major axes are computed from periods and stellar masses; potential target leakage at data-provenance level",
            "Candidate expression grammar is supplied (power laws); this is symbolic selection, not free-form law invention",
            "Intercept is fitted via median; this is parameter estimation, not neural-network training",
            "Holdout groups are distinct stars, but stars and planets are not independent physical experiments",
            "No Lean/C3 certification of the physical law; exoplanet deviations are empirical, with measurement errors and model caveats",
            "Outliers are catalog-specific counterexamples to a numerical tolerance, not disproof of celestial mechanics"
        ])
    (out/"report.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
    (out/"selected_experiments.json").write_text(json.dumps(experiments,indent=2)+"\n")
    (out/"random_baselines.json").write_text(json.dumps(random_models,indent=2)+"\n")
    print("NASA_REAL_DATA",n_raw,len(rows),"split",len(pool),len(test),"sha",digest,flush=True)
    print("DISCOVERED_FORMULA",formula,"holdout",holdout,"beat_random",
        count_active_better,"of",BASELINE_REPEATS,flush=True)
    print("FALSIFIER_EXAMPLES",top[:2],flush=True)
    return report

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_nasa")
