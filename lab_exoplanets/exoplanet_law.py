#!/usr/bin/env python3
# coding: utf-8
"""
INSACERMO — DISCOVERY-BY-CONSTRAINTS / EXOPLANET ORBITAL LAW
PRE-REGISTRATION (created before the archive's planetary data are downloaded).

Objective: search for a simple power law P ~ C*a^p*M^q using real data.
This is intentionally an attempt to REDISCOVER a known physical relationship
(Kepler's 3rd law), NOT a claim to invent a novel universal law.

Primary data: NASA Exoplanet Archive TAP PS (default_flag=1).
Columns: pl_name, hostname, discoverymethod, pl_orbper, pl_orbsmax,
st_mass, and uncertainties & parameter-ref names when available.
No ML model training, but TRAIN median offset is explicitly data fitted.

Critical CIRCULARITY caveat: Archive pl_orbsmax is frequently DERIVED from
period and stellar mass rather than measured independently. Success on such
rows DOES NOT independently validate Kepler nor discover a physical law.
We will attempt to partition rows by provenance/ref names and uncertainty
availability and flag suspicious high agreement. Claims restricted to
"catalog consistency/redetection" absent independent orbital measurements.

DATA FILTER (frozen):
 - default_flag==1
 - P,a,M positive finite, 0.2<M<5 solar masses,
 - 0.003<a<100 au, 0.2<P<50000 days
 - source table 'ps', not merging multiple source rows
 - sort by planet name; deterministic group split HOSTNAME via SHA256
   keyed to 20261114; train if hash mod 10 < 6, calibration if 6..7,
   test if 8..9.
 - if fewer than 100 test rows: report INCONCLUSIVE and no scientific claim.

CANDIDATE EQUATION SEARCH (preregistered):
 p,q in increments 0.5, p in {0, .5, 1, 1.5, 2, 2.5, 3},
 q in {-1.5,-1,-.5,0,.5,1,1.5}, total 49;
 fit c = median(log(Pyears) - p*log(a) - q*log(M)) on TRAIN.
 rank by median absolute log residual on train, ties p,q ascending.
 Evaluate selected candidate on heldout, plus:
 - known Kepler p=1.5, q=-0.5, with intercept calibrated from TRAIN;
 - a-only p=1.5,q=0;
 - constant P p=0,q=0;
 - negative control: SHUFFLE mass across test with fixed Random(20261114);
 - holdout residual quantiles, 5% and 10% tolerance rates.

UNCERTAINTY / OBSERVABILITY:
 for rows with supplied errors on all three variables, construct 1-sigma
 intervals in (P,a,M), compute a CONSTRAINT-CONSISTENCY interval for
 R=Pyears^2*M/a^3. ACT_CONSISTENT if 1 lies in that interval;
 REFUSE if uncertainty incomplete; FLAG_DISJOINT if 1 outside interval.
 This is *interval consistency*, NOT truth, nor a 68% simultaneous confidence
 guarantee, and 1-sigma errors are not hard bounds.

A meaningful NEW scientific discovery would require independent observations,
unmodeled predictive success, and peer review; this protocol does not assert it.
"""
import csv,hashlib,io,random,math,json,statistics,sys
from pathlib import Path

SEED=20261114
FIELDS=["pl_name","hostname","discoverymethod","pl_orbper","pl_orbsmax",
        "st_mass","pl_orbpererr1","pl_orbpererr2","pl_orbsmaxerr1",
        "pl_orbsmaxerr2","st_masserr1","st_masserr2"]
QUERY="select "+",".join(FIELDS)+" from ps where default_flag=1 and pl_orbper is not null and pl_orbsmax is not null and st_mass is not null"
SOURCE="https://exoplanetarchive.ipac.caltech.edu/TAP/sync"

def finite(v):
    try:
        a=float(v)
        return a if math.isfinite(a) else None
    except (ValueError,TypeError):return None

def data_split(row):
    h=hashlib.sha256(("INSACERMO-20261114|"+row["hostname"]).encode()).digest()[0]%10
    return "train" if h<=5 else "cal" if h<=7 else "test"

def quant(vals,q):
    if not vals:return None
    z=sorted(vals);t=q*(len(z)-1);lo=int(t);hi=min(lo+1,len(z)-1)
    return z[lo]*(hi-t)+z[hi]*(t-lo)

def median(vals):
    return statistics.median(vals)

def filter_data(path):
    raw=Path(path).read_bytes()
    rows=[]
    for record in csv.DictReader(io.StringIO(raw.decode("utf-8-sig"))):
        p=finite(record["pl_orbper"]);a=finite(record["pl_orbsmax"]);m=finite(record["st_mass"])
        if p is None or a is None or m is None:continue
        if not (0.2 < p < 50000 and .003 < a < 100 and .2 < m < 5):continue
        if not record["hostname"] or not record["pl_name"]:continue
        record["P_years"]=p/365.25
        record["a"]=a
        record["m"]=m
        record["y"]=math.log(record["P_years"])
        record["x"]=math.log(a)
        record["z"]=math.log(m)
        record["split"]=data_split(record)
        rows.append(record)
    assert len(rows)>=100,("insufficient catalogue rows",len(rows))
    rows.sort(key=lambda r:r["pl_name"])
    return rows,{"file_sha256":hashlib.sha256(raw).hexdigest(),"rows_filtered":len(rows),
                 "tap_query":QUERY,"server":SOURCE}

def residual(row,p,q,c):
    return row["y"]-(c+p*row["x"]+q*row["z"])

def fit_c(rows,p,q):
    return median([r["y"]-p*r["x"]-q*r["z"] for r in rows])

def score(rows,p,q,c):
    errors=[abs(residual(r,p,q,c)) for r in rows]
    return {"median_abs_log_error":median(errors),
            "p90_abs_log_error":quant(errors,.9),
            "within_5pct":sum(x<=math.log(1.05) for x in errors)/len(errors),
            "within_10pct":sum(x<=math.log(1.10) for x in errors)/len(errors),
            "n":len(rows)}

def interval(r):
    # conventional physical ratio: Kepler P_years^2 * M / a^3 approximately 1
    fields=(("pl_orbper","pl_orbpererr1","pl_orbpererr2"),
            ("pl_orbsmax","pl_orbsmaxerr1","pl_orbsmaxerr2"),
            ("st_mass","st_masserr1","st_masserr2"))
    ranges=[]
    for field,up,down in fields:
        center=finite(r[field])
        plus=finite(r[up]);minus=finite(r[down])
        if center is None or plus is None or minus is None:
            return None
        if plus < 0 or minus > 0:return None
        low=center+minus; high=center+plus
        if low<=0 or high<=low:return None
        ranges.append((low,high))
    (p0,p1),(a0,a1),(m0,m1)=ranges
    lo=(p0/365.25)**2 * m0 / a1**3
    hi=(p1/365.25)**2 * m1 / a0**3
    assert lo<=hi
    return lo,hi

def audit(path,outdir):
    rows,info=filter_data(path)
    groups={k:[r for r in rows if r["split"]==k] for k in ("train","cal","test")}
    train=groups["train"];test=groups["test"];cal=groups["cal"]
    if min(map(len,(train,cal,test)))<100:
        raise ValueError("INCONCLUSIVE: fewer than 100 rows in one required split")
    candidates=[]
    for p2 in range(7):
        for q2 in range(-3,4):
            p=p2/2;q=q2/2;c=fit_c(train,p,q)
            candidates.append({"p":p,"q":q,"c":c,
                               "training_error":score(train,p,q,c)["median_abs_log_error"]})
    candidates.sort(key=lambda r:(r["training_error"],r["p"],r["q"]))
    selected=candidates[0]

    def candidate_report(p,q,label):
        c=fit_c(train,p,q)
        return {"name":label,"p":p,"q":q,"c":c,"train":score(train,p,q,c),
                "cal":score(cal,p,q,c),"test":score(test,p,q,c)}

    selected_report=candidate_report(selected["p"],selected["q"],"search_winner")
    known=candidate_report(1.5,-.5,"classical_kepler")
    without_mass=candidate_report(1.5,0,"a_only")
    constant=candidate_report(0,0,"constant_period")
    # explicitly confirm the negative control is not inadvertently superior
    mass_test=list(test)
    shuffled=[r["z"] for r in mass_test]
    random.Random(SEED).shuffle(shuffled)
    shuffled_rows=[dict(r,z=newmass) for r,newmass in zip(mass_test,shuffled)]
    negative=score(shuffled_rows,1.5,-.5,known["c"])

    interval_counts={"COMPATIBLE_INTERVAL":0,"FLAG_DISJOINT":0,"REFUSE_INCOMPLETE":0}
    example_flags=[]
    for r in test:
        bounds=interval(r)
        if bounds is None:interval_counts["REFUSE_INCOMPLETE"]+=1
        elif bounds[0]<=1<=bounds[1]:interval_counts["COMPATIBLE_INTERVAL"]+=1
        else:
            interval_counts["FLAG_DISJOINT"]+=1
            if len(example_flags)<10:
                example_flags.append({"planet":r["pl_name"],"R_interval":bounds,
                                      "P_days":r["pl_orbper"],"a_AU":r["a"],"M_solar":r["m"]})
    # Circularity test: R values almost exactly one strongly indicate derived a
    ratios=[r["P_years"]**2*r["m"]/r["a"]**3 for r in test]
    suspicious_exact=sum(abs(math.log(t))<.001 for t in ratios)
    result={
        "protocol":"pre-registered finite exponent grid on NASA exoplanet table, no holdout tuning",
        "dataset":info,
        "splits":{k:{"rows":len(v),"hosts":len(set(r["hostname"] for r in v))}
                  for k,v in groups.items()},
        "searched_candidates":len(candidates),
        "top_10_candidates":candidates[:10],
        "known_law":"Kepler orbital law: P_years^2 proportional to a_AU^3/M_solar",
        "models":[selected_report,known,without_mass,constant],
        "negative_mass_permutation_test":negative,
        "holdout_uncertainty_interval_audit":interval_counts,
        "flagged_examples":example_flags,
        "exact_kepler_ratio_within_0.1pct_count":suspicious_exact,
        "sample_kepler_ratios":[{"planet":r["pl_name"],"R":r["P_years"]**2*r["m"]/r["a"]**3}
                                 for r in test[:8]],
        "interpretation":{
            "possible_circularity":"Semi-major axis often inferred from period and mass; apparent relation may be algebraic catalog dependency.",
            "interval_results":"1-sigma intervals are not hard physical guarantees.",
            "novelty":"Kepler was published centuries ago. This is not a novel physical law.",
            "independent_validation":"Needs a real independent orbital-separation measurement provenance audit."
        }
    }
    outdir=Path(outdir);outdir.mkdir(parents=True,exist_ok=True)
    (outdir/"exoplanet_law_results.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print("NASA PS DATA",info)
    print("SPLITS",result["splits"])
    print("GRID_BEST",selected)
    for m in result["models"]:
        print("MODEL",m["name"],"exponents",m["p"],m["q"],
              "train_medlog",m["train"]["median_abs_log_error"],
              "TEST_MEDLOG",m["test"]["median_abs_log_error"],
              "TEST_WITHIN_5PCT",m["test"]["within_5pct"])
    print("NEGATIVE_PERMUTED_MASS",negative)
    print("INTERVALS",interval_counts)
    print("SUSPICIOUS_RATIO_WITHIN_0.1PCT",suspicious_exact,"/",len(test))
    print("WARNING: catalog dependencies mean this does NOT constitute independent physical discovery")
    print("OUTPUT",outdir/"exoplanet_law_results.json")

if __name__=="__main__":
    if len(sys.argv)!=3:sys.exit("usage: exoplanet_law.py official_tap.csv results_dir")
    audit(sys.argv[1],sys.argv[2])
