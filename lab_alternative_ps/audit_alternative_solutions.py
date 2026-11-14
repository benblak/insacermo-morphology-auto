#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
INSACERMO — EXOPLANET INDEPENDENT-SOLUTION PROVENANCE AUDIT
Predeclared 2026-11-14 before fetching alternative PS solutions.

Keep the exact original 45 flags and default dataset frozen. For each planet:
* Find all NASA Exoplanet Archive PS literature solution rows with P, a, M.
* Exclude the default row from alternative-solution comparison.
* Does ANY alternate literature row have R=P_years^2*M/a^3 inside its
  quoted 1-sigma propagated interval [Rmin,Rmax]? If yes, classify
  "alternative explains within quoted 1-sigma intervals".
* Also count alternate point solutions within 5% of R=1, as a separate
  weaker criterion (cannot be conflated with interval consistency).
* If no complete alternate, classify "unresolved due to missing solution",
  NOT physical anomaly.
* Record the solution reference in pl_refname; do not equate separate
  catalogue solutions with independently measured semi-major axes.
* This is EXPLORATORY cross-source audit, not independent physical discovery.
* Any favorable alternative is cherry-selected by existence, so use
  diagnostic evidence only, not a calibrated probability of inconsistency.
* Distinguish 'same published row' vs cross-paper metrics. Keep baseline flag.
"""
import csv,io,math,json,hashlib,collections,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"lab_exoplanets"))
from exoplanet_law import filter_data, interval, finite

def relratio(r):
    p=finite(r.get("pl_orbper"))
    a=finite(r.get("pl_orbsmax"))
    m=finite(r.get("st_mass"))
    if p is None or a is None or m is None or min(p,a,m)<=0:return None
    return (p/365.25)**2*m/a**3

def alt_analysis(default_csv,all_ps_csv,outdir):
    default,source=filter_data(default_csv)
    flagged=[]
    for d in default:
        if d["split"]!="test":continue
        b=interval(d)
        if b is not None and not (b[0]<=1<=b[1]):
            flagged.append(d)
    if len(flagged)!=45:
        raise ValueError(f"Frozen original flags changed: got {len(flagged)} not 45")
    raw=Path(all_ps_csv).read_bytes()
    records=list(csv.DictReader(io.StringIO(raw.decode("utf-8-sig"))))
    groups=collections.defaultdict(list)
    for r in records:
        if r.get("pl_name"):groups[r["pl_name"]].append(r)
    out=[]
    counts=collections.Counter()
    for d in flagged:
        name=d["pl_name"]
        original=relratio(d)
        alternatives=[]
        for r in groups[name]:
            if r.get("default_flag")=="1":continue
            ratio=relratio(r)
            if ratio is None:continue
            b=interval(r)
            compatible_interval=bool(b is not None and b[0]<=1<=b[1])
            close_5percent=bool(abs(math.log(ratio))<=math.log(1.05))
            alternatives.append({
                "reference":r.get("pl_refname",""),
                "ratio":ratio,
                "period_days":r.get("pl_orbper"),
                "semimajor_axis_au":r.get("pl_orbsmax"),
                "stellar_mass_solar":r.get("st_mass"),
                "bounds":b,
                "interval_complete":b is not None,
                "compatible_1sigma":compatible_interval,
                "close_5pct":close_5percent
            })
        alternatives.sort(key=lambda r:abs(math.log(r["ratio"])))
        has_any=bool(alternatives)
        has_interval=any(v["compatible_1sigma"] for v in alternatives)
        has_near=any(v["close_5pct"] for v in alternatives)
        interval_n=sum(v["interval_complete"] for v in alternatives)
        status=("ALTERNATIVE_1SIGMA_COMPATIBLE" if has_interval else
                "ALTERNATIVE_POINT_WITHIN_5PCT_ONLY" if has_near else
                "NO_COMPLETE_ALTERNATIVE" if not has_any else
                "ALTERNATIVES_STILL_DISJOINT_OR_NO_ERRORS")
        counts[status]+=1
        out.append({
            "planet":name,
            "hostname":d["hostname"],
            "original_ratio":original,
            "original_bounds":interval(d),
            "status":status,
            "number_alternative_complete_triplets":len(alternatives),
            "number_alternative_complete_intervals":interval_n,
            "has_alternative_1sigma_compatible":has_interval,
            "has_alternative_point_within5pct":has_near,
            "best_alternative":alternatives[0] if alternatives else None,
            "first_3_alternatives":alternatives[:3],
            "all_alternatives":alternatives,
        })
    out.sort(key=lambda r:r["planet"])
    assert len(out)==45
    results={
        "study":"INSACERMO exoplanets — 45 default-solution flags vs alternative NASA literature solutions",
        "frozen_default_sha256":source["file_sha256"],
        "alternative_nasa_ps_sha256":hashlib.sha256(raw).hexdigest(),
        "frozen_45_flags":len(out),
        "status_counts":dict(counts),
        "n_flags_with_complete_alternatives":sum(r["number_alternative_complete_triplets"]>0 for r in out),
        "n_flags_with_1sigma_compatible_alternative":sum(r["has_alternative_1sigma_compatible"] for r in out),
        "n_flags_with_near5pct_point_alternative":sum(r["has_alternative_point_within5pct"] for r in out),
        "n_flags_no_alt_triplets":sum(r["number_alternative_complete_triplets"]==0 for r in out),
        "cases":out,
        "limitations":[
            "An alternate catalogue solution may derive semi-major axis from the period and stellar mass itself.",
            "Selection of the most compatible alternate is posthoc existence; not an independent confirmation.",
            "A quoted 1-sigma interval is not a hard bound; correlations and model assumptions are ignored.",
            "A mismatch may reflect source provenance rather than any novel physical phenomenon.",
            "The original 45 flags were discovered on an earlier holdout; this is an exploratory diagnostic, not an independent new holdout."
        ]
    }
    outdir=Path(outdir);outdir.mkdir(parents=True,exist_ok=True)
    (outdir/"alternative_solutions_audit.json").write_text(json.dumps(results,indent=2,ensure_ascii=False)+"\n")
    with (outdir/"alternative_solutions_summary.csv").open("w",newline="",encoding="utf-8") as f:
        w=csv.DictWriter(f,fieldnames=["planet","hostname","original_ratio","status","number_alternative_complete_triplets","number_alternative_complete_intervals","has_alternative_1sigma_compatible","has_alternative_point_within5pct","best_alternative_reference","best_alternative_ratio"])
        w.writeheader()
        for r in out:
            z={k:r.get(k) for k in w.fieldnames}
            z["best_alternative_reference"]=r["best_alternative"]["reference"] if r["best_alternative"] else None
            z["best_alternative_ratio"]=r["best_alternative"]["ratio"] if r["best_alternative"] else None
            w.writerow(z)
    print("FROZEN FLAGS",len(out),"EXPLORATORY CROSS-SOLUTION DATA")
    print("STATUS COUNTS",dict(counts))
    print("ALTERNATE COMPLETE",results["n_flags_with_complete_alternatives"])
    print("ALTERNATE 1SIGMA COMPATIBLE",results["n_flags_with_1sigma_compatible_alternative"])
    print("ALTERNATE POINT NEAR 5PCT",results["n_flags_with_near5pct_point_alternative"])
    print("NO ALTERNATE TRIPLETS",results["n_flags_no_alt_triplets"])
    for item in out:
        if item["planet"] in ("OGLE2-TR-L9 b","TOI-2274 b","K2-318 b"):
            print("EXAMPLE",item["planet"],json.dumps({k:v for k,v in item.items() if k!="all_alternatives"},ensure_ascii=False))
    print("FILE",outdir/"alternative_solutions_audit.json")
    print("PHYSICAL_DISCOVERY_CERTIFIED=NO")

if __name__=="__main__":
    if len(sys.argv)!=4:sys.exit("usage: audit_alternative_solutions.py default_ps.csv alternate_ps.csv out_dir")
    alt_analysis(sys.argv[1],sys.argv[2],sys.argv[3])
