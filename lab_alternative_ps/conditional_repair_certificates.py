#!/usr/bin/env python3
# coding: utf-8
"""
INSACERMO — EXPLICIT ONE-VARIABLE REPAIR CERTIFICATE FOR THE ORIGINAL 45 FLAGS.

Frozen original 45 flags; NO model retuning.

For each flagged default solution:
  the Kepler-compatible semi-major axis in astronomical units would be
      a* = (P_years**2 * M_solar)**(1/3).
  Intersecting its permitted range from the reported P & M 1-sigma endpoints
  with the quoted a 1-sigma interval requires a minimal a-interval expansion:
      required_a_low = (P_low_years**2 * M_low)**(1/3)
      required_a_high = (P_high_years**2 * M_high)**(1/3)
      gap_AU = max(required_a_low - a_high, a_low - required_a_high, 0)
  This minimum gap is a NUMERICAL DISTANCE BETWEEN INTERVALS.
  It is NOT an independent physical measurement, and not proof a is wrong.
  It also ignores covariances, planet mass and binarity.
  An alternate published row may give a different internally consistent fit.

Diagnostics:
  root(s) of inconsistency may be P, M, a, correlated values, wrong sources,
  numerical rounding, a missing model term, or planet mass. The script does
  NOT select a unique physical cause.
"""
import csv,io,math,sys,collections,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"lab_exoplanets"))
from exoplanet_law import filter_data,interval,finite

def closed_interval(r,key):
    x=finite(r[key])
    down=finite(r[key+"err2"])
    up=finite(r[key+"err1"])
    if x is None or up is None or down is None or x+down<=0:return None
    if up<0 or down>0:return None
    return (x+down,x+up)

def main(frozen_csv,alternative_results_json,output_folder):
    original,meta=filter_data(frozen_csv)
    results=json.loads(Path(alternative_results_json).read_text())
    assert results["frozen_default_sha256"]==meta["file_sha256"],"default file hash mismatch"
    alts={x["planet"]:x for x in results["cases"]}
    flags=[]
    for r in original:
        if r["split"]!="test":continue
        v=interval(r)
        if v is None or v[0]<=1<=v[1]:continue
        (p0,p1)=closed_interval(r,"pl_orbper")
        (a0,a1)=closed_interval(r,"pl_orbsmax")
        (m0,m1)=closed_interval(r,"st_mass")
        Pyears=(r["P_years"])
        M=r["m"]
        a0star=(p0/365.25)**(2/3) * m0**(1/3)
        a1star=(p1/365.25)**(2/3) * m1**(1/3)
        astar=(Pyears**2*M)**(1/3)
        # disjoint A intervals are mathematically equivalent to R-interval disjoint for P,M>0
        gap=max(0,a0star-a1,a0-a1star)
        assert gap>0, (r["pl_name"],v,astar,(a0,a1),(a0star,a1star))
        # minimum target change to nominal a, not a measured independent modification.
        nominal_delta=astar-r["a"]
        case=dict(
            planet=r["pl_name"],
            original_a_au=r["a"], compatible_nominal_a_au=astar,
            nominal_delta_au=nominal_delta,
            nominal_delta_pct_relative_to_catalog_a=100*nominal_delta/r["a"],
            catalog_a_1sigma_low=a0,catalog_a_1sigma_high=a1,
            kepler_required_a_1sigma_low=a0star,
            kepler_required_a_1sigma_high=a1star,
            interval_distance_gap_au=gap,
            original_ratio_r=r["P_years"]**2*r["m"]/r["a"]**3,
            original_ratio_low=v[0],original_ratio_high=v[1],
            alternative_status=alts[r["pl_name"]]["status"],
            original_has_alternate_compatible=alts[r["pl_name"]]["has_alternative_1sigma_compatible"],
            caveat="conditional consistency, not a correction or an independent distance measurement"
        )
        flags.append(case)
    assert len(flags)==45
    counts=dict(collections.Counter(x["alternative_status"] for x in flags))
    flags.sort(key=lambda x:-abs(x["nominal_delta_pct_relative_to_catalog_a"]))
    dest=Path(output_folder);dest.mkdir(parents=True,exist_ok=True)
    with (dest/"NASA_45_CONDITIONAL_REPAIR_CERTIFICATES.csv").open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=list(flags[0]))
        w.writeheader();w.writerows(flags)
    summary=dict(
        cases=45,source_sha256=meta["file_sha256"],
        status_counts=counts,
        top5_by_nominal_correction=flags[:5],
        examples={name:next((x for x in flags if x["planet"]==name),None)
                  for name in ("OGLE2-TR-L9 b","TOI-2274 b","K2-318 b")},
        theorem="The two intervals for a cannot overlap iff the original Kepler R interval excludes 1 (for positive P,a,M and independent endpoint propagation).",
        limitations=["conditional on the approximate mass-dominant Kepler equation",
                     "correlated quoted uncertainties treated as independent marginal bounds",
                     "nominal target does not tell which measurement or scientific model is wrong",
                     "catalogue may contain semimajor axes derived from period and stellar mass"]
    )
    (dest/"NASA_45_REPAIR_SUMMARY.json").write_text(json.dumps(summary,indent=2,ensure_ascii=False)+"\n")
    print("EXACT CONDITIONAL REPAIR CERTIFICATES: 45/45")
    print("STATUS COUNTS",counts)
    for name,v in summary["examples"].items():
        print("REPAIR",name,json.dumps({
            k:v[k] for k in ("original_a_au","compatible_nominal_a_au",
                            "nominal_delta_pct_relative_to_catalog_a",
                            "interval_distance_gap_au","alternative_status")
        }) if v else "NOT FOUND")
    print("CAVEAT: numerical witness, no new law or physical anomaly proven")

if __name__=="__main__":
    if len(sys.argv)!=4:raise SystemExit("usage: conditional_repair.py original_ps.csv alternative_solutions_audit.json outputdir")
    main(*sys.argv[1:])
