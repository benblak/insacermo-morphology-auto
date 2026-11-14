#!/usr/bin/env python3
"""POST-HOC NASA catalogue consistency review, fixed original PS test split.
Report EVERY 1-sigma interval-disjoint row with explicit witness data,
ratio bounds and source columns (provenance requires followup).
Not a new physics result. Do not change preregistered search/model.
"""
import csv,json,sys,math
from pathlib import Path
from exoplanet_law import filter_data,interval

rows,meta=filter_data(sys.argv[1])
output=Path(sys.argv[2]);output.mkdir(parents=True,exist_ok=True)
flags=[]
count={"yes":0,"no":0,"unknown":0}
for r in rows:
    if r["split"]!="test":continue
    val=interval(r)
    if val is None:count["unknown"]+=1;continue
    lo,hi=val
    if lo<=1<=hi:
        count["yes"]+=1
        continue
    count["no"]+=1
    ratio=r["P_years"]**2*r["m"]/r["a"]**3
    # How much lower or higher 1 is outside the derived propagated interval
    gap=lo if lo>1 else (1/hi)
    flag={"planet":r["pl_name"],"host":r["hostname"],
          "discoverymethod":r["discoverymethod"],"P_days":r["pl_orbper"],
          "P_err_plus_days":r["pl_orbpererr1"],"P_err_minus_days":r["pl_orbpererr2"],
          "a_au":r["pl_orbsmax"],"a_err_plus_au":r["pl_orbsmaxerr1"],
          "a_err_minus_au":r["pl_orbsmaxerr2"],
          "stellar_mass_solar":r["st_mass"],
          "stellar_mass_err_plus_solar":r["st_masserr1"],
          "stellar_mass_err_minus_solar":r["st_masserr2"],
          "R_point":ratio,"R_min":lo,"R_max":hi,
          "disjoint_factor":gap}
    flags.append(flag)
assert count=={"yes":422,"no":45,"unknown":66},count
flags.sort(key=lambda x:-x["disjoint_factor"])
path=output/"NASA_45_1SIGMA_DISJOINT_CASES.csv"
with path.open("w",newline="") as f:
    writer=csv.DictWriter(f,fieldnames=list(flags[0].keys()))
    writer.writeheader()
    writer.writerows(flags)
summary={"original_ps_csv_sha256":meta["file_sha256"],
         "test_n":533,"interval_compatible":422,
         "interval_disjoint":45,"interval_unknown":66,
         "flags_sorted_by_distance_to_interval":flags[:10],
         "meaning":"conditional compatibility of quoted 1-sigma intervals with R=1. This is not a formal physical refutation or a significance test.",
         "limitations":["possible derived semi-major axes",
                        "1-sigma intervals are statistical and not guaranteed bounds",
                        "period mass and separation may be correlated / source-dependent",
                        "planet mass omitted, binary/multi-star systems may violate simplification",
                        "catalogue may combine different data releases and conventions"]}
(output/"NASA_45_FLAGS_SUMMARY.json").write_text(json.dumps(summary,indent=2,ensure_ascii=False)+"\n")
print("CASE AUDIT",count)
print("SORTED TOP5",json.dumps(flags[:5],ensure_ascii=False))
print("OUTPUT",path)
print("NO_NEW_PHYSICS_CLAIM")
