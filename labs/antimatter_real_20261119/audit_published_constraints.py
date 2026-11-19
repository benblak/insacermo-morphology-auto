"""Independent checks for published arithmetic only, no fake experimental data.
References:
https://link.springer.com/article/10.1140/epjc/s10052-026-15384-x
https://link.springer.com/article/10.1140/epjc/s10052-018-6299-6
https://global-nu.org/results.html [PRELIMINARY Bari 2026.a]
https://science.osti.gov/np/Highlights/2026/4a
https://www.project8.org/about
"""
import json
from decimal import Decimal, getcontext
from pathlib import Path
import os
getcontext().prec=50
D=Decimal
OUT=Path(os.environ.get("REAL_BARYON_OUT","/tmp/insacermo-real-baryon"))
OUT.mkdir(parents=True,exist_ok=True)
d21=D("0.00007465")
d_atm=D("0.0024720")
s12=D("0.3047");s13=D("0.02218")
# Bari convention: Delta = m3² - (m1²+m2²)/2.
term=(1-s13)*s12*d21+s13*(d_atm+d21/2)
masses={}
for m in ("0.002","0.003","0.004"):
  m1=D(m)
  masses[m]=str((m1*m1+term).sqrt()*1000)
assert term==D("0.00007789818043610"),term
assert D("9.049")<D(masses["0.002"])<D("9.051")
assert D("9.689")<D(masses["0.004"])<D("9.691")
assert 900 < 338000
assert D("198") < D("214.2") < D("225")
assert max(D(x) for x in masses.values())<D(40)
out={
 "status":"arithmetic-only published-constraints audit; not a C3 certification of physical models",
 "EWBG_same_scale":{
   "phase_transition_GeV":[600,900],
   "eEDM_min_CPV_scale_GeV":338000,
   "arithmetic_intersection_empty":True,
   "caveat":"conditional on identifying EFT scales and on the published physical approximations; EDM is statistical"
 },
 "leptogenesis_specific_2018":{
   "delta_cp_degrees":[198,225],
   "Bari_preliminary_bestfit_degrees":214.2,
   "Bari_convention":"Delta_m3l² = m3²-(m1²+m2²)/2",
   "beta_mass_sq_offset_eV2":str(term),
   "beta_mass_meV_at_lightest_2_3_4_meV":masses,
   "KATRIN_bound_meV":450,
   "Project8_approx_goal_meV":40,
   "caveat":"theory remains compatible, not established; coarse Project8 goal is not an instrument detectability function"
 },
 "next_probe":"a real prediction calculator and error model needed to prove which measurement differentiates physical theories",
 "logical_warning":"Lean proves statements conditional on literals; does not certify measured values, prediction validity, exclusivity of models or statistical exclusion."
}
(OUT/"RESULTATS_PHYSIQUES_PUBLIES.json").write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n")
print(json.dumps(out,indent=2,ensure_ascii=False))
print("PUBLISHED_CONSTRAINTS_ARITHMETIC_SUCCESS")
