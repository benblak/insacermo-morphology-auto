import csv
import importlib.util
import io
import re
import urllib.request

# Reuse exactly the already-validated France rail topology/scenario.
spec = importlib.util.spec_from_file_location(
    "france_rail_base",
    "experiments/france_rail_structural_audit_v1.py",
)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)

FREQ_URL = (
    "https://ressources.data.sncf.com/explore/dataset/frequentation-gares/"
    "download/?format=csv&timezone=Europe%2FParis&use_labels_for_header=true&csv_separator=%3B"
)

with urllib.request.urlopen(FREQ_URL, timeout=120) as r:
    freq_raw = r.read()

text = freq_raw.decode("utf-8-sig")
rows = list(csv.DictReader(io.StringIO(text), delimiter=";"))
assert rows, "empty station-frequency dataset"

def field_key(row, exact=None, contains=None):
    keys = list(row)
    if exact is not None:
        for k in keys:
            if k.strip().lower() == exact.lower():
                return k
    if contains is not None:
        for k in keys:
            if contains.lower() in k.strip().lower():
                return k
    raise KeyError((exact, contains, keys))

uic_key = field_key(rows[0], exact="Code UIC")
voy_key = field_key(rows[0], contains="Total Voyageurs 2024")

def clean_int(x):
    if x is None:
        return None
    s = str(x).strip()
    if not s:
        return None
    # Opendatasoft CSV may contain spaces/nonbreaking spaces as thousands sep.
    s = s.replace("\u202f", "").replace("\xa0", "").replace(" ", "")
    s = s.replace(",", ".")
    try:
        return int(round(float(s)))
    except ValueError:
        return None

freq_by_uic = {}
for row in rows:
    uic = re.sub(r"\D", "", row.get(uic_key, ""))
    voy = clean_int(row.get(voy_key))
    if uic and voy is not None:
        freq_by_uic[uic[-8:]] = voy

def gtfs_uic(stop_id):
    digits = re.sub(r"\D", "", stop_id)
    assert len(digits) >= 8, stop_id
    return digits[-8:]

passengers = {}
missing = []
for t in base.targets:
    uic = gtfs_uic(t)
    if uic not in freq_by_uic:
        missing.append((t, uic, base.station_name.get(t, t)))
    else:
        passengers[t] = freq_by_uic[uic]

assert not missing, f"unmatched target stations: {missing}"
assert all(passengers[t] > 0 for t in base.targets)

def contract_weight(bundle):
    # Passenger-exposure proxy: sum of 2024 annual station passenger counts
    # of all future obligations in the contract.
    return sum(passengers[q] for q in bundle)

total_mass = sum(contract_weight(b) for b in base.Gamma)
assert total_mass > 0

weighted = {}
for state in base.restoration_sets:
    hard_mass = 0
    soft_mass = 0
    safe_mass = 0
    dmap = base.depths[state]
    for b in base.Gamma:
        w = contract_weight(b)
        d = dmap[b]
        if d is None:
            hard_mass += w
        elif d > base.DEADLINE:
            soft_mass += w
        else:
            safe_mass += w
    assert hard_mass + soft_mass + safe_mass == total_mass
    weighted[state] = {
        "hard_mass": hard_mass,
        "soft_mass": soft_mass,
        "safe_mass": safe_mass,
        "hard_risk": hard_mass / total_mass,
        "deadline_risk": (hard_mass + soft_mass) / total_mass,
        "safe_share": safe_mass / total_mass,
    }

admissible = [s for s in base.restoration_sets if len(s) <= base.BUDGET]

best_hard_weighted = min(
    admissible,
    key=lambda s: (
        weighted[s]["hard_risk"],
        weighted[s]["deadline_risk"],
        len(s),
        tuple(sorted(s)),
    ),
)
best_deadline_weighted = min(
    admissible,
    key=lambda s: (
        weighted[s]["deadline_risk"],
        weighted[s]["hard_risk"],
        len(s),
        tuple(sorted(s)),
    ),
)

best_hard_unweighted = min(
    admissible,
    key=lambda s: (
        base.results[s]["hard"],
        base.results[s]["miss"],
        len(s),
        tuple(sorted(s)),
    ),
)
best_deadline_unweighted = min(
    admissible,
    key=lambda s: (
        base.results[s]["miss"],
        base.results[s]["hard"],
        len(s),
        tuple(sorted(s)),
    ),
)

def label(state):
    if not state:
        return "NONE"
    return "+".join(base.station_name.get(s, s) for s in sorted(state))

print("INSACERMO_FRANCE_RAIL_PASSENGER_WEIGHTED_AUDIT_V1")
print("STATUS EXPLORATORY_SOCIOECONOMIC_EXPOSURE_PROXY")
print("FREQUENTATION_SOURCE", FREQ_URL)
print("FREQUENTATION_YEAR", 2024)
print("MATCHED_TARGETS", len(passengers))
print("CONTRACT_WEIGHT passenger-exposure=sum_2024_station_passengers")
print("WARNING weighted mass is a prioritization proxy, not passengers stranded and not euros")
print("TOTAL_WEIGHTED_CONTRACT_MASS", total_mass)

for i, t in enumerate(base.targets, 1):
    print(
        "WEIGHT_TARGET", i,
        "UIC", gtfs_uic(t),
        "NAME", base.station_name.get(t, t),
        "PASSENGERS_2024", passengers[t],
    )

for state in sorted(base.restoration_sets, key=lambda x: (len(x), tuple(sorted(x)))):
    w = weighted[state]
    print(
        "WEIGHTED_RESTORED", label(state),
        "HARD_RISK", f"{w['hard_risk']:.12f}",
        "DEADLINE_RISK", f"{w['deadline_risk']:.12f}",
        "SAFE_SHARE", f"{w['safe_share']:.12f}",
        "HARD_MASS", w["hard_mass"],
        "SOFT_MASS", w["soft_mass"],
        "SAFE_MASS", w["safe_mass"],
    )

print("UNWEIGHTED_BEST_HARD_REPAIR", label(best_hard_unweighted))
print("WEIGHTED_BEST_HARD_REPAIR", label(best_hard_weighted))
print("UNWEIGHTED_BEST_DEADLINE_REPAIR", label(best_deadline_unweighted))
print("WEIGHTED_BEST_DEADLINE_REPAIR", label(best_deadline_weighted))
print(
    "HARD_DECISION_CHANGED_BY_PASSENGER_WEIGHTING",
    int(best_hard_unweighted != best_hard_weighted),
)
print(
    "DEADLINE_DECISION_CHANGED_BY_PASSENGER_WEIGHTING",
    int(best_deadline_unweighted != best_deadline_weighted),
)
print("RESULT COMPLETE")
