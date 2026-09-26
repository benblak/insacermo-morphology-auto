# INSACERMO — Rhea stoichiometric resource-competition stress test V1
#
# Purpose
# -------
# Test the general INSACERMO future-bundle semantics outside ordinary graphs.
# Here, actions are stoichiometric reactions and states are finite molecular
# inventories (Petri-net/resource semantics).  We deliberately do NOT project
# chemistry to a molecule->molecule graph.
#
# Data
# ----
# Current public Rhea TSV release files (CC BY 4.0):
#   rhea-directions.tsv
#   rhea-reaction-smiles.tsv
#   rhea-chebi-smiles.tsv
#   chebiId_name.tsv
#
# Rhea convention used here:
# - every reaction has direction-specific siblings;
# - we use ONLY the explicit left-to-right member from rhea-directions.tsv;
# - this is a structural stoichiometric direction, not a claim about a specific
#   cell's thermodynamic/physiological flux direction.
#
# Stress test
# -----------
# Search all LR reactions for two distinct reactions that each consume one unit
# of the same non-currency ChEBI participant P and have distinct target products.
#
# Baseline inventory = sum of the reactant multisets of both reactions.
# Destruction        = remove exactly one unit of P.
#
# Then:
#   - target A must remain individually producible,
#   - target B must remain individually producible,
#   - producing both targets by firing both reactions must become impossible,
#   - adding one unit of P must repair the pair.
#
# This is a real-data LOCAL STOICHIOMETRIC MODULE witness.  It is not a claim
# that the pair is impossible in the full biochemical universe: external Rhea
# reactions could replenish P.  The point is to test INSACERMO under resource
# consumption, where the SCC/state-goal theorem is not the governing certificate.

from __future__ import annotations

import csv
import hashlib
import io
import itertools
import re
import urllib.request
from collections import Counter, defaultdict

BASE = "https://ftp.expasy.org/databases/rhea/tsv/"
FILES = {
    "directions": BASE + "rhea-directions.tsv",
    "reaction_smiles": BASE + "rhea-reaction-smiles.tsv",
    "chebi_smiles": BASE + "rhea-chebi-smiles.tsv",
    "names": BASE + "chebiId_name.tsv",
}

CURRENCY_NAME_PATTERNS = (
    "water", "h2o", "proton", "hydron", "dioxygen", "oxygen", "phosphate",
    "diphosphate", "pyrophosphate", "carbon dioxide", "co2", "ammonium",
    "nad+", "nadh", "nadp+", "nadph", "atp", "adp", "amp", "coa",
    "coenzyme a",
)


def download(url: str) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": "INSACERMO/1.0"})
    with urllib.request.urlopen(req, timeout=180) as r:
        return r.read()


def decode(raw: bytes) -> str:
    return raw.decode("utf-8-sig", errors="replace")


def norm_key(s: str) -> str:
    return re.sub(r"[^a-z0-9]+", "", (s or "").lower())


def read_tsv(raw: bytes):
    text = decode(raw)
    rows = list(csv.reader(io.StringIO(text), delimiter="\t"))
    return [r for r in rows if r and any(x.strip() for x in r)]


def header_map(row):
    return {norm_key(v): i for i, v in enumerate(row)}


def find_col(hmap, candidates):
    cs = [norm_key(x) for x in candidates]
    for c in cs:
        if c in hmap:
            return hmap[c]
    for key, idx in hmap.items():
        if any(c in key or key in c for c in cs):
            return idx
    return None


def parse_directions(raw):
    rows = read_tsv(raw)
    h = header_map(rows[0])
    i_master = find_col(h, ["MASTER_ID", "RHEA_ID_MASTER", "MASTER"])
    i_lr = find_col(h, ["RHEA_ID_LR", "ID_LR", "LEFT_TO_RIGHT", "LR"])
    if i_master is None or i_lr is None:
        raise RuntimeError(f"Cannot resolve directions columns: {rows[0]}")
    out = {}
    for r in rows[1:]:
        if len(r) <= max(i_master, i_lr):
            continue
        m = r[i_master].strip().replace("RHEA:", "")
        lr = r[i_lr].strip().replace("RHEA:", "")
        if m and lr:
            out[lr] = m
    return out, rows[0]


def parse_reaction_smiles(raw):
    rows = read_tsv(raw)
    # Current Rhea release may provide this export headerless as:
    #   <RHEA_ID>\t<reaction SMILES>
    first = rows[0]
    headerless = len(first) >= 2 and first[0].strip().replace("RHEA:", "").isdigit() and ">>" in first[1]
    if headerless:
        i_id, i_rxn, start = 0, 1, 0
        reported_header = ["HEADERLESS_RHEA_ID", "HEADERLESS_REACTION_SMILES"]
    else:
        h = header_map(first)
        i_id = find_col(h, ["RHEA_ID", "RHEAID", "ID"])
        i_rxn = find_col(h, ["REACTION_SMILES", "REACTIONSMILES", "SMILES"])
        if i_id is None or i_rxn is None:
            raise RuntimeError(f"Cannot resolve reaction-smiles columns: {first}")
        start = 1
        reported_header = first
    out = {}
    for r in rows[start:]:
        if len(r) <= max(i_id, i_rxn):
            continue
        rid = r[i_id].strip().replace("RHEA:", "")
        rxn = r[i_rxn].strip()
        if rid and ">>" in rxn:
            out[rid] = rxn
    return out, reported_header


def parse_chebi_smiles(raw):
    rows = read_tsv(raw)
    h = header_map(rows[0])
    i_id = find_col(h, ["CHEBI_ID", "CHEBIID", "ID"])
    i_sm = find_col(h, ["SMILES"])
    start = 1
    if i_id is None or i_sm is None:
        # Defensive fallback for a two-column headerless export.
        i_id, i_sm, start = 0, 1, 0
    sm_to_ids = defaultdict(list)
    for r in rows[start:]:
        if len(r) <= max(i_id, i_sm):
            continue
        cid = r[i_id].strip()
        sm = r[i_sm].strip()
        if cid and sm:
            if not cid.upper().startswith("CHEBI:") and cid.isdigit():
                cid = "CHEBI:" + cid
            sm_to_ids[sm].append(cid)
    return sm_to_ids, rows[0]


def parse_names(raw):
    rows = read_tsv(raw)
    # This file is documented as 2 columns and may be headerless.
    start = 0
    if rows and ("chebi" in rows[0][0].lower() or "name" in " ".join(rows[0]).lower()):
        if not rows[0][0].strip().upper().startswith("CHEBI:"):
            start = 1
    out = {}
    for r in rows[start:]:
        if len(r) < 2:
            continue
        cid = r[0].strip()
        name = r[1].strip()
        if not cid.upper().startswith("CHEBI:") and cid.isdigit():
            cid = "CHEBI:" + cid
        if cid and name:
            out[cid] = name
    return out


def participant_counter(side: str, sm_to_ids):
    c = Counter()
    unresolved = []
    for sm in [x for x in side.split(".") if x]:
        ids = sm_to_ids.get(sm, [])
        if not ids:
            unresolved.append(sm)
            continue
        # A canonical SMILES may occasionally map to more than one ChEBI ID.
        # For an exact-resource witness we require an unambiguous mapping.
        uniq = sorted(set(ids))
        if len(uniq) != 1:
            unresolved.append(sm)
            continue
        c[uniq[0]] += 1
    return c, unresolved


def enabled(inv: Counter, need: Counter) -> bool:
    return all(inv[k] >= v for k, v in need.items())


def fire(inv: Counter, left: Counter, right: Counter):
    if not enabled(inv, left):
        return None
    out = inv.copy()
    for k, v in left.items():
        out[k] -= v
    for k, v in right.items():
        out[k] += v
    return out


def can_fire_both(inv, r1, r2):
    a = fire(inv, r1["left"], r1["right"])
    if a is not None and fire(a, r2["left"], r2["right"]) is not None:
        return True
    b = fire(inv, r2["left"], r2["right"])
    if b is not None and fire(b, r1["left"], r1["right"]) is not None:
        return True
    return False


def name_of(cid, names):
    return names.get(cid, cid)


def currency(cid, names):
    n = name_of(cid, names).lower()
    return any(p in n for p in CURRENCY_NAME_PATTERNS)


def main():
    raw = {k: download(v) for k, v in FILES.items()}
    sha = {k: hashlib.sha256(v).hexdigest() for k, v in raw.items()}

    lr_to_master, directions_header = parse_directions(raw["directions"])
    rxn_smiles, smiles_header = parse_reaction_smiles(raw["reaction_smiles"])
    sm_to_ids, chebi_smiles_header = parse_chebi_smiles(raw["chebi_smiles"])
    names = parse_names(raw["names"])

    reactions = []
    unresolved_lr = 0
    for lr_id, master in lr_to_master.items():
        rxn = rxn_smiles.get(lr_id)
        if not rxn:
            continue
        left_sm, right_sm = rxn.split(">>", 1)
        left, ul = participant_counter(left_sm, sm_to_ids)
        right, ur = participant_counter(right_sm, sm_to_ids)
        if ul or ur or not left or not right:
            unresolved_lr += 1
            continue
        # Exclude degenerate net-no-change transforms.
        if left == right:
            continue
        reactions.append({
            "lr": lr_id,
            "master": master,
            "left": left,
            "right": right,
            "rxn_smiles": rxn,
        })

    by_reactant = defaultdict(list)
    reactant_freq = Counter()
    for i, r in enumerate(reactions):
        for p, coeff in r["left"].items():
            reactant_freq[p] += 1
            if coeff == 1 and p not in r["right"]:
                by_reactant[p].append(i)

    candidates = []
    for p, idxs in by_reactant.items():
        if len(idxs) < 2 or currency(p, names):
            continue
        # Avoid extremely ubiquitous cofactors while retaining real branch points.
        freq = reactant_freq[p]
        if freq > 40:
            continue
        for i, j in itertools.combinations(idxs, 2):
            r1, r2 = reactions[i], reactions[j]
            if r1["master"] == r2["master"]:
                continue

            # Find one distinct target on each right side not already required
            # on either left side and not shared across the two reactions.
            left_union = set(r1["left"]) | set(r2["left"])
            t1s = [x for x in r1["right"] if x not in left_union and x not in r2["right"]]
            t2s = [x for x in r2["right"] if x not in left_union and x not in r1["right"]]
            if not t1s or not t2s:
                continue
            t1, t2 = sorted(t1s)[0], sorted(t2s)[0]

            # Baseline has exactly enough resources to execute both reactions.
            baseline = r1["left"] + r2["left"]
            destroyed = baseline.copy()
            destroyed[p] -= 1

            single1 = enabled(destroyed, r1["left"])
            single2 = enabled(destroyed, r2["left"])
            pair_before = can_fire_both(baseline, r1, r2)
            pair_after = can_fire_both(destroyed, r1, r2)
            repaired = destroyed.copy()
            repaired[p] += 1
            pair_repaired = can_fire_both(repaired, r1, r2)

            if not (single1 and single2 and pair_before and not pair_after and pair_repaired):
                continue

            # Prefer interpretable local modules: rare common resource, few total
            # participants, named distinct targets.
            complexity = sum(r1["left"].values()) + sum(r2["left"].values())
            complexity += sum(r1["right"].values()) + sum(r2["right"].values())
            score = (freq, complexity, name_of(p, names), int(r1["lr"]), int(r2["lr"]))
            candidates.append((score, p, t1, t2, r1, r2, baseline, destroyed))

    print("INSACERMO_RHEA_STOICHIOMETRIC_RESOURCE_STRESS_V1")
    print("STATUS EXPLORATORY_REAL_CHEMISTRY_RESOURCE_WITNESS")
    print("SEMANTICS FINITE_INVENTORY_PETRI_NET_LOCAL_MODULE")
    print("RHEA_DIRECTION_CONVENTION EXPLICIT_LEFT_TO_RIGHT_MEMBER_ONLY")
    print("SCC_STATE_GOAL_CERTIFICATE_APPLICABLE 0")
    print("GENERAL_INSACERMO_BUNDLE_SEMANTICS_APPLICABLE 1")
    for k in FILES:
        print("SOURCE_URL", k, FILES[k])
        print("SOURCE_SHA256", k, sha[k])
    print("DIRECTIONS_HEADER", "|".join(directions_header))
    print("REACTION_SMILES_HEADER", "|".join(smiles_header))
    print("CHEBI_SMILES_HEADER", "|".join(chebi_smiles_header))
    print("LR_DIRECTION_IDS", len(lr_to_master))
    print("PARSED_LR_REACTIONS", len(reactions))
    print("UNRESOLVED_LR_REACTIONS", unresolved_lr)
    print("CANDIDATE_RESOURCE_CONFLICT_WITNESSES", len(candidates))

    if not candidates:
        print("RESULT NO_WITNESS_FOUND")
        return

    candidates.sort(key=lambda x: x[0])
    _, p, t1, t2, r1, r2, baseline, destroyed = candidates[0]

    def fmt(c):
        return "; ".join(f"{name_of(k,names)} [{k}] x{v}" for k, v in sorted(c.items()))

    print("SHARED_LIMITING_RESOURCE", name_of(p, names), p)
    print("RESOURCE_REACTION_FREQUENCY", reactant_freq[p])
    print("REACTION_A_LR", "RHEA:" + r1["lr"], "MASTER", "RHEA:" + r1["master"])
    print("REACTION_A_LEFT", fmt(r1["left"]))
    print("REACTION_A_RIGHT", fmt(r1["right"]))
    print("REACTION_B_LR", "RHEA:" + r2["lr"], "MASTER", "RHEA:" + r2["master"])
    print("REACTION_B_LEFT", fmt(r2["left"]))
    print("REACTION_B_RIGHT", fmt(r2["right"]))
    print("TARGET_A", name_of(t1, names), t1)
    print("TARGET_B", name_of(t2, names), t2)
    print("BASELINE_RESOURCE_UNITS", baseline[p])
    print("AFTER_DESTRUCTION_RESOURCE_UNITS", destroyed[p])
    print("TARGET_A_INDIVIDUALLY_FEASIBLE_AFTER", int(enabled(destroyed, r1["left"])))
    print("TARGET_B_INDIVIDUALLY_FEASIBLE_AFTER", int(enabled(destroyed, r2["left"])))
    print("PAIR_FEASIBLE_BEFORE", int(can_fire_both(baseline, r1, r2)))
    print("PAIR_FEASIBLE_AFTER", int(can_fire_both(destroyed, r1, r2)))
    repaired = destroyed.copy(); repaired[p] += 1
    print("PAIR_FEASIBLE_AFTER_ADD_ONE_RESOURCE_REPAIR", int(can_fire_both(repaired, r1, r2)))
    print("MINIMAL_LOST_BUNDLE_ORDER", 2)
    print("MECHANISM STOICHIOMETRIC_RESOURCE_COMPETITION")
    print("DESTRUCTION REMOVE_ONE_UNIT_OF_SHARED_RESOURCE")
    print("REPAIR ADD_ONE_UNIT_OF_SHARED_RESOURCE")
    print("LIMITATION local_two_reaction_module_not_whole_cell_or_global_rhea_replenishment")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
