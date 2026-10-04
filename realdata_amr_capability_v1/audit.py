from __future__ import annotations

import hashlib
import itertools
import json
import re
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import defaultdict
from pathlib import Path

import numpy as np
import pandas as pd

VERSION = "INSACERMO_REALDATA_AMR_CAPABILITY_VS_PROBES_V1"
SOURCE = "NCBI BioSample antibiogram records"
SPECIES = "Salmonella enterica"
MAX_RECORDS = 3000
BATCH_SIZE = 200
SLEEP_SECONDS = 0.36

# Frozen before endpoint opening.
ANTIBIOTICS = (
    "ampicillin",
    "ceftriaxone",
    "ciprofloxacin",
    "gentamicin",
    "tetracycline",
    "chloramphenicol",
    "nalidixic acid",
    "trimethoprim-sulfamethoxazole",
)
BASE_SIZE = 3
MAX_PROBES = 3

ALIASES = {
    "ampicillin": {"ampicillin"},
    "ceftriaxone": {"ceftriaxone"},
    "ciprofloxacin": {"ciprofloxacin"},
    "gentamicin": {"gentamicin"},
    "tetracycline": {"tetracycline"},
    "chloramphenicol": {"chloramphenicol"},
    "nalidixic acid": {"nalidixicacid"},
    "trimethoprim-sulfamethoxazole": {
        "trimethoprimsulfamethoxazole",
        "trimethoprimsulphamethoxazole",
        "sulfamethoxazoletrimethoprim",
        "sulphamethoxazoletrimethoprim",
    },
}


def compact(s: str) -> str:
    return re.sub(r"[^a-z0-9]+", "", str(s).lower())


def canonical_antibiotic(value: str):
    x = compact(value)
    for canon, aliases in ALIASES.items():
        if x in aliases:
            return canon
    return None


def canonical_pheno(value: str):
    x = str(value).strip().lower()
    if x in {"s", "susceptible", "sensitive"} or x.startswith("suscept"):
        return "S"
    if x in {"r", "resistant"} or x.startswith("resist"):
        return "R"
    return None


def get_json(url: str):
    req = urllib.request.Request(url, headers={"User-Agent": "INSACERMO-realdata-audit/1.0"})
    with urllib.request.urlopen(req, timeout=180) as r:
        return json.loads(r.read())


def get_bytes(url: str):
    req = urllib.request.Request(url, headers={"User-Agent": "INSACERMO-realdata-audit/1.0"})
    with urllib.request.urlopen(req, timeout=180) as r:
        return r.read()


def esearch_ids():
    term = f'{SPECIES}[orgn] AND antibiogram[filter]'
    params = {
        "db": "biosample",
        "term": term,
        "retmax": str(MAX_RECORDS),
        "retmode": "json",
    }
    url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?" + urllib.parse.urlencode(params)
    obj = get_json(url)
    result = obj["esearchresult"]
    ids = result["idlist"]
    return int(result["count"]), ids, url


def parse_ast_rows(xml_bytes: bytes):
    root = ET.fromstring(xml_bytes)
    rows = []
    for bs in root.findall(".//BioSample"):
        accession = bs.attrib.get("accession")
        if not accession:
            idnode = bs.find(".//Ids/Id[@db='BioSample']")
            accession = None if idnode is None else (idnode.text or "").strip()
        if not accession:
            continue

        for table in bs.findall(".//Table"):
            headers = [
                (cell.text or "").strip()
                for cell in table.findall("./Header//Cell")
            ]
            if not headers:
                continue
            norm_headers = [compact(h) for h in headers]
            for row in table.findall("./Body//Row"):
                cells = [(cell.text or "").strip() for cell in row.findall("./Cell")]
                if not cells:
                    continue
                if len(cells) < len(headers):
                    cells += [""] * (len(headers) - len(cells))
                rec = {norm_headers[i]: cells[i] for i in range(min(len(headers), len(cells)))}

                drug = None
                for key in ("antibiotic", "drug"):
                    if key in rec and rec[key]:
                        drug = canonical_antibiotic(rec[key])
                        break
                if drug is None:
                    continue

                pheno = None
                for key in ("phenotype", "resistancephenotype", "sir"):
                    if key in rec and rec[key]:
                        pheno = canonical_pheno(rec[key])
                        break
                if pheno is None:
                    continue

                rows.append((accession, drug, pheno))
    return rows


def fetch_snapshot():
    total_count, ids, search_url = esearch_ids()
    all_rows = []
    xml_hash = hashlib.sha256()
    fetched_ids = []

    for start in range(0, len(ids), BATCH_SIZE):
        batch = ids[start:start+BATCH_SIZE]
        params = {
            "db": "biosample",
            "id": ",".join(batch),
            "retmode": "xml",
        }
        url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?" + urllib.parse.urlencode(params)
        raw = get_bytes(url)
        xml_hash.update(raw)
        fetched_ids.extend(batch)
        all_rows.extend(parse_ast_rows(raw))
        time.sleep(SLEEP_SECONDS)

    Path("realdata_amr_capability_v1").mkdir(exist_ok=True)
    ids_payload = {
        "species": SPECIES,
        "total_matching_biosamples": total_count,
        "max_records": MAX_RECORDS,
        "fetched_ids": fetched_ids,
    }
    ids_text = json.dumps(ids_payload, indent=2, sort_keys=True)
    Path("realdata_amr_capability_v1/snapshot_ids.json").write_text(ids_text, encoding="utf-8")
    ids_sha = hashlib.sha256(ids_text.encode()).hexdigest()

    return all_rows, total_count, ids_sha, xml_hash.hexdigest(), search_url


def build_matrix(rows):
    obs = defaultdict(lambda: defaultdict(set))
    for accession, drug, pheno in rows:
        obs[accession][drug].add(pheno)

    records = []
    ambiguous = 0
    for accession, bydrug in obs.items():
        rec = {"BioSample": accession}
        ok = True
        for drug in ANTIBIOTICS:
            vals = bydrug.get(drug, set())
            if len(vals) == 1:
                rec[drug] = next(iter(vals))
            else:
                ok = False
                if len(vals) > 1:
                    ambiguous += 1
                break
        if ok:
            records.append(rec)

    df = pd.DataFrame(records)
    if not df.empty:
        df = df.sort_values("BioSample").reset_index(drop=True)
    return df, ambiguous


def repair_price(probe_cols, action_cols, df):
    if not probe_cols:
        groups = [(None, df)]
    else:
        groups = list(df.groupby(list(probe_cols), dropna=False, sort=True))

    total = 0
    for _, g in groups:
        counts = [(g[a] == "S").sum() for a in action_cols]
        total += len(g) - int(max(counts))
    return int(total)


def best_probe_frontier(df, base_actions, probe_pool):
    out = []
    for k in range(MAX_PROBES + 1):
        combos = [()] if k == 0 else itertools.combinations(probe_pool, k)
        best = None
        for combo in combos:
            price = repair_price(combo, base_actions, df)
            candidate = (price, tuple(combo))
            if best is None or candidate < best:
                best = candidate
        out.append({
            "k": k,
            "repair_price": int(best[0]),
            "witness": list(best[1]),
        })
    return out


def scenario(df, base_actions, added):
    base_actions = tuple(base_actions)
    expanded = base_actions + (added,)
    probe_pool = tuple(a for a in ANTIBIOTICS if a not in expanded)

    # Frozen cohort rule: actionable under the base portfolio.
    mask = np.zeros(len(df), dtype=bool)
    for a in base_actions:
        mask |= (df[a].to_numpy() == "S")
    cohort = df.loc[mask].reset_index(drop=True)

    base_zero = repair_price((), base_actions, cohort)
    expanded_zero = repair_price((), expanded, cohort)
    frontier = best_probe_frontier(cohort, base_actions, probe_pool)

    match_k = None
    for p in frontier:
        if p["repair_price"] <= expanded_zero:
            match_k = p["k"]
            break

    return {
        "base_actions": list(base_actions),
        "added_action": added,
        "probe_pool": list(probe_pool),
        "cohort_n": int(len(cohort)),
        "base_zero_probe_repair": base_zero,
        "expanded_zero_probe_repair": expanded_zero,
        "absolute_repair_reduction": int(base_zero - expanded_zero),
        "fractional_repair_reduction": (
            0.0 if base_zero == 0 else float((base_zero - expanded_zero) / base_zero)
        ),
        "base_probe_frontier": frontier,
        "probes_needed_to_match_added_capability": (
            match_k if match_k is not None else f">{MAX_PROBES}"
        ),
    }


def main():
    rows, total_count, ids_sha, xml_sha, search_url = fetch_snapshot()
    df, ambiguous = build_matrix(rows)

    scenarios = []
    for base in itertools.combinations(ANTIBIOTICS, BASE_SIZE):
        for added in ANTIBIOTICS:
            if added not in base:
                scenarios.append(scenario(df, base, added))

    scenarios.sort(
        key=lambda s: (
            -s["absolute_repair_reduction"],
            -s["fractional_repair_reduction"],
            tuple(s["base_actions"]),
            s["added_action"],
        )
    )

    report = {
        "version": VERSION,
        "source": SOURCE,
        "species": SPECIES,
        "search_url": search_url,
        "total_matching_biosamples": total_count,
        "max_records_fetched": MAX_RECORDS,
        "snapshot_ids_sha256": ids_sha,
        "concatenated_xml_sha256": xml_sha,
        "parsed_ast_rows": len(rows),
        "complete_eight_antibiotic_isolates": int(len(df)),
        "ambiguous_isolates_excluded": int(ambiguous),
        "antibiotics": list(ANTIBIOTICS),
        "base_size": BASE_SIZE,
        "max_probes": MAX_PROBES,
        "scenario_count": len(scenarios),
        "scenarios": scenarios,
    }
    Path("realdata_amr_capability_v1/report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True), encoding="utf-8"
    )

    print(VERSION)
    print("total_matching_biosamples", total_count)
    print("fetched_cap", MAX_RECORDS)
    print("snapshot_ids_sha256", ids_sha)
    print("concatenated_xml_sha256", xml_sha)
    print("parsed_ast_rows", len(rows))
    print("complete_eight_antibiotic_isolates", len(df))
    print("ambiguous_isolates_excluded", ambiguous)
    print("scenario_count", len(scenarios))
    print("TOP_SCENARIOS")
    for s in scenarios[:10]:
        print(json.dumps(s, sort_keys=True))

    if scenarios:
        top = scenarios[0]
        print("TOP_BASE", "+".join(top["base_actions"]))
        print("TOP_ADDED", top["added_action"])
        print("TOP_COHORT_N", top["cohort_n"])
        print("TOP_BASE_ZERO", top["base_zero_probe_repair"])
        print("TOP_EXPANDED_ZERO", top["expanded_zero_probe_repair"])
        print("TOP_ABS_REDUCTION", top["absolute_repair_reduction"])
        print("TOP_FRAC_REDUCTION", f'{top["fractional_repair_reduction"]:.12f}')
        print("TOP_FRONTIER", [x["repair_price"] for x in top["base_probe_frontier"]])
        print("TOP_MATCH_K", top["probes_needed_to_match_added_capability"])

    # Structural checks only; no scientific endpoint is pre-filled.
    assert len(ANTIBIOTICS) == 8
    assert len(scenarios) == 280
    assert total_count > 0
    assert len(rows) > 0
    assert len(df) >= 50
    assert all(s["expanded_zero_probe_repair"] <= s["base_zero_probe_repair"] for s in scenarios)

    print("AUDIT_PASS")


if __name__ == "__main__":
    main()
