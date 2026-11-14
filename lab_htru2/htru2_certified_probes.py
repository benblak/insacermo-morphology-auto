#!/usr/bin/env python3
# coding: utf-8
"""
INSACERMO: HTRU2 real radio-pulsar candidates; pre-registered finite-world audit.
This is a NEW laboratory test, not a modification of the frozen engine.
Code written before fetching/examining the dataset's actual values or labels.

PRE-REGISTERED PRIMARY DESIGN (unchanged after seeing results):
  Data: original HTRU2 CSV, UCI dataset #372 (17,898 rows; 8 measurements, 0/1 label).
  Split: random.Random(20261114), shuffle row indices; first 80% training, rest holdout.
  Observation alphabet: for each feature, >= TRAIN median (binary); eight probes,
     fixed by unsupervised medians, no label-dependent thresholds or retuning.
  Actions: label 0, label 1, or REFUSE.
  Finite reference contract: ACT only when ALL training reference worlds consistent
     with observations have the same label. REFUSE if no further possible observation
     can ever yield a reference-pure full signature; REFUSE on out-of-reference data.
  Adaptive: EXACT dynamic programming minimizes expected number of probes over
     training reference worlds, subject to that contract. Each probe costs one.
  Fixed: EXACT best globally fixed order (all 8! represented by subset DP), with
     identical early ACT/REFUSE stopping criteria.
  Evaluation: frozen train DP/order applied to untouched holdout; report real
     action error rate, coverage, refusal, mean probe counts. If any holdout
     ACT is wrong, explain certification is only for closed training reference.
  No ML model training. Data-dependent median binarization and optimization over
     train labels ARE used, so do not claim "learning nothing from data".
  No energy/power or real-world observatory time is measured.

Data source must be https://archive.ics.uci.edu/static/public/372/htru2.zip
or the legacy official UCI URL if unavailable.
License CC BY 4.0. Robert Lyon, HTRU2, https://doi.org/10.24432/C5DK6R
"""
import collections
import csv
import functools
import hashlib
import itertools
import json
import random
import statistics
import sys
import zipfile
from pathlib import Path

SEED = 20261114
N_FEATURES = 8
ALL_MASK = (1 << N_FEATURES) - 1
N_SIG = 1 << N_FEATURES
SOURCE = "https://archive.ics.uci.edu/static/public/372/htru2.zip"
FEATURES = [
    "Profile_mean","Profile_stdev","Profile_skewness","Profile_kurtosis",
    "DM_mean","DM_stdev","DM_skewness","DM_kurtosis",
]

def load_dataset(zip_path):
    zip_path = Path(zip_path)
    blob = zip_path.read_bytes()
    with zipfile.ZipFile(zip_path) as z:
        csv_names = [n for n in z.namelist() if n.endswith("HTRU_2.csv")]
        if len(csv_names) != 1:
            raise ValueError("HTRU_2.csv not uniquely found: "+str(z.namelist()))
        raw = z.read(csv_names[0])
    rows = []
    labels = []
    for i, row in enumerate(csv.reader(raw.decode("utf-8-sig").splitlines()), 1):
        if not row or not any(row):
            continue
        if len(row) != 9:
            raise ValueError(f"line {i}: {len(row)} columns instead of 9")
        v = tuple(float(s) for s in row[:8])
        label = int(row[8])
        if label not in (0, 1):
            raise ValueError(f"line {i}: non-binary label")
        if not all(float("-inf") < x < float("inf") for x in v):
            raise ValueError("nonfinite feature")
        rows.append(v)
        labels.append(label)
    if len(rows) != 17898 or sum(labels) != 1639:
        raise ValueError(f"Unexpected data shape/count: {len(rows)}, positives={sum(labels)}")
    return rows, labels, {
        "uci_zip_sha256": hashlib.sha256(blob).hexdigest(),
        "csv_sha256": hashlib.sha256(raw).hexdigest(),
        "original_csv_bytes": len(raw),
        "source": SOURCE,
        "license": "CC BY 4.0",
        "credit": "Robert Lyon, HTRU2, DOI:10.24432/C5DK6R",
    }

def bin_sig(row, medians):
    out = 0
    for j, v in enumerate(row):
        if v >= medians[j]:
            out |= 1 << j
    return out

def compute_model(rows, labels, train_idx):
    medians = [statistics.median(rows[i][j] for i in train_idx) for j in range(N_FEATURES)]
    hist = [[0, 0] for _ in range(N_SIG)]
    for i in train_idx:
        hist[bin_sig(rows[i], medians)][labels[i]] += 1
    return medians, hist

def enumerate_submasks(mask):
    sub = mask
    while True:
        yield sub
        if sub == 0:
            return
        sub = (sub - 1) & mask

def plan(hist):
    # Each (observed-feature mask, observed 1-bits) is an epistemic belief cell.
    @functools.lru_cache(None)
    def info(mask, bits):
        c0 = c1 = 0
        can_ever_act = False
        for sig, cnt in enumerate(hist):
            if sig & mask != bits:
                continue
            c0 += cnt[0]
            c1 += cnt[1]
            if (cnt[0] == 0) != (cnt[1] == 0):
                can_ever_act = True
        return c0, c1, can_ever_act

    def terminal(mask, bits):
        c0, c1, can_ever_act = info(mask, bits)
        if not (c0+c1):
            return "REFUSE_OOD"
        if c0 == 0:
            return "ACT_1"
        if c1 == 0:
            return "ACT_0"
        if not can_ever_act:
            return "REFUSE_ABSOLUTE"
        if mask == ALL_MASK:
            return "REFUSE_ABSOLUTE"
        return None

    # Optimal adaptive path, expectation with empirical training-world probabilities.
    choices = {}
    @functools.lru_cache(None)
    def adaptive_cost(mask, bits):
        c0, c1, _ = info(mask, bits)
        if terminal(mask, bits) is not None:
            return 0.0
        n = c0 + c1
        assert n > 0
        best = float("inf")
        chosen = None
        for j in range(N_FEATURES):
            bit = 1 << j
            if mask & bit:
                continue
            n0, n1, _ = info(mask | bit, bits)
            m0 = n0 + n1
            p0 = m0 / n
            n0, n1, _ = info(mask | bit, bits | bit)
            m1 = n0 + n1
            assert m0 + m1 == n
            val = 1 + p0 * adaptive_cost(mask | bit, bits) + (m1/n) * adaptive_cost(mask | bit, bits | bit)
            if val < best - 1e-12:
                best = val
                chosen = j
        assert chosen is not None
        choices[(mask, bits)] = chosen
        return best

    total_train = sum(sum(x) for x in hist)
    a_cost = adaptive_cost(0, 0)

    # Fixed-order expected cost: at a prefix, count training worlds that have
    # not stopped yet. Optimal fixed order via DP on feature subsets (2**8 states).
    @functools.lru_cache(None)
    def unresolved_mass(mask):
        count = 0
        for bits in enumerate_submasks(mask):
            if terminal(mask, bits) is None:
                c0, c1, _ = info(mask, bits)
                count += c0 + c1
        return count

    fixed_choices = {}
    @functools.lru_cache(None)
    def fixed_cost(mask):
        if mask == ALL_MASK:
            return 0.0
        unresolved = unresolved_mass(mask) / total_train
        best = float("inf")
        chosen = None
        for j in range(N_FEATURES):
            bit = 1 << j
            if mask & bit:
                continue
            value = unresolved + fixed_cost(mask | bit)
            if value < best - 1e-12:
                best = value
                chosen = j
        fixed_choices[mask] = chosen
        return best

    f_cost = fixed_cost(0)
    order = []
    mask = 0
    while mask != ALL_MASK:
        j = fixed_choices[mask]
        order.append(j)
        mask |= (1 << j)
    assert sorted(order) == list(range(N_FEATURES))
    assert a_cost <= f_cost + 1e-9, (a_cost, f_cost)

    def apply_one(full_sig, mode):
        mask = bits = asked = 0
        while True:
            dec = terminal(mask, bits)
            if dec is not None:
                return dec, asked
            if mode == "adaptive":
                j = choices[(mask, bits)]
            else:
                j = order[asked]
                assert (mask & (1 << j)) == 0
            bit = 1 << j
            mask |= bit
            if full_sig & bit:
                bits |= bit
            asked += 1
            assert asked <= N_FEATURES

    return {
        "medians_info": info, "terminal": terminal,
        "train_opt_adaptive_probes": a_cost,
        "train_opt_fixed_probes": f_cost,
        "best_fixed_feature_order": order,
        "optimized_adaptive_states": len(choices),
        "reference_nonempty_signatures": sum(sum(x)>0 for x in hist),
        "reference_pure_signatures": sum((x[0] == 0) != (x[1] == 0) for x in hist),
        "reference_mixed_signatures": sum(x[0] > 0 and x[1] > 0 for x in hist),
        "apply_one": apply_one,
    }

def evaluate(indexes, rows, labels, medians, apply_one, mode):
    totals = collections.Counter()
    samples = []
    for ix in indexes:
        full = bin_sig(rows[ix], medians)
        verdict, cost = apply_one(full, mode)
        y = labels[ix]
        totals["n"] += 1
        totals["probes"] += cost
        totals["max_probes"] = max(totals["max_probes"], cost)
        totals["positives"] += y
        totals["negatives"] += 1 - y
        if verdict.startswith("ACT_"):
            pred = int(verdict[-1])
            totals["acted"] += 1
            totals["acted_positives"] += y
            totals["action_errors"] += pred != y
            totals["false_pulsar"] += (pred == 1 and y == 0)
            totals["missed_pulsar"] += (pred == 0 and y == 1)
            totals[f"act_{pred}"] += 1
            if pred != y and len(samples) < 6:
                samples.append({"row_index":ix, "true":y, "act":pred, "probes":cost, "sig":full})
        else:
            totals["refused"] += 1
            totals[verdict] += 1
    N = len(indexes)
    out = dict(totals)
    out.update({
        "mean_probes":totals["probes"]/N,
        "coverage":totals["acted"]/N,
        "conditional_action_error_rate":(totals["action_errors"]/totals["acted"] if totals["acted"] else None),
        "errors_over_all":totals["action_errors"]/N,
        "error_examples":samples
    })
    return out

def main():
    if len(sys.argv) != 3:
        sys.exit("Usage: python3 htru2_certified_probes.py <official-htru2.zip> <output_folder>")
    zip_path, outdir = Path(sys.argv[1]), Path(sys.argv[2])
    outdir.mkdir(parents=True,exist_ok=True)
    rows, labels, data_info = load_dataset(zip_path)
    rng = random.Random(SEED)
    indices = list(range(len(rows)))
    rng.shuffle(indices)
    train = indices[:len(rows)*4//5]
    holdout = indices[len(rows)*4//5:]
    # Test labels never used to choose medians, a probing order or DP.
    medians, hist = compute_model(rows, labels, train)
    m = plan(hist)
    a_train = evaluate(train,rows,labels,medians,m["apply_one"],"adaptive")
    f_train = evaluate(train,rows,labels,medians,m["apply_one"],"fixed")
    a_test = evaluate(holdout,rows,labels,medians,m["apply_one"],"adaptive")
    f_test = evaluate(holdout,rows,labels,medians,m["apply_one"],"fixed")
    assert a_train["action_errors"] == f_train["action_errors"] == 0
    assert abs(a_train["mean_probes"]-m["train_opt_adaptive_probes"]) < 1e-10
    assert abs(f_train["mean_probes"]-m["train_opt_fixed_probes"]) < 1e-10
    # The contract is the same for both policies; only inspection order changes.
    assert a_train["acted"] == f_train["acted"]
    assert a_test["acted"] == f_test["acted"]
    assert a_test["action_errors"] == f_test["action_errors"]

    output={
        "protocol":{"seed":SEED,"split":"80/20 row-shuffle, no stratification","n_total":len(rows),
                    "n_train":len(train),"n_holdout":len(holdout),
                    "eight_binary_probes":">= training median per feature",
                    "actions":["ACT_0","ACT_1","REFUSE"],
                    "strategy":"exact DP expected-probe minimization; best fixed exact subset DP",
                    "certification":"finite training-world reference only, not unseen data"},
        "data":data_info,
        "medians":dict(zip(FEATURES, medians)),
        "reference_histogram":hist,
        "strategy":{"train_opt_adaptive_probes":m["train_opt_adaptive_probes"],
                    "train_opt_fixed_probes":m["train_opt_fixed_probes"],
                    "best_fixed_feature_order":[FEATURES[j] for j in m["best_fixed_feature_order"]],
                    "optimized_adaptive_states":m["optimized_adaptive_states"],
                    "reference_nonempty_signatures":m["reference_nonempty_signatures"],
                    "reference_pure_signatures":m["reference_pure_signatures"],
                    "reference_mixed_signatures":m["reference_mixed_signatures"]},
        "results":{"training_adaptive":a_train,"training_best_fixed":f_train,
                   "holdout_adaptive":a_test,"holdout_best_fixed":f_test}
    }
    # Summary written after the frozen holdout is evaluated. Not retuned.
    (outdir/"htru2_results.json").write_text(json.dumps(output,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    with (outdir/"htru2_reference_signatures.csv").open("w",newline="",encoding="utf-8") as f:
        writer=csv.writer(f)
        writer.writerow(["binary_signature","training_label_0","training_label_1","reference_verdict"])
        for i,x in enumerate(hist):
            verdict = "EMPTY" if sum(x)==0 else "MIXED" if all(x) else "ACT_0" if x[0] else "ACT_1"
            writer.writerow([f"{i:08b}",x[0],x[1],verdict])
    summary=(
        "# INSACERMO — HTRU2, expérience sur données radio réelles\n\n"
        "Protocole fixé avant téléchargement et lecture des observations. "
        "Source UCI HTRU2, Robert Lyon, DOI:10.24432/C5DK6R, licence CC BY 4.0.\n\n"
        f"- Taille : {len(rows)} candidats; {len(train)} référence, {len(holdout)} cachés pour le choix de politique.\n"
        f"- Référence : {m['reference_pure_signatures']} signatures pures, "
        f"{m['reference_mixed_signatures']} mélangées, "
        f"{m['reference_nonempty_signatures']} signatures observées.\n"
        f"- Moyenne optimale d'observations, référence : adaptatif {a_train['mean_probes']:.4f}, "
        f"meilleur ordre fixe {f_train['mean_probes']:.4f}.\n"
        f"- Moyenne hors échantillon : adaptatif {a_test['mean_probes']:.4f}, "
        f"meilleur ordre fixe {f_test['mean_probes']:.4f}.\n"
        f"- Hors échantillon : couverture des décisions {a_test['coverage']:.2%}; "
        f"{a_test['action_errors']} décisions erronées sur {a_test['acted']} décisions prises; "
        f"{a_test['refused']} refus sur {a_test['n']} candidats.\n"
        f"- Sur les décisions erronées : {a_test.get('false_pulsar',0)} faux pulsars proposés, "
        f"{a_test.get('missed_pulsar',0)} vrais pulsars écartés.\n\n"
        "ATTENTION : 'certifié' signifie garanti uniquement sur l'univers FINI des "
        "exemples de référence compatibles avec les observations. Aucun théorème "
        "ne garantit les étiquettes des candidats nouveaux. Un nombre d'erreurs "
        "positif en holdout contredit toute prétention à la certitude hors échantillon. "
        "Les sondes mesurent le nombre de caractéristiques inspectées, pas l'énergie "
        "consommée ou le temps physique de l'observatoire. Ce n'est pas un "
        "algorithme original d'extraction de pulsars ou une découverte astronomique.\n"
    )
    (outdir/"CONCLUSIONS_HONNETES.md").write_text(summary,encoding="utf-8")
    print(summary)
    print("FULL_RESULTS_JSON="+str(outdir/"htru2_results.json"))
    print("PRE_REGISTERED_PROTOCOL=PASS; TRAIN_WORLD_GUARANTEE=PASS")
    if a_test["action_errors"]:
        print("UNSEEN_WORLD_CERTAINTY=REFUTED_BY_HOLDOUT")
    else:
        print("UNSEEN_WORLD_CERTAINTY=NOT_PROVED_(zero_sample_errors_is_not_a_proof)")

if __name__=="__main__":
    main()
