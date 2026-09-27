#!/usr/bin/env python3
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from insacermo_actionability_engine_v1 import FiniteContract, audit_observation

HERE = Path(__file__).resolve().parent
CASES = json.loads((HERE / "cases.json").read_text(encoding="utf-8"))


def one_state_status(actions, available, admissible_actions):
    world = "sample"
    contract = FiniteContract(
        worlds=(world,),
        actions=tuple(actions),
        available=frozenset(available),
        admissible_pairs=frozenset(
            (world, a) for a in admissible_actions
        ),
    )
    audit = audit_observation(contract, {world: "one-fiber"})
    # certificate consistency: ACT iff at least one common action exists
    common = audit.fibers[0].common_actions
    consistent = (audit.status == "ACT") == bool(common)
    return audit.status, list(common), consistent


def direct_replay():
    rows = []
    for sample_id in CASES["xct_scanned"]:
        status, witness, ok = one_state_status(
            actions=("XCT",),
            available=("XCT",),
            admissible_actions=("XCT",),
        )
        rows.append({
            "sample_id": sample_id,
            "public_class": "xct_scanned",
            "expected": "ACT",
            "status": status,
            "witness": witness,
            "certificate_consistent": ok,
        })

    for sample_id in CASES["no_xct"]:
        status, witness, ok = one_state_status(
            actions=("XCT",),
            available=("XCT",),
            admissible_actions=(),
        )
        rows.append({
            "sample_id": sample_id,
            "public_class": "not_to_be_xct_scanned",
            "expected": "REFUSE",
            "status": status,
            "witness": witness,
            "certificate_consistent": ok,
        })
    return rows


def probe_witness():
    completion_rows = []
    for sensitive in CASES["probe_case"]["completions"]:
        status, witness, ok = one_state_status(
            actions=("XCT",),
            available=("XCT",),
            admissible_actions=() if sensitive else ("XCT",),
        )
        completion_rows.append({
            "xct_sensitive": sensitive,
            "status": status,
            "witness": witness,
            "certificate_consistent": ok,
        })

    statuses = {r["status"] for r in completion_rows}
    if statuses == {"ACT"}:
        verdict = "ACT"
    elif statuses == {"REFUSE"}:
        verdict = "REFUSE"
    else:
        verdict = "PROBE"

    return {
        "case_id": CASES["probe_case"]["id"],
        "missing_fact": CASES["probe_case"]["missing_fact"],
        "completions": completion_rows,
        "status": verdict,
        "certificate_consistent": all(r["certificate_consistent"] for r in completion_rows),
    }


def repair_witness():
    base_action = CASES["repair_case"]["base_action"]
    repair_action = CASES["repair_case"]["repair_action"]

    base_status, base_witness, ok1 = one_state_status(
        actions=(base_action, repair_action),
        available=(base_action,),
        admissible_actions=(repair_action,),
    )
    expanded_status, expanded_witness, ok2 = one_state_status(
        actions=(base_action, repair_action),
        available=(base_action, repair_action),
        admissible_actions=(repair_action,),
    )
    verdict = (
        "REPAIR"
        if base_status == "REFUSE" and expanded_status == "ACT"
        else expanded_status
    )
    return {
        "case_id": CASES["repair_case"]["id"],
        "base_status": base_status,
        "base_witness": base_witness,
        "expanded_status": expanded_status,
        "expanded_witness": expanded_witness,
        "repair_action": repair_action,
        "returned_sample": CASES["repair_case"]["returned_sample"],
        "status": verdict,
        "certificate_consistent": ok1 and ok2,
    }


def main():
    direct = direct_replay()
    probe = probe_witness()
    repair = repair_witness()

    direct_agree = sum(r["status"] == r["expected"] for r in direct)
    internal_ok = (
        all(r["certificate_consistent"] for r in direct)
        and probe["certificate_consistent"]
        and repair["certificate_consistent"]
    )

    statuses = [r["status"] for r in direct] + [probe["status"], repair["status"]]
    histogram = dict(sorted(Counter(statuses).items()))

    result = {
        "protocol": "INSACERMO × Bennu Curation V1",
        "evidence_class": "real-domain external-policy replay / engine stress test",
        "direct_replay": {
            "n": len(direct),
            "agreement": direct_agree,
            "agreement_rate": direct_agree / len(direct),
            "rows": direct,
        },
        "probe": probe,
        "repair": repair,
        "status_histogram": histogram,
        "zero_internal_certificate_inconsistencies": internal_ok,
        "pass": (
            direct_agree == len(direct)
            and probe["status"] == "PROBE"
            and repair["status"] == "REPAIR"
            and internal_ok
        ),
    }

    (HERE / "results.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    lines = [
        "# INSACERMO × Bennu Curation V1 — Results",
        "",
        f"- Evidence class: {result['evidence_class']}",
        f"- Direct XCT replay: **{direct_agree}/{len(direct)} agreement**",
        f"- PROBE witness: **{probe['status']}**",
        f"- REPAIR witness: **{repair['status']}**",
        f"- Internal certificate inconsistencies: **{0 if internal_ok else 1}**",
        f"- Overall frozen-endpoint result: **{'PASS' if result['pass'] else 'FAIL'}**",
        "",
        "## Status histogram",
        "",
    ]
    for k, v in histogram.items():
        lines.append(f"- {k}: {v}")
    lines += [
        "",
        "## Interpretation boundary",
        "",
        "This is not a prediction of NASA allocation decisions and not a validation of NASA policy. "
        "It is a frozen-domain conformance/stress test of the existing INSACERMO finite engine in a "
        "real curation setting where information acquisition, irreversible material handling, missing "
        "contract-relevant information, and capability substitution coexist.",
        "",
    ]
    (HERE / "RESULTS.md").write_text("\n".join(lines), encoding="utf-8")

    print(json.dumps({
        "direct_agreement": f"{direct_agree}/{len(direct)}",
        "probe": probe["status"],
        "repair": repair["status"],
        "histogram": histogram,
        "certificate_inconsistencies": 0 if internal_ok else 1,
        "pass": result["pass"],
    }, sort_keys=True))

    if not result["pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
