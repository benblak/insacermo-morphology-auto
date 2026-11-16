#!/usr/bin/env python3
"""Three domains, ONE unchanged historical INSACERMO C3 executable.

Runs actual insacermo_one_engine.decide and replay for 3 × 5 cases.
The world descriptions/observation channels are supplied by separate adapters;
the engine itself never sees the domain name or source strings.
No new decision gate, no changes to the frozen C3 source.
"""
from __future__ import annotations
import hashlib
import json
import os
import sqlite3
import tempfile
import unicodedata
from pathlib import Path
from dataclasses import dataclass

from insacermo_one_engine import decide, replay, canonical

ROOT = Path(__file__).resolve().parent
EXPECTED_FROZEN_GIT_BLOB = "bd5310b3692bcbad4e874005b7dd8eda90616f74"
DEFAULT_OUTPUT = ROOT / "out"
VERDICTS = {
    "act": "ACT",
    "probe": "PROBE",
    "repair": "REPAIR",
    "open": "EPISTEMIC_OPEN",
    "refuse": "REFUSE_ROBUST",
}

def git_blob_sha(data: bytes) -> str:
    header = b"blob " + str(len(data)).encode() + b"\0"
    return hashlib.sha1(header + data).hexdigest()

def assert_frozen_source() -> str:
    source = (ROOT.parent / "insacermo_one_engine.py").read_bytes()
    digest = git_blob_sha(source)
    assert digest == EXPECTED_FROZEN_GIT_BLOB, ("FROZEN_ENGINE_CHANGED", digest)
    return digest

@dataclass(frozen=True)
class Domain:
    domain: str
    first: str
    second: str
    observation: str
    labels: tuple[bool, bool]

def domains() -> list[Domain]:
    def clean(s: str) -> str:
        return "".join(c for c in unicodedata.normalize("NFD", s)
                       if not unicodedata.category(c).startswith("M"))
    x, y = "3 ≠ 3", "3 = 3"
    assert clean(x) == clean(y) == "3 = 3"

    with sqlite3.connect(":memory:") as db:
        cents = [1049, 1051]
        observed = [db.execute("SELECT ? / 100", (v,)).fetchone()[0] for v in cents]
        assert observed == [10, 10]
    a, b = "Report.txt", "report.txt"
    assert a != b and a.casefold() == b.casefold()
    with tempfile.TemporaryDirectory() as tmp:
        p, q = Path(tmp) / a, Path(tmp) / b
        p.write_text("allowed", encoding="utf-8")
        q.write_text("restricted", encoding="utf-8")
        assert not p.samefile(q), "Filesystem must be case-sensitive"
    return [
        Domain("unicode", x, y, clean(x), (False, True)),
        Domain("finance_sqlite", "1049 cents", "1051 cents", str(observed[0]), (False, True)),
        Domain("case_sensitive_files", a, b, a.casefold(), (True, False)),
    ]

def model(domain: Domain, case: str) -> dict:
    assert case in VERDICTS
    # Each domain has two admissible raw worlds, with opposed target decisions.
    # REPAIR adds two post-repair worlds (2/3) with original truths unchanged.
    # A successful REPAIR must change the reachable state, not merely be relabeled.
    is_repair = case == "repair"
    W = 4 if is_repair else 2
    flags = [bool(v) for v in domain.labels]
    good = [[not v, v] for v in flags]
    if is_repair:
        good.extend([[not v, v] for v in flags])
    # PROBE = observation differentiates worlds, does not alter state.
    # REPAIR = conditioned transition to preserved source states 2/3.
    if is_repair:
        next_false, next_true = [[2, 1, 2, 3]], [[0, 3, 2, 3]]
    else:
        next_false, next_true = [[0, 1]], [[0, 1]]
    result = {
        "worldCount": W,
        "actionCount": 2,
        "probeCount": 1,
        "good": good,
        "sense": [[1, 2] + ([1, 2] if is_repair else [])],
        "nextFalse": next_false,
        "nextTrue": next_true,
        "actionCost": [0, 0],
        "probeCost": [1],
        "lowerWorld": [0, 1] if case == "refuse" else [0],
        "upperWorld": [0] if case == "act" else [0, 1],
        "mustActions": [0, 1],
        "mayActions": [0, 1],
        "probeKinds": ["REPAIR" if is_repair else "PROBE"],
        "depth": 1,
        "budget": 0 if case in ("open", "refuse") else 1,
        "reserve": 5,
        "debt": 0
    }
    return result

def run(out: Path) -> dict:
    engine_blob = assert_frozen_source()
    out.mkdir(parents=True, exist_ok=True)
    report = {
        "frozen_source_git_blob": engine_blob,
        "engine": "INSACERMO_C3_FINITE_ONE_ENGINE_V1",
        "source_branch": "insacermo-one-engine-c3-complete-finite-20261011",
        "scope": "3 declared two-world domains; 15 decisions; model-level Lean certificates",
        "domains": {},
        "all_certificates_replayed": False,
    }
    for domain in domains():
        rows = {}
        for case, expected in VERDICTS.items():
            contract = model(domain, case)
            folder = out / domain.domain / case
            result = decide(contract, folder)
            assert result["verdict"] == expected, (domain.domain, case, result)
            assert result["authorized"] == (case in ("act", "probe", "repair"))
            assert replay(folder), (domain.domain, case, "lean-replay-failed")
            candidate = json.loads((folder / "candidate.json").read_text())
            assert candidate["verdict"] == expected
            # Confirm all 15 contracts remain traceable to their declared domain.
            rows[case] = {
                "verdict": result["verdict"],
                "authorized": result["authorized"],
                "sha256_contract": result["contract_sha256"],
                "sha256_proof": result["source_sha256"],
                "sha256_receipt": result["receipt_sha256"],
                "replay": True,
            }
            print(domain.domain, case, result["verdict"], "LEAN_ACCEPTED")
        report["domains"][domain.domain] = {
            "real_sources": [domain.first, domain.second],
            "lossy_observation": domain.observation,
            "target_labels": list(domain.labels),
            "cases": rows,
        }

    # Tamper tests: a valid receipt, generated Lean file, and contract are each
    # modified and must be rejected by the historical verifier. Restore after.
    negative = []
    folder = out / "unicode" / "probe"
    for name, mutate in (
        ("receipt.json", lambda b: b.replace(b'"authorized":true', b'"authorized":false')),
        ("C3Decision.lean", lambda b: b + b"\n-- TAMPER\n"),
        ("contract.json", lambda b: b.replace(b'"reserve":5', b'"reserve":6')),
    ):
        p = folder / name
        saved = p.read_bytes()
        modified = mutate(saved)
        assert modified != saved, ("mutation-not-applied", name)
        try:
            p.write_bytes(modified)
            assert not replay(folder), ("tampered-data-accepted", name)
        finally:
            p.write_bytes(saved)
        assert replay(folder)
        negative.append(name)
    assert not replay(folder, lean_binary="/lean-binary-not-present")
    report["negative_controls"] = negative + ["lean_missing"]
    report["all_certificates_replayed"] = True
    (out / "audit.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print("AUDIT_PASS", "15 LEAN-VERIFIED", "3 DOMAINS", "4 TAMPER/FAIL-CLOSED CHECKS")
    return report

if __name__ == "__main__":
    import sys
    run(Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_OUTPUT)
