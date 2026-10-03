from __future__ import annotations

from dataclasses import dataclass, asdict
from typing import Callable, Iterable
import hashlib
import json


VERSION = "INSACERMO_AUTONOMOUS_EXPLORER_V0"


def _hash(obj) -> str:
    blob = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(blob.encode()).hexdigest()


@dataclass
class FrontierState:
    exact_n: int
    exact_k: int
    witness: set[int]


@dataclass
class Event:
    phase: str
    n: int
    status: str
    details: dict

    def payload(self) -> dict:
        d = asdict(self)
        d["event_hash"] = _hash(d)
        return d


def reciprocal_endpoint_edges(c: int) -> list[tuple[int, int, int]]:
    """All ordered a<b<c satisfying 1/a = 1/b + 1/c, via exact integers."""
    out: list[tuple[int, int, int]] = []
    for b in range(1, c):
        num = b * c
        den = b + c
        a, r = divmod(num, den)
        if r == 0 and 1 <= a < b:
            out.append((a, b, c))
    return out


class AutonomousFrontierExplorer:
    """
    Minimal external autonomous loop.

    It is deliberately conservative:
    * PROBE the first unresolved endpoint after the exact frontier;
    * ACT only when the existing exact witness can be extended safely;
    * REFUSE when the available certificate grammar cannot close exactness.

    The core INSACERMO freeze is not modified.
    """

    def __init__(
        self,
        state: FrontierState,
        endpoint_generator: Callable[[int], Iterable[tuple[int, int, int]]],
    ):
        self.state = state
        self.endpoint_generator = endpoint_generator
        self.trace: list[dict] = []

    def _emit(self, phase: str, n: int, status: str, details: dict) -> dict:
        event = Event(phase=phase, n=n, status=status, details=details).payload()
        self.trace.append(event)
        return event

    def probe_next(self) -> tuple[int, list[tuple[int, int, int]], list[tuple[int, int, int]]]:
        n = self.state.exact_n + 1
        edges = sorted(self.endpoint_generator(n))
        active = [e for e in edges if e[0] in self.state.witness and e[1] in self.state.witness]

        pair_sets = [set(e[:2]) for e in edges]
        common = sorted(set.intersection(*pair_sets)) if pair_sets else []
        common_missing = [x for x in common if x not in self.state.witness]

        self._emit(
            "PROBE",
            n,
            "OBSERVED",
            {
                "endpoint_edges": [list(e) for e in edges],
                "active_obstructions": [list(e) for e in active],
                "common_pair_vertices": common,
                "common_missing_blockers": common_missing,
                "witness_size_before": len(self.state.witness),
            },
        )
        return n, edges, active

    def step(self) -> dict:
        n, edges, active = self.probe_next()

        if not active:
            previous_n = self.state.exact_n
            previous_k = self.state.exact_k
            self.state.witness.add(n)
            self.state.exact_n = n
            self.state.exact_k = previous_k + 1

            # Exactness certificate:
            # lower bound = safely extended witness;
            # upper bound = f(n) <= f(n-1)+1.
            return self._emit(
                "ACT",
                n,
                "EXACT_FRONTIER_EXTENDED",
                {
                    "from_exact_n": previous_n,
                    "from_exact_k": previous_k,
                    "to_exact_n": n,
                    "to_exact_k": self.state.exact_k,
                    "lower_bound_witness_size": len(self.state.witness),
                    "upper_bound_rule": "f(n) <= f(n-1) + 1",
                    "endpoint_edge_count": len(edges),
                    "certificate_kind": "SAFE_ENDPOINT_EXTENSION",
                },
            )

        # We do not silently repair or claim a maximum. The next structural
        # question is identified, but the current grammar refuses exactness.
        return self._emit(
            "REFUSE",
            n,
            "EXACTNESS_NOT_CERTIFIED",
            {
                "active_obstructions": [list(e) for e in active],
                "reason": "ADDING_ENDPOINT_BREAKS_CURRENT_EXACT_WITNESS",
                "next_question": "FIND_CERTIFIED_REPAIR_OR_STRONGER_UPPER_BOUND",
                "exact_frontier_preserved_at": self.state.exact_n,
                "exact_value_preserved_at": self.state.exact_k,
            },
        )

    def run_until_refuse(self, max_steps: int = 8) -> dict:
        for _ in range(max_steps):
            event = self.step()
            if event["phase"] == "REFUSE":
                break

        result = {
            "version": VERSION,
            "final_exact_n": self.state.exact_n,
            "final_exact_k": self.state.exact_k,
            "trace": self.trace,
        }
        result["run_hash"] = _hash(result)
        return result


def verify_trace(result: dict) -> dict:
    failures: list[str] = []
    body = {k: v for k, v in result.items() if k != "run_hash"}
    if result.get("run_hash") != _hash(body):
        failures.append("RUN_HASH_MISMATCH")

    for i, event in enumerate(result.get("trace", [])):
        eb = {k: v for k, v in event.items() if k != "event_hash"}
        if event.get("event_hash") != _hash(eb):
            failures.append(f"EVENT_HASH_MISMATCH:{i}")

    return {"valid": not failures, "failures": failures}
