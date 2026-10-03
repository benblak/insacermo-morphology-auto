from __future__ import annotations

from dataclasses import dataclass, asdict
import hashlib
import json
import time

VERSION = "INSACERMO_AUTONOMOUS_EXPLORER_MAX_FEASIBILITY_V1"


def h(obj):
    return hashlib.sha256(
        json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    ).hexdigest()


def triples_upto(n: int):
    out = []
    for b in range(1, n + 1):
        for c in range(b + 1, n + 1):
            q, r = divmod(b * c, b + c)
            if r == 0 and 1 <= q < b:
                out.append((q, b, c))
    return out


def valid_witness(W: set[int], edges) -> bool:
    return all(not all(x in W for x in e) for e in edges)


def feasibility_target(edges, n: int, target_k: int, solver_name: str):
    """
    Decide only the information bit needed at the next frontier:
      does there exist an admissible witness of size >= target_k?

    Equivalently choose a hitting set R of removed vertices with
      |R| <= n - target_k
    hitting every forbidden triple.
    """
    from pysat.card import CardEnc, EncType
    from pysat.solvers import Solver

    max_removed = n - target_k
    if max_removed < 0:
        return {"sat": False, "model_witness": None, "seconds": 0.0}

    clauses = [list(e) for e in edges]  # r_a OR r_b OR r_c
    card = CardEnc.atmost(
        lits=list(range(1, n + 1)),
        bound=max_removed,
        top_id=n,
        encoding=EncType.seqcounter,
    )

    t0 = time.perf_counter()
    with Solver(name=solver_name, bootstrap_with=clauses + card.clauses) as solver:
        sat = solver.solve()
        model = solver.get_model() if sat else None
    dt = time.perf_counter() - t0

    if not sat:
        return {"sat": False, "model_witness": None, "seconds": dt}

    positives = {x for x in model if 1 <= x <= n}
    removed = positives
    witness = {x for x in range(1, n + 1) if x not in removed}

    return {
        "sat": True,
        "model_witness": sorted(witness),
        "removed_size": len(removed),
        "witness_size": len(witness),
        "seconds": dt,
    }


@dataclass
class Step:
    phase: str
    n: int
    operator: str
    status: str
    details: dict

    def payload(self):
        d = asdict(self)
        d["event_hash"] = h(d)
        return d


class FreeExplorer:
    """
    Autonomous exact frontier explorer.

    Given an exact frontier f(n)=k and one size-k witness, the next value obeys
      k <= f(n+1) <= k+1.

    Therefore the explorer never optimizes the whole problem. It asks only:
      "Does a witness of size k+1 exist?"

    Strategy:
      1. choose the next unresolved endpoint itself;
      2. PROBE exact endpoint constraints;
      3. SAFE_ADD if the inherited witness extends directly;
      4. otherwise escalate to a single cardinality-feasibility query;
      5. cross-check SAT/UNSAT with two independent SAT backends;
      6. replay any SAT witness against every forbidden triple;
      7. conclude GROWTH (SAT) or PLATEAU (UNSAT);
      8. REFUSE on disagreement or failed replay.

    SAT results are exact computational cross-checks, not Lean proofs.
    """

    def __init__(self, n: int, k: int, witness: set[int],
                 primary_solver: str = "g3", check_solver: str = "m22"):
        self.n = n
        self.k = k
        self.W = set(witness)
        self.primary_solver = primary_solver
        self.check_solver = check_solver
        self.trace = []

    def emit(self, phase, n, operator, status, details):
        e = Step(phase, n, operator, status, details).payload()
        self.trace.append(e)
        return e

    def probe(self, n: int):
        edges = triples_upto(n)
        new_edges = [e for e in edges if e[2] == n]
        active = [e for e in new_edges if all(x in self.W for x in e if x != n)]
        self.emit("PROBE", n, "EXACT_ENDPOINT_ENUMERATION", "OBSERVED", {
            "new_edges": [list(e) for e in new_edges],
            "active_obstructions": [list(e) for e in active],
            "previous_exact": [self.n, self.k],
            "inherited_band": [self.k, self.k + 1],
        })
        return edges, new_edges, active

    def safe_add(self, n: int, edges, active):
        self.emit("PLAN", n, "SAFE_ADD", "TRY", {
            "active_obstruction_count": len(active)
        })
        if active:
            self.emit("PLAN", n, "SAFE_ADD", "NO_CERTIFICATE", {})
            return None

        W2 = set(self.W)
        W2.add(n)
        if len(W2) != self.k + 1 or not valid_witness(W2, edges):
            self.emit("PLAN", n, "SAFE_ADD", "REJECTED_BY_GLOBAL_REPLAY", {})
            return None
        return W2

    def exact_feasibility(self, n: int, edges):
        target = self.k + 1
        self.emit("PLAN", n, "TARGET_FEASIBILITY", "ESCALATE", {
            "question": f"EXISTS_ADMISSIBLE_WITNESS_SIZE_AT_LEAST_{target}",
            "target_k": target,
            "max_removed": n - target,
            "primary_solver": self.primary_solver,
            "check_solver": self.check_solver,
        })

        a = feasibility_target(edges, n, target, self.primary_solver)
        b = feasibility_target(edges, n, target, self.check_solver)

        self.emit("PROBE", n, "SAT_CROSSCHECK", "OBSERVED", {
            "primary_sat": a["sat"],
            "check_sat": b["sat"],
            "primary_seconds": round(a["seconds"], 6),
            "check_seconds": round(b["seconds"], 6),
        })

        if a["sat"] != b["sat"]:
            return self.emit("REFUSE", n, "TARGET_FEASIBILITY",
                             "SOLVER_DISAGREEMENT", {
                                 "primary_sat": a["sat"],
                                 "check_sat": b["sat"],
                                 "frontier_preserved": [self.n, self.k],
                             })

        old_k = self.k

        if not a["sat"]:
            # The old witness remains valid at n when n itself is not selected.
            if not valid_witness(self.W, edges):
                return self.emit("REFUSE", n, "TARGET_FEASIBILITY",
                                 "INHERITED_WITNESS_REPLAY_FAILED", {
                                     "frontier_preserved": [self.n, self.k],
                                 })
            self.n = n
            return self.emit("ACT", n, "TARGET_FEASIBILITY",
                             "EXACT_FRONTIER_PLATEAU", {
                                 "previous_exact_k": old_k,
                                 "new_exact_k": self.k,
                                 "decision_bit": "UNSAT_FOR_K_PLUS_1",
                                 "lower_bound_witness_size": len(self.W),
                                 "upper_bound_source": "UNSAT_TARGET_FEASIBILITY",
                                 "proof_status": "EXACT_COMPUTATIONAL_CROSSCHECK_NOT_LEAN",
                             })

        W1 = set(a["model_witness"])
        W2 = set(b["model_witness"])
        if (len(W1) < target or len(W2) < target or
                not valid_witness(W1, edges) or not valid_witness(W2, edges)):
            return self.emit("REFUSE", n, "TARGET_FEASIBILITY",
                             "SAT_WITNESS_REPLAY_FAILED", {
                                 "frontier_preserved": [self.n, self.k],
                             })

        # The inherited exact upper bound gives f(n) <= old_k+1 = target.
        # SAT gives f(n) >= target, so equality follows.
        self.n = n
        self.k = target
        self.W = W1
        return self.emit("ACT", n, "TARGET_FEASIBILITY",
                         "EXACT_FRONTIER_GROWTH", {
                             "previous_exact_k": old_k,
                             "new_exact_k": self.k,
                             "decision_bit": "SAT_FOR_K_PLUS_1",
                             "primary_witness_size": len(W1),
                             "check_witness_size": len(W2),
                             "primary_removed_size": a["removed_size"],
                             "check_removed_size": b["removed_size"],
                             "global_replay": "PASS_BOTH_WITNESSES",
                             "upper_bound_rule": "f(n) <= f(n-1)+1",
                             "proof_status": "EXACT_COMPUTATIONAL_CROSSCHECK_NOT_LEAN",
                         })

    def step(self):
        n = self.n + 1
        edges, new_edges, active = self.probe(n)

        W2 = self.safe_add(n, edges, active)
        if W2 is not None:
            old_k = self.k
            self.n = n
            self.k += 1
            self.W = W2
            return self.emit("ACT", n, "SAFE_ADD",
                             "EXACT_FRONTIER_GROWTH", {
                                 "previous_exact_k": old_k,
                                 "new_exact_k": self.k,
                                 "witness_size": len(self.W),
                                 "global_replay": "PASS",
                                 "upper_bound_rule": "f(n) <= f(n-1)+1",
                                 "proof_status": "STRUCTURAL_TRANSFER_FROM_EXACT_PREVIOUS_FRONTIER",
                             })

        return self.exact_feasibility(n, edges)

    def run(self, max_frontier_steps=8):
        for _ in range(max_frontier_steps):
            e = self.step()
            if e["phase"] == "REFUSE":
                break
        out = {
            "version": VERSION,
            "final_exact_n": self.n,
            "final_exact_k": self.k,
            "trace": self.trace,
        }
        out["run_hash"] = h(out)
        return out


def verify_run(out):
    body = {k: v for k, v in out.items() if k != "run_hash"}
    if out.get("run_hash") != h(body):
        return False
    for e in out.get("trace", []):
        eb = {k: v for k, v in e.items() if k != "event_hash"}
        if e.get("event_hash") != h(eb):
            return False
    return True
