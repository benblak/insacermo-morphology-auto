from __future__ import annotations
from dataclasses import dataclass, asdict
import hashlib, json

VERSION = "INSACERMO_AUTONOMOUS_EXPLORER_MAX_1"


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


def valid_removed(R: set[int], edges):
    return all(any(x in R for x in e) for e in edges)


def witness_from_removed(n: int, R: set[int]):
    return {x for x in range(1, n + 1) if x not in R}


def exact_hitting_set(edges, solver: str):
    from pysat.examples.hitman import Hitman

    with Hitman(solver=solver) as hitman:
        for e in edges:
            hitman.hit(list(e))
        hs = hitman.get()
    if hs is None:
        raise RuntimeError("HITMAN_RETURNED_NONE")
    return set(hs)


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
    Autonomous certified frontier explorer.

    It is given only:
      * an exact frontier point (n,k),
      * one witness of size k,
      * the exact forbidden-relation generator.

    It is NOT given a target endpoint or a hand-written plan.

    Policy:
      1. select the next unresolved n;
      2. PROBE exact new endpoint constraints;
      3. use a zero-cost structural SAFE_ADD if possible;
      4. if blocked, autonomously escalate to an exact minimum hitting-set
         operator and cross-check it with a second independent SAT backend;
      5. globally replay the returned witness;
      6. resolve either GROWTH (k+1) or PLATEAU (k);
      7. REFUSE on disagreement or anything outside the inherited [k,k+1] band.

    The SAT solver is an external exact combinatorial tool selected by the
    explorer. It is not machine learning and is not represented as Lean proof.
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

    def probe(self, n):
        edges = triples_upto(n)
        new_edges = [e for e in edges if e[2] == n]
        R_prev = {x for x in range(1, n) if x not in self.W}
        active = [e for e in new_edges if not any(x in R_prev for x in e)]
        self.emit("PROBE", n, "EXACT_ENDPOINT_ENUMERATION", "OBSERVED", {
            "new_edges": [list(e) for e in new_edges],
            "active_obstructions": [list(e) for e in active],
            "previous_witness_size": len(self.W),
            "previous_removed_size": len(R_prev),
        })
        return edges, new_edges, R_prev, active

    def safe_add(self, n, edges, R_prev, active):
        self.emit("PLAN", n, "SAFE_ADD", "TRY", {
            "active_obstruction_count": len(active)
        })
        if active:
            self.emit("PLAN", n, "SAFE_ADD", "NO_CERTIFICATE", {})
            return None
        R = set(R_prev)
        if not valid_removed(R, edges):
            self.emit("PLAN", n, "SAFE_ADD", "REJECTED_BY_GLOBAL_REPLAY", {})
            return None
        W = witness_from_removed(n, R)
        if len(W) != self.k + 1:
            self.emit("PLAN", n, "SAFE_ADD", "CARDINALITY_MISMATCH", {})
            return None
        return R, W

    def exact_resolve(self, n, edges):
        self.emit("PLAN", n, "EXACT_HITTING_SET", "ESCALATE", {
            "primary_solver": self.primary_solver,
            "check_solver": self.check_solver,
            "edge_count": len(edges),
            "inherited_exact_band": [self.k, self.k + 1],
        })

        R1 = exact_hitting_set(edges, self.primary_solver)
        R2 = exact_hitting_set(edges, self.check_solver)
        k1 = n - len(R1)
        k2 = n - len(R2)

        if k1 != k2:
            return self.emit("REFUSE", n, "EXACT_HITTING_SET",
                             "SOLVER_DISAGREEMENT", {
                                 "primary_value": k1,
                                 "check_value": k2,
                                 "frontier_preserved": [self.n, self.k],
                             })

        if k1 not in (self.k, self.k + 1):
            return self.emit("REFUSE", n, "EXACT_HITTING_SET",
                             "OUTSIDE_INHERITED_BAND", {
                                 "solver_value": k1,
                                 "expected_band": [self.k, self.k + 1],
                                 "frontier_preserved": [self.n, self.k],
                             })

        if not valid_removed(R1, edges):
            return self.emit("REFUSE", n, "EXACT_HITTING_SET",
                             "PRIMARY_WITNESS_REPLAY_FAILED", {
                                 "frontier_preserved": [self.n, self.k],
                             })

        W1 = witness_from_removed(n, R1)
        if len(W1) != k1:
            return self.emit("REFUSE", n, "EXACT_HITTING_SET",
                             "PRIMARY_CARDINALITY_REPLAY_FAILED", {
                                 "frontier_preserved": [self.n, self.k],
                             })

        old_k = self.k
        self.n = n
        self.k = k1
        self.W = W1

        status = "EXACT_FRONTIER_GROWTH" if k1 == old_k + 1 else "EXACT_FRONTIER_PLATEAU"
        return self.emit("ACT", n, "EXACT_HITTING_SET", status, {
            "previous_exact_k": old_k,
            "new_exact_k": self.k,
            "witness_size": len(self.W),
            "minimum_removed_size": len(R1),
            "primary_solver": self.primary_solver,
            "check_solver": self.check_solver,
            "crosscheck_value": k2,
            "global_replay": "PASS",
            "proof_status": "EXACT_COMPUTATIONAL_CROSSCHECK_NOT_LEAN",
        })

    def step(self):
        n = self.n + 1
        edges, new_edges, R_prev, active = self.probe(n)

        safe = self.safe_add(n, edges, R_prev, active)
        if safe is not None:
            R, W = safe
            old_k = self.k
            self.n = n
            self.k = old_k + 1
            self.W = W
            return self.emit("ACT", n, "SAFE_ADD", "EXACT_FRONTIER_GROWTH", {
                "previous_exact_k": old_k,
                "new_exact_k": self.k,
                "witness_size": len(self.W),
                "global_edge_count": len(edges),
                "global_replay": "PASS",
                "upper_rule": "f(n) <= f(n-1)+1",
                "proof_status": "STRUCTURAL_TRANSFER_FROM_EXACT_PREVIOUS_FRONTIER",
            })

        return self.exact_resolve(n, edges)

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
