from __future__ import annotations

from dataclasses import dataclass, asdict
import hashlib
import json
import time

VERSION = "INSACERMO_AUTONOMOUS_EXPLORER_MAX_MIP_V1"


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


def _milp_keep_form(edges, n: int, target_k: int):
    import numpy as np
    from scipy.optimize import milp, Bounds, LinearConstraint
    from scipy.sparse import lil_matrix, vstack

    m = len(edges)
    A = lil_matrix((m, n), dtype=float)
    for i, e in enumerate(edges):
        for v in e:
            A[i, v - 1] = 1.0
    A = A.tocsr()

    A2 = vstack([A, np.ones((1, n))]).tocsr()
    lb = np.concatenate([np.full(m, -np.inf), [float(target_k)]])
    ub = np.concatenate([np.full(m, 2.0), [np.inf]])

    t0 = time.perf_counter()
    res = milp(
        np.zeros(n),
        integrality=np.ones(n),
        bounds=Bounds(np.zeros(n), np.ones(n)),
        constraints=LinearConstraint(A2, lb, ub),
        options={"time_limit": 120, "mip_rel_gap": 0.0},
    )
    dt = time.perf_counter() - t0

    out = {
        "status": int(res.status),
        "message": str(res.message),
        "seconds": dt,
        "sat": bool(res.status == 0),
    }
    if res.status == 0:
        W = {i + 1 for i, x in enumerate(res.x) if x > 0.5}
        out["witness"] = sorted(W)
        out["witness_size"] = len(W)
    return out


def _milp_removed_form(edges, n: int, target_k: int):
    import numpy as np
    from scipy.optimize import milp, Bounds, LinearConstraint
    from scipy.sparse import lil_matrix, vstack

    max_removed = n - target_k
    m = len(edges)
    A = lil_matrix((m, n), dtype=float)
    for i, e in enumerate(edges):
        for v in e:
            A[i, v - 1] = 1.0
    A = A.tocsr()

    A2 = vstack([A, np.ones((1, n))]).tocsr()
    lb = np.concatenate([np.ones(m), [-np.inf]])
    ub = np.concatenate([np.full(m, np.inf), [float(max_removed)]])

    t0 = time.perf_counter()
    res = milp(
        np.zeros(n),
        integrality=np.ones(n),
        bounds=Bounds(np.zeros(n), np.ones(n)),
        constraints=LinearConstraint(A2, lb, ub),
        options={"time_limit": 120, "mip_rel_gap": 0.0},
    )
    dt = time.perf_counter() - t0

    out = {
        "status": int(res.status),
        "message": str(res.message),
        "seconds": dt,
        "sat": bool(res.status == 0),
    }
    if res.status == 0:
        R = {i + 1 for i, x in enumerate(res.x) if x > 0.5}
        W = {x for x in range(1, n + 1) if x not in R}
        out["witness"] = sorted(W)
        out["witness_size"] = len(W)
        out["removed_size"] = len(R)
    return out


def exact_feasibility_crosscheck(edges, n: int, target_k: int):
    """
    Cross-check the same yes/no frontier question in two equivalent MILP encodings:
      KEEP form: each forbidden triple contains at most two kept vertices.
      REMOVED form: each forbidden triple contains at least one removed vertex.

    Both are solved by HiGHS through scipy.optimize.milp. This is a dual
    formulation cross-check, NOT an independent theorem prover and NOT Lean.
    """
    a = _milp_keep_form(edges, n, target_k)
    b = _milp_removed_form(edges, n, target_k)
    return a, b


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
    Information-minimal autonomous frontier explorer.

    Given exact f(n)=k:
      k <= f(n+1) <= k+1.

    The explorer therefore asks only:
      does a size-(k+1) admissible witness exist?

    It first tries a transparent SAFE_ADD. If blocked, it escalates to an exact
    mixed-integer feasibility query in two equivalent encodings, then globally
    replays any returned witness. A failure/disagreement yields REFUSE.

    Computational MILP optimality/infeasibility is not labelled Lean verification.
    """

    def __init__(self, n: int, k: int, witness: set[int]):
        self.n = n
        self.k = k
        self.W = set(witness)
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
            "edge_count": len(edges),
        })
        return edges, active

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

    def mip_feasibility(self, n: int, edges):
        target = self.k + 1
        self.emit("PLAN", n, "MIP_TARGET_FEASIBILITY", "ESCALATE", {
            "question": f"EXISTS_ADMISSIBLE_WITNESS_SIZE_AT_LEAST_{target}",
            "target_k": target,
            "keep_form": "sum(triple kept) <= 2 and sum(kept) >= target",
            "removed_form": "sum(triple removed) >= 1 and sum(removed) <= n-target",
        })

        a, b = exact_feasibility_crosscheck(edges, n, target)

        self.emit("PROBE", n, "MIP_DUAL_FORMULATION_CROSSCHECK", "OBSERVED", {
            "keep_status": a["status"],
            "removed_status": b["status"],
            "keep_sat": a["sat"],
            "removed_sat": b["sat"],
            "keep_seconds": round(a["seconds"], 6),
            "removed_seconds": round(b["seconds"], 6),
            "keep_message": a["message"],
            "removed_message": b["message"],
        })

        # status 0 = solved feasible; status 2 = proven infeasible by HiGHS.
        accepted_statuses = {0, 2}
        if a["status"] not in accepted_statuses or b["status"] not in accepted_statuses:
            return self.emit("REFUSE", n, "MIP_TARGET_FEASIBILITY",
                             "SOLVER_DID_NOT_FINISH_EXACTLY", {
                                 "keep_status": a["status"],
                                 "removed_status": b["status"],
                                 "frontier_preserved": [self.n, self.k],
                             })

        if a["sat"] != b["sat"]:
            return self.emit("REFUSE", n, "MIP_TARGET_FEASIBILITY",
                             "FORMULATION_DISAGREEMENT", {
                                 "keep_sat": a["sat"],
                                 "removed_sat": b["sat"],
                                 "frontier_preserved": [self.n, self.k],
                             })

        old_k = self.k

        if not a["sat"]:
            if not valid_witness(self.W, edges):
                return self.emit("REFUSE", n, "MIP_TARGET_FEASIBILITY",
                                 "INHERITED_WITNESS_REPLAY_FAILED", {
                                     "frontier_preserved": [self.n, self.k],
                                 })
            self.n = n
            return self.emit("ACT", n, "MIP_TARGET_FEASIBILITY",
                             "EXACT_FRONTIER_PLATEAU", {
                                 "previous_exact_k": old_k,
                                 "new_exact_k": self.k,
                                 "decision_bit": "INFEASIBLE_FOR_K_PLUS_1",
                                 "lower_bound_witness_size": len(self.W),
                                 "upper_bound_source": "MIP_INFEASIBILITY_CROSSCHECK",
                                 "proof_status": "EXACT_COMPUTATIONAL_MIP_CROSSCHECK_NOT_LEAN",
                             })

        W1 = set(a["witness"])
        W2 = set(b["witness"])
        if (len(W1) < target or len(W2) < target or
                not valid_witness(W1, edges) or not valid_witness(W2, edges)):
            return self.emit("REFUSE", n, "MIP_TARGET_FEASIBILITY",
                             "MIP_WITNESS_REPLAY_FAILED", {
                                 "frontier_preserved": [self.n, self.k],
                             })

        self.n = n
        self.k = target
        self.W = W1
        return self.emit("ACT", n, "MIP_TARGET_FEASIBILITY",
                         "EXACT_FRONTIER_GROWTH", {
                             "previous_exact_k": old_k,
                             "new_exact_k": self.k,
                             "decision_bit": "FEASIBLE_FOR_K_PLUS_1",
                             "keep_witness_size": len(W1),
                             "removed_witness_size": len(W2),
                             "global_replay": "PASS_BOTH_FORMULATIONS",
                             "upper_bound_rule": "f(n) <= f(n-1)+1",
                             "proof_status": "EXACT_COMPUTATIONAL_MIP_CROSSCHECK_NOT_LEAN",
                         })

    def step(self):
        n = self.n + 1
        edges, active = self.probe(n)

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

        return self.mip_feasibility(n, edges)

    def run(self, max_frontier_steps=10):
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
