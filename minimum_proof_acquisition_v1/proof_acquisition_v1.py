from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from typing import Iterable, Mapping

VERSION = "INSACERMO_MINIMUM_PROOF_ACQUISITION_V1"

class ProofAcquisitionError(ValueError):
    pass

def proof_deficit(reserve: int, upper_bound: int) -> int:
    """Exact integer tightening needed to make upper_bound < reserve."""
    if not isinstance(reserve, int) or not isinstance(upper_bound, int):
        raise ProofAcquisitionError("INTEGER_BOUNDS_REQUIRED")
    if reserve <= 0 or upper_bound < 0:
        raise ProofAcquisitionError("INVALID_BOUND_OR_RESERVE")
    return 0 if upper_bound < reserve else upper_bound - reserve + 1

@dataclass(frozen=True)
class AbsoluteBoundOffer:
    source_id: str
    cost: float
    guaranteed_upper_bound: int
    authority_id: str

    def __post_init__(self):
        if not self.source_id or not self.authority_id:
            raise ProofAcquisitionError("EMPTY_SOURCE_OR_AUTHORITY")
        if self.cost < 0:
            raise ProofAcquisitionError("NEGATIVE_COST")
        if self.guaranteed_upper_bound < 0:
            raise ProofAcquisitionError("NEGATIVE_BOUND")

@dataclass(frozen=True)
class ComponentBoundOffer:
    source_id: str
    component: str
    cost: float
    guaranteed_component_upper_bound: int
    authority_id: str

    def __post_init__(self):
        if not self.source_id or not self.component or not self.authority_id:
            raise ProofAcquisitionError("EMPTY_FIELD")
        if self.cost < 0:
            raise ProofAcquisitionError("NEGATIVE_COST")
        if self.guaranteed_component_upper_bound < 0:
            raise ProofAcquisitionError("NEGATIVE_BOUND")

@dataclass(frozen=True)
class AcquisitionPlan:
    mode: str
    reserve: int
    baseline_upper_bound: int
    proof_deficit: int
    selected_sources: tuple[str, ...]
    total_cost: float
    guaranteed_post_upper_bound: int
    restores_act: bool
    planner_version: str = VERSION

def plan_same_debt_absolute(*, reserve: int, baseline_upper_bound: int,
                            offers: Iterable[AbsoluteBoundOffer]) -> AcquisitionPlan:
    delta = proof_deficit(reserve, baseline_upper_bound)
    if delta == 0:
        return AcquisitionPlan("SAME_DEBT_MIN", reserve, baseline_upper_bound, delta, (), 0.0,
                               baseline_upper_bound, True)
    feasible = [o for o in offers if o.guaranteed_upper_bound < reserve]
    if not feasible:
        return AcquisitionPlan("SAME_DEBT_MIN", reserve, baseline_upper_bound, delta, (), 0.0,
                               baseline_upper_bound, False)
    best = min(feasible, key=lambda o: (o.cost, o.guaranteed_upper_bound, o.source_id))
    return AcquisitionPlan("SAME_DEBT_MIN", reserve, baseline_upper_bound, delta,
                           (best.source_id,), float(best.cost), best.guaranteed_upper_bound, True)

def plan_additive_components(*, reserve: int, baseline_components: Mapping[str, int],
                             offers: Iterable[ComponentBoundOffer]) -> AcquisitionPlan:
    if reserve <= 0:
        raise ProofAcquisitionError("INVALID_RESERVE")
    baseline = dict(baseline_components)
    if not baseline or any((not k) or (not isinstance(v, int)) or v < 0 for k, v in baseline.items()):
        raise ProofAcquisitionError("INVALID_BASELINE_COMPONENTS")
    baseline_total = sum(baseline.values())
    delta = proof_deficit(reserve, baseline_total)
    if delta == 0:
        return AcquisitionPlan("ADDITIVE_COMPONENTS", reserve, baseline_total, delta, (), 0.0,
                               baseline_total, True)

    offers = list(offers)
    for o in offers:
        if o.component not in baseline:
            raise ProofAcquisitionError("UNKNOWN_COMPONENT")
        if o.guaranteed_component_upper_bound > baseline[o.component]:
            raise ProofAcquisitionError("OFFER_DOES_NOT_TIGHTEN")

    best = None
    n = len(offers)
    for k in range(1, n + 1):
        for idxs in combinations(range(n), k):
            chosen = [offers[i] for i in idxs]
            comps = [o.component for o in chosen]
            if len(set(comps)) != len(comps):
                continue
            post = dict(baseline)
            for o in chosen:
                post[o.component] = o.guaranteed_component_upper_bound
            post_total = sum(post.values())
            if post_total >= reserve:
                continue
            cost = float(sum(o.cost for o in chosen))
            ids = tuple(sorted(o.source_id for o in chosen))
            candidate = (cost, post_total, len(ids), ids, chosen)
            if best is None or candidate[:4] < best[:4]:
                best = candidate

    if best is None:
        return AcquisitionPlan("ADDITIVE_COMPONENTS", reserve, baseline_total, delta, (), 0.0,
                               baseline_total, False)
    cost, post_total, _, ids, _ = best
    return AcquisitionPlan("ADDITIVE_COMPONENTS", reserve, baseline_total, delta, ids, cost,
                           post_total, True)
