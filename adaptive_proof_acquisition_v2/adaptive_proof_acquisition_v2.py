from __future__ import annotations
from dataclasses import dataclass
from typing import Mapping, Iterable, Any
import math

VERSION = "INSACERMO_ADAPTIVE_PROOF_ACQUISITION_V2"

class AdaptiveProofError(ValueError):
    pass

@dataclass(frozen=True)
class FiniteWorld:
    world_id: str
    true_debt: int
    def __post_init__(self):
        if not self.world_id or self.true_debt < 0:
            raise AdaptiveProofError("INVALID_WORLD")

@dataclass(frozen=True)
class CertifiedAdaptiveProbe:
    probe_id: str
    cost: float
    outcome_by_world: Mapping[str, str]
    certified_bound_by_outcome: Mapping[str, int]
    authority_id: str
    def __post_init__(self):
        if not self.probe_id or not self.authority_id or self.cost < 0:
            raise AdaptiveProofError("INVALID_PROBE")
        if any(v < 0 for v in self.certified_bound_by_outcome.values()):
            raise AdaptiveProofError("INVALID_CERTIFIED_BOUND")

@dataclass(frozen=True)
class PlanNode:
    kind: str
    current_upper_bound: int
    worst_case_additional_cost: float
    probe_id: str | None = None
    branches: Mapping[str, "PlanNode"] | None = None

def _ctx_key(worlds, outcome):
    ids=",".join(sorted(w.world_id for w in worlds))
    return ids+"::"+outcome

def _bound_for_context(worlds, probe, outcome):
    if probe.certified_bound_by_context_outcome is not None:
        key=_ctx_key(worlds,outcome)
        if key in probe.certified_bound_by_context_outcome:
            return probe.certified_bound_by_context_outcome[key]
    return probe.certified_bound_by_outcome.get(outcome)

def validate_probe_soundness(worlds: Iterable[FiniteWorld], probe: CertifiedAdaptiveProbe) -> None:
    ws=list(worlds)
    ids={w.world_id for w in ws}
    if set(probe.outcome_by_world) != ids:
        raise AdaptiveProofError("OUTCOME_MAP_MUST_COVER_EXACT_WORLDS")
    groups={}
    for w in ws:
        out=probe.outcome_by_world[w.world_id]
        groups.setdefault(out,[]).append(w)
    for out,g in groups.items():
        bound=_bound_for_context(ws,probe,out)
        if bound is None:
            continue
        true_max=max(w.true_debt for w in g)
        if true_max > bound:
            raise AdaptiveProofError("UNSOUND_OUTCOME_CERTIFICATE")

def _possible_outcomes(worlds, probe):
    return sorted({probe.outcome_by_world[w.world_id] for w in worlds})

def _subworlds(worlds, probe, outcome):
    return tuple(w for w in worlds if probe.outcome_by_world[w.world_id] == outcome)

def plan_guaranteed_act(*, reserve:int, baseline_upper_bound:int,
                        worlds:Iterable[FiniteWorld],
                        probes:Iterable[CertifiedAdaptiveProbe]) -> PlanNode:
    if reserve <= 0 or baseline_upper_bound < 0:
        raise AdaptiveProofError("INVALID_GATE")
    worlds=tuple(worlds)
    probes=tuple(probes)
    if not worlds:
        raise AdaptiveProofError("EMPTY_WORLD_SET")
    if any(w.true_debt > baseline_upper_bound for w in worlds):
        raise AdaptiveProofError("UNSOUND_BASELINE_BOUND")
    for p in probes:
        validate_probe_soundness(worlds,p)

    memo={}
    def solve(world_ids:frozenset[str], current_bound:int, available:tuple[str,...]):
        key=(world_ids,current_bound,available)
        if key in memo:
            return memo[key]
        current_worlds=tuple(w for w in worlds if w.world_id in world_ids)
        if current_bound < reserve:
            node=PlanNode("ACT",current_bound,0.0)
            memo[key]=node
            return node

        best=None
        byid={p.probe_id:p for p in probes}
        for pid in available:
            p=byid[pid]
            outcomes=_possible_outcomes(current_worlds,p)
            branches={}
            worst=0.0
            feasible=True
            remaining=tuple(x for x in available if x!=pid)
            for out in outcomes:
                sw=_subworlds(current_worlds,p,out)
                cert=_bound_for_context(current_worlds,p,out)
                if cert is None:
                    feasible=False
                    break
                true_max=max(w.true_debt for w in sw)
                if true_max > cert:
                    raise AdaptiveProofError("UNSOUND_CONTEXT_CERTIFICATE")
                post=min(current_bound,cert)
                child=solve(frozenset(w.world_id for w in sw),post,remaining)
                if child is None:
                    feasible=False
                    break
                branches[out]=child
                worst=max(worst,child.worst_case_additional_cost)
            if not feasible:
                continue
            total=float(p.cost)+worst
            node=PlanNode("PROBE",current_bound,total,p.probe_id,branches)
            signature=(total,p.cost,p.probe_id)
            if best is None or signature < best[0]:
                best=(signature,node)
        result=None if best is None else best[1]
        memo[key]=result
        return result

    ids=frozenset(w.world_id for w in worlds)
    return solve(ids,baseline_upper_bound,tuple(sorted(p.probe_id for p in probes))) or PlanNode(
        "REFUSE",baseline_upper_bound,math.inf)

def execute_plan(plan:PlanNode, outcomes_by_probe:Mapping[str,str]) -> str:
    node=plan
    while node.kind=="PROBE":
        if node.probe_id not in outcomes_by_probe:
            return "REFUSE"
        outcome=outcomes_by_probe[node.probe_id]
        if node.branches is None or outcome not in node.branches:
            return "REFUSE"
        node=node.branches[outcome]
    return node.kind

def assert_plan_safe(plan:PlanNode, reserve:int, worlds:Iterable[FiniteWorld],
                     probes:Iterable[CertifiedAdaptiveProbe]) -> None:
    worlds=tuple(worlds); probes={p.probe_id:p for p in probes}
    for w in worlds:
        outcomes={pid:p.outcome_by_world[w.world_id] for pid,p in probes.items()}
        decision=execute_plan(plan,outcomes)
        if decision=="ACT" and not (w.true_debt < reserve):
            raise AdaptiveProofError("UNSAFE_ACT_BRANCH")
