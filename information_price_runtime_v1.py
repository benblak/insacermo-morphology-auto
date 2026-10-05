from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Iterable, Sequence

World = Any
Probe = Any
Action = Any

@dataclass(frozen=True)
class ProofCertificate:
    world_index: int
    action: Action
    probes: tuple[Probe, ...]
    outcomes: tuple[Any, ...]
    price: int

@dataclass(frozen=True)
class VerificationResult:
    valid: bool
    reason: str
    remaining_conflicts: int

def _signature(world: World, probes: Sequence[Probe], observe: Callable[[Probe, World], Any]) -> tuple[Any, ...]:
    return tuple(observe(p, world) for p in probes)

def verify_certificate(
    worlds: Sequence[World],
    world_index: int,
    probes: Sequence[Probe],
    observe: Callable[[Probe, World], Any],
    action_of: Callable[[World], Action],
    claimed_action: Action | None = None,
    claimed_outcomes: Sequence[Any] | None = None,
    claimed_price: int | None = None,
) -> VerificationResult:
    if not (0 <= world_index < len(worlds)):
        return VerificationResult(False, "WORLD_INDEX_OUT_OF_RANGE", 0)
    x = worlds[world_index]
    action_x = action_of(x)
    if claimed_action is not None and claimed_action != action_x:
        return VerificationResult(False, "ACTION_MISMATCH", 0)

    sig_x = _signature(x, probes, observe)
    if claimed_outcomes is not None and tuple(claimed_outcomes) != sig_x:
        return VerificationResult(False, "OUTCOME_MISMATCH", 0)
    if claimed_price is not None and claimed_price != len(probes):
        return VerificationResult(False, "PRICE_MISMATCH", 0)

    conflicts = 0
    for y in worlds:
        if action_of(y) == action_x:
            continue
        if _signature(y, probes, observe) == sig_x:
            conflicts += 1
    if conflicts:
        return VerificationResult(False, "UNRESOLVED_ACTION_CONFLICT", conflicts)
    return VerificationResult(True, "CERTIFIED", 0)

def make_certificate(
    worlds: Sequence[World],
    world_index: int,
    probes: Sequence[Probe],
    observe: Callable[[Probe, World], Any],
    action_of: Callable[[World], Action],
) -> ProofCertificate:
    x = worlds[world_index]
    outcomes = _signature(x, probes, observe)
    cert = ProofCertificate(world_index, action_of(x), tuple(probes), outcomes, len(probes))
    vr = verify_certificate(
        worlds, world_index, cert.probes, observe, action_of,
        claimed_action=cert.action,
        claimed_outcomes=cert.outcomes,
        claimed_price=cert.price,
    )
    if not vr.valid:
        raise ValueError(vr.reason)
    return cert

def irredundant_certificate(
    worlds: Sequence[World],
    world_index: int,
    library: Sequence[Probe],
    observe: Callable[[Probe, World], Any],
    action_of: Callable[[World], Action],
) -> ProofCertificate | None:
    probes = list(library)
    full = verify_certificate(worlds, world_index, probes, observe, action_of)
    if not full.valid:
        return None
    changed = True
    while changed:
        changed = False
        for p in list(reversed(probes)):
            trial = list(probes)
            trial.remove(p)
            if verify_certificate(worlds, world_index, trial, observe, action_of).valid:
                probes = trial
                changed = True
    return make_certificate(worlds, world_index, probes, observe, action_of)

def classify_with_certificate(
    worlds: Sequence[World],
    world_index: int,
    library: Sequence[Probe],
    observe: Callable[[Probe, World], Any],
    action_of: Callable[[World], Action],
) -> dict[str, Any]:
    cert = irredundant_certificate(worlds, world_index, library, observe, action_of)
    if cert is None:
        return {
            "verdict": "REFUSE",
            "reason": "NO_CERTIFICATE_IN_DECLARED_PROBE_LIBRARY",
            "world_index": world_index,
        }
    return {
        "verdict": "ACT",
        "world_index": world_index,
        "action": cert.action,
        "proof_price": cert.price,
        "probes": list(cert.probes),
        "outcomes": list(cert.outcomes),
        "certificate": cert,
    }
