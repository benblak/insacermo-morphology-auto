#!/usr/bin/env python3
"""
INSACERMO Actionability Engine V1
Finite deterministic exact kernel.

This module implements the operational objects used by the formal kernel:
- common-action fiber safety
- ACT / REFUSE for a fixed observation
- exact minimum action covers
- exact minimum safe partitions
- certified message protocols
- exact finite context-message Pareto frontiers

It is intentionally small, deterministic, and exhaustive. It is not a
replacement for the Lean proofs; it is an executable realization of the same
finite semantics for experiments and the public engine.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product
from typing import Dict, Hashable, Iterable, List, Mapping, Optional, Sequence, Tuple


World = Hashable
Action = Hashable
Symbol = Hashable
Context = Hashable
LocalWorld = Hashable


@dataclass(frozen=True)
class FiniteContract:
    worlds: Tuple[World, ...]
    actions: Tuple[Action, ...]
    available: frozenset[Action]
    admissible_pairs: frozenset[Tuple[World, Action]]

    def admissible(self, world: World, action: Action) -> bool:
        return (world, action) in self.admissible_pairs

    def action_region(self, action: Action) -> frozenset[World]:
        if action not in self.available:
            return frozenset()
        return frozenset(
            w for w in self.worlds if self.admissible(w, action)
        )

    def common_actions(self, block: Iterable[World]) -> Tuple[Action, ...]:
        block = tuple(block)
        return tuple(
            a
            for a in self.actions
            if a in self.available
            and all(self.admissible(w, a) for w in block)
        )

    def pointwise_feasible(self) -> bool:
        return all(self.common_actions((w,)) for w in self.worlds)


@dataclass(frozen=True)
class FiberCertificate:
    symbol: Symbol
    worlds: Tuple[World, ...]
    common_actions: Tuple[Action, ...]

    @property
    def safe(self) -> bool:
        return bool(self.common_actions)


@dataclass(frozen=True)
class ObservationAudit:
    status: str
    fibers: Tuple[FiberCertificate, ...]
    unsafe_symbols: Tuple[Symbol, ...]


@dataclass(frozen=True)
class CertifiedMessages:
    encode: Mapping[World, int]
    decode: Mapping[int, Action]

    @property
    def message_count(self) -> int:
        return len(self.decode)


@dataclass(frozen=True)
class ExactMinimum:
    value: Optional[int]
    witness: object | None


@dataclass(frozen=True)
class ContextContract:
    contexts: Tuple[Context, ...]
    local_worlds: Tuple[LocalWorld, ...]
    actions: Tuple[Action, ...]
    available: frozenset[Action]
    admissible_triples: frozenset[Tuple[Context, LocalWorld, Action]]

    def admissible(self, k: Context, x: LocalWorld, a: Action) -> bool:
        return (k, x, a) in self.admissible_triples

    def pointwise_feasible(self) -> bool:
        return all(
            any(
                a in self.available and self.admissible(k, x, a)
                for a in self.actions
            )
            for k in self.contexts
            for x in self.local_worlds
        )


@dataclass(frozen=True)
class ContextMessageProtocol:
    q: int
    m: int
    summary: Mapping[Context, int]
    encode: Mapping[Tuple[Context, LocalWorld], int]
    decode: Mapping[Tuple[int, int], Action]


def fibers_of_observation(
    worlds: Sequence[World],
    observation: Mapping[World, Symbol],
) -> Dict[Symbol, Tuple[World, ...]]:
    grouped: Dict[Symbol, List[World]] = {}
    for w in worlds:
        if w not in observation:
            raise ValueError(f"Missing observation symbol for world {w!r}")
        grouped.setdefault(observation[w], []).append(w)
    return {s: tuple(ws) for s, ws in grouped.items()}


def audit_observation(
    contract: FiniteContract,
    observation: Mapping[World, Symbol],
) -> ObservationAudit:
    fibers = fibers_of_observation(contract.worlds, observation)
    certificates = tuple(
        FiberCertificate(
            symbol=symbol,
            worlds=block,
            common_actions=contract.common_actions(block),
        )
        for symbol, block in fibers.items()
    )
    unsafe = tuple(c.symbol for c in certificates if not c.safe)
    return ObservationAudit(
        status="ACT" if not unsafe else "REFUSE",
        fibers=certificates,
        unsafe_symbols=unsafe,
    )


def _set_partitions(items: Sequence[World]):
    """Generate each set partition once."""
    if not items:
        yield tuple()
        return

    blocks: List[List[World]] = []

    def rec(i: int):
        if i == len(items):
            yield tuple(tuple(b) for b in blocks)
            return
        item = items[i]
        for j in range(len(blocks)):
            blocks[j].append(item)
            yield from rec(i + 1)
            blocks[j].pop()
        blocks.append([item])
        yield from rec(i + 1)
        blocks.pop()

    # Canonical symmetry breaking: first item starts first block.
    blocks.append([items[0]])
    yield from rec(1)


def minimum_safe_partition(contract: FiniteContract) -> ExactMinimum:
    if not contract.pointwise_feasible():
        return ExactMinimum(None, None)
    best = None
    best_part = None
    for part in _set_partitions(contract.worlds):
        if all(contract.common_actions(block) for block in part):
            if best is None or len(part) < best:
                best = len(part)
                best_part = part
    return ExactMinimum(best, best_part)


def minimum_action_cover(contract: FiniteContract) -> ExactMinimum:
    if not contract.pointwise_feasible():
        return ExactMinimum(None, None)
    available = tuple(a for a in contract.actions if a in contract.available)
    for r in range(len(available) + 1):
        for subset in combinations(available, r):
            if all(
                any(contract.admissible(w, a) for a in subset)
                for w in contract.worlds
            ):
                return ExactMinimum(r, subset)
    return ExactMinimum(None, None)


def certified_messages_from_cover(
    contract: FiniteContract,
    cover: Sequence[Action],
) -> CertifiedMessages:
    cover = tuple(cover)
    if not cover:
        raise ValueError("A nonempty finite contract needs at least one message.")
    decode = {i: a for i, a in enumerate(cover)}
    encode: Dict[World, int] = {}
    for w in contract.worlds:
        chosen = next(
            (
                i
                for i, a in decode.items()
                if a in contract.available and contract.admissible(w, a)
            ),
            None,
        )
        if chosen is None:
            raise ValueError(f"Cover does not certify world {w!r}")
        encode[w] = chosen
    return CertifiedMessages(encode=encode, decode=decode)


def minimum_certified_messages(contract: FiniteContract) -> ExactMinimum:
    cover = minimum_action_cover(contract)
    if cover.value is None:
        return ExactMinimum(None, None)
    protocol = certified_messages_from_cover(contract, cover.witness)
    return ExactMinimum(protocol.message_count, protocol)


def verify_certified_messages(
    contract: FiniteContract,
    protocol: CertifiedMessages,
) -> bool:
    for message, action in protocol.decode.items():
        if action not in contract.available:
            return False
    for w in contract.worlds:
        if w not in protocol.encode:
            return False
        m = protocol.encode[w]
        if m not in protocol.decode:
            return False
        if not contract.admissible(w, protocol.decode[m]):
            return False
    return True


def _all_functions(domain: Sequence[object], codomain_size: int):
    if codomain_size <= 0:
        return
    for values in product(range(codomain_size), repeat=len(domain)):
        yield dict(zip(domain, values))


def find_context_message_protocol(
    contract: ContextContract,
    q: int,
    m: int,
) -> Optional[ContextMessageProtocol]:
    if q <= 0 or m <= 0:
        return None

    states = tuple(
        (k, x) for k in contract.contexts for x in contract.local_worlds
    )
    if not states:
        return None

    for summary in _all_functions(contract.contexts, q):
        for encode in _all_functions(states, m):
            used_pairs = sorted(
                {(summary[k], encode[(k, x)]) for k, x in states}
            )
            candidates: Dict[Tuple[int, int], Tuple[Action, ...]] = {}
            failed = False
            for qm in used_pairs:
                valid = tuple(
                    a
                    for a in contract.actions
                    if a in contract.available
                    and all(
                        contract.admissible(k, x, a)
                        for k, x in states
                        if (summary[k], encode[(k, x)]) == qm
                    )
                )
                if not valid:
                    failed = True
                    break
                candidates[qm] = valid
            if failed:
                continue

            # A total decoder needs some available fallback for unused cells.
            available_actions = tuple(
                a for a in contract.actions if a in contract.available
            )
            if not available_actions:
                continue
            fallback = available_actions[0]
            decode = {}
            for qi in range(q):
                for mi in range(m):
                    decode[(qi, mi)] = candidates.get((qi, mi), (fallback,))[0]

            protocol = ContextMessageProtocol(
                q=q,
                m=m,
                summary=summary,
                encode=encode,
                decode=decode,
            )
            if verify_context_message_protocol(contract, protocol):
                return protocol
    return None


def verify_context_message_protocol(
    contract: ContextContract,
    protocol: ContextMessageProtocol,
) -> bool:
    states = tuple(
        (k, x) for k in contract.contexts for x in contract.local_worlds
    )
    for k in contract.contexts:
        if k not in protocol.summary:
            return False
        if not (0 <= protocol.summary[k] < protocol.q):
            return False
    for state in states:
        if state not in protocol.encode:
            return False
        if not (0 <= protocol.encode[state] < protocol.m):
            return False
        k, x = state
        qm = (protocol.summary[k], protocol.encode[state])
        if qm not in protocol.decode:
            return False
        a = protocol.decode[qm]
        if a not in contract.available:
            return False
        if not contract.admissible(k, x, a):
            return False
    return True


def context_message_feasible(
    contract: ContextContract,
    q: int,
    m: int,
) -> bool:
    return find_context_message_protocol(contract, q, m) is not None


def pareto_frontier(
    contract: ContextContract,
    max_q: Optional[int] = None,
    max_m: Optional[int] = None,
) -> Tuple[Tuple[int, int], ...]:
    if not contract.pointwise_feasible():
        return tuple()
    max_q = max_q or max(1, len(contract.contexts))
    max_m = max_m or max(1, len(contract.actions))
    feasible = [
        (q, m)
        for q in range(1, max_q + 1)
        for m in range(1, max_m + 1)
        if context_message_feasible(contract, q, m)
    ]
    minimal = []
    for p in feasible:
        dominated = any(
            r != p and r[0] <= p[0] and r[1] <= p[1]
            for r in feasible
        )
        if not dominated:
            minimal.append(p)
    return tuple(sorted(minimal))


def summarize_contract(contract: FiniteContract) -> dict:
    cover = minimum_action_cover(contract)
    safe = minimum_safe_partition(contract)
    messages = minimum_certified_messages(contract)
    return {
        "pointwise_feasible": contract.pointwise_feasible(),
        "minimum_action_cover": cover.value,
        "minimum_safe_symbols": safe.value,
        "minimum_certified_messages": messages.value,
        "action_cover_witness": list(cover.witness or ()),
        "safe_partition_witness": [
            list(block) for block in (safe.witness or ())
        ],
    }


__all__ = [
    "FiniteContract",
    "FiberCertificate",
    "ObservationAudit",
    "CertifiedMessages",
    "ExactMinimum",
    "ContextContract",
    "ContextMessageProtocol",
    "audit_observation",
    "minimum_safe_partition",
    "minimum_action_cover",
    "minimum_certified_messages",
    "verify_certified_messages",
    "find_context_message_protocol",
    "verify_context_message_protocol",
    "context_message_feasible",
    "pareto_frontier",
    "summarize_contract",
]
