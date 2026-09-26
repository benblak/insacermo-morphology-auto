# INSACERMO public-interface prototype

This directory is a standalone, dependency-free prototype for the future public
INSACERMO website.

It is deliberately a **presentation prototype**.  The scenario buttons use
demonstration data and do not claim to execute the Lean kernel or domain
backends.

The expected production data contract is represented by `example_result.json`
and is aligned with `engine/contract_io_v1.py`.

## User-facing structure

1. Future Contract
2. Current system / backend audit
3. ACT / PROBE / REPAIR / REFUSE
4. Future map: immediate / recoverable / irreversible / unknown
5. Joint obstructions
6. Proposed probe or repair
7. Expert evidence drawer

## Scientific rule

The UI must never collapse evidence levels.  A result must retain whether its
support is formal, exact, exhaustive, empirical, heuristic, or merely declared.

Frozen scientific reference:
- branch: `insacermo-engine-freeze-2026-09-26`
- commit: `3b712a0afdbe5f8893a43cbbe94868f2b8627e06`
- global root run: `36244409179` — SUCCESS
