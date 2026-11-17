# INSACERMO CORE — experimentally discovered and reused abstraction (2026-11-17)

**Core priority only:** find a useful new substructure in hidden Boolean laws, reuse it on laws not supplied in advance, enlarge the language after falsification, and refuse unjustified universal certainties. Historic MAX TOTAL, C3 and Lean kernel are frozen.

This was PRE-REGISTERED on the isolated branch in commit `e7a1032135a9e8638f0d8b66e2e4368153867372`. Full protocol (artifact) SHA256 `8e0d9fc6ebed173cbae80377aeefd4a286510049aa0716e2efc8f17cd7dffdd9`. **Independent Python audit PASS**, not a new Lean theorem.

**Discovery:** three separate synthetic 24-bit oracles, 16 contexts + 24 single-bit flips each, exhaustive projection, shared cofactor mining. The code was not given secret formulas, input-support sets or the specific core concept. It discovered 5-bit `H_auto_0` on input bits [10,11,12,19,23], with an independently checked 32-entry complete truth table, shared by all 3 source laws. Source oracle queries: **1392** (464 per source).

**Transfer on five previously undisclosed synthetic laws** (final scoring on 1024 fresh configurations per law, after sealing model+all oracle transcripts):

| Target | Learned connector arity | Transfer queries | Baseline rebuild queries | Independent 1024-point result |
| --- | ---: | ---: | ---: | --- |
| target_0 | 1 | 104 | 464 | 1024/1024 correct |
| target_1 | 1 | 102 | 464 | 1024/1024 correct |
| target_2 | 2 | 416 | 528 | 1024/1024 correct |
| target_3 | 1 | 104 | 464 | 1024/1024 correct; **rare hidden exception invalidates universal law** |
| target_4 (unrelated negative) | none; REFUSE | 446 | 464 | REFUSE_TRANSFER, no candidate |

**Crucial counterexample-driven representation enlargement:** on target_2, all 19 one-external-input compositions were evaluated; best had **12 disagreements out of 64 challenge points**. Automatic escalation to two-external-input truth-table connector generated the correct new structure using bits [15,22] (175 candidates checked in total), correct on all 128 projected configurations and 1024 sealed-holdout points. No named AND/XOR/majority repairs were supplied to the learner, but generic Shannon cofactor operations and bounded search arities 1 and 2 were programmed.

**Costs, including negative finding:** for three clean target laws, target-only transfer costs 622 versus 1456 baseline queries (57.3% reduction). All five targets transfer =1172 calls vs baseline=2384 calls. But **source discovery costs 1392** additional oracle calls, so end-to-end experimental cost **2564**, worse than 2384 baselines across five tasks. No claim of net amortized savings or minimal query count. More transfers needed to recover discovery investment.

**Rare exception:** target_3 received no exceptional query; its transferred formula is WRONG at that hidden input even though 1024/1024 holdout examples were correct. Post-seal independent auditor explicitly confirmed the counterexample. All five verdicts are **REFUSE_UNCONDITIONAL**. Negative control was appropriately rejected.

**Independent verification:** separate `independent_audit.py` recomputes every observed oracle answer, 32-row shared latent truth table, all three sources' 64-entry reduced truth tables, 64 challenge answers for each target, 1024 truly withheld target answers for each, exact reduced truth tables of the three clean targets, correct rejection of unrelated target, query counts and source digests. Receipt: `INDEPENDENT_REUSABLE_ABSTRACTION_PASS`.

**Full reproducible artifact**: conversation ZIP `INSACERMO_CORE_AUTONOMOUS_ABSTRACTION_TRANSFER_20261117.zip` SHA256 `f4b49d3fca18731c2172f6378e6bfc6b1965b2e546aeb0fa17d3bedcce93de63`. Includes complete scripts, source generator, preregistration, pre-holdout sealed model and traces, result, independent audit receipt, README and SHA256SUMS.

**Limits:** This is a synthetic Boolean lab with deliberately shared fixed-coordinate core. The investigator uses a **programmed general representation** (Shannon truth-table cofactors and generic connector arity 1→2), rather than inventing unrestricted mathematical primitives. No physical law or universal discovery proved; no new Lean theorem for this learner; no source-cost amortization yet. Core historic engine unchanged.
