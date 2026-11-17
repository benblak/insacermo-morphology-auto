# INSACERMO — CORE RESULT: unprogrammed *specific* repair discovered through generic contrastive falsification (2026-11-17)

This is the **only core scientific priority**: finding unknown law structure and necessary assumptions without supplying the target formula or a menu of candidate structures. No new domain, Wine, Kepler or historic-engine changes. Original INSACERMO MAX TOTAL / C3 / Lean source stays frozen.

**Protocol preregistered BEFORE any new hidden-oracle experiments** in `labs/CONTRASTIVE_STRUCTURE_INVENTION_PREREG_20261117.md`, commit `dfdba3028d882a7fcb18326491b0e01631739fbc`. Full original preregistration local SHA256 `dbe6fe9939d0da44bbf28ce2be7628a8d3f818f6114ba01388ee63e6fa7a5526`.

## Controlled synthetic blind experiment

N=24 Boolean input controls (16,777,216 total configurations). Generic query-only learner; no target formula, no predetermined variable support, no monotonicity/antitonicity/affine class list, no majority or AND repair operator provided. The available *general mathematical primitives* are a Shannon reduced decision DAG, one-bit experiments, contrastive minimal-counterexample reduction, and generic support-relevance probing. This is not mathematics invented without any primitives.

The independent Python auditor reads hidden code only after sealing answers and graph hypotheses. Outcome: **INDEPENDENT_AUDIT_PASS**; all three clean cases have exact recovered support and exact projected truth table, plus 2048/2048 random independent full-input checks for each of four cases. No case exceeds 6000 unique oracle queries. Recorded results:

| Case | Initially observed support | Final inferred support | Unique queries | Automatic DAG reconstructions |
|---|---:|---:|---:|---:|
| Simple 3-input XOR reference | 3 | 3 | 643 | 0 |
| XOR plus **hidden threshold 3-of-4** | 3 | **7** | 2740 | **2** |
| XOR plus hidden conjunction of five | 3 | **8** | 4772 | **1** |
| Simple XOR with one precommitted rare 24-bit needle | 3 | 3 observed (actual support is 24) | 643 | 0 |

Crucial nonlocal challenge for threshold 3-of-4:
- Initial 301 low-Hamming-weight settings (0,1,2 active) cannot reveal the additional 3-of-4 interaction.
- A 24-bit all-ones challenge contradicts the initial projected DAG.
- **Flipping any one of the four unknown bits at all-ones does NOT change the hidden threshold output** (4 active -> 3 still active). The recorded external single-flip sensitivity is empty.
- The generic contradiction *minimizer* derives a smaller contradicting input with exactly 3 previously unseen causal inputs.
- The learner expands its support 3 -> 6 and reconstructs a DAG.
- The next generic challenge of other-bit irrelevance identifies the **fourth** input and expands support 6 -> 7 with a second DAG reconstruction.
- The auditor confirms complete 2^7 projected truth and 2048 independent full-space checks.

In the second compound-gate case, generic minimization finds all 5 previously hidden bits and expands 3 -> 8, one rebuild.

The clean XOR and its rare one-point exception have identical ordered 643-query transcripts AND answer hashes. The hidden needle was not queried. Their true laws differ. Both verdicts properly **REFUSE_UNCONDITIONAL**. This aligns with the previously Lean-proved unqueried-completions theorem (prior branch), not a new Lean proof of the current searcher.

Total unique discovery queries across 4 experiments: **8798**. The oracle audit independently replays the complete source-defined answers and all full projected tables. This is **a controlled synthetic validation**, not discovery of a new physical law, not universal identification of arbitrary functions, not minimal-query optimality, and not proof of unrestricted invention of representations. The test was deliberately designed to challenge simple bit toggles; the general contrastive algorithm remains programmed.

## Reproducible artifact

Conversation artifact `INSACERMO_CORE_CONTRASTIVE_DISCOVERY_20261117.zip`, SHA256 `314b48b096388b11fd0b13fdfcbdc9c9b1d5f9d972cab309df0bdb5af68318ab`.
Contains `PREREG.md`, `learner.py`, hidden `private_oracle.py`, `independent_audit.py`, `sealed_results.json`, `independent_receipt.json`, README and source SHA256SUMS. Reproduce with standard Python 3: `python learner.py && python independent_audit.py` in its unpacked folder.

**Next ONLY question:** ask the searcher to invent a *new primitive or abstraction* as an answer to a falsification, rather than only adding input variables to a general Shannon language; test with genuine independent provenance and a new unseen oracle. Do not repeat old scientific-domain demonstrations. Historical MAX TOTAL/C3 kernel remains untouched.
