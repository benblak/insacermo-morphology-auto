# INSACERMO CORE — Learned XOR latent coordinates after breaking signed-permutation hypothesis

**2026-11-17. Only core objective: self-discovery and critical falsification of a mathematical representation. Historical MAX TOTAL / C3 and prior artifacts remain untouched.**

Pre-registration **before running any newly defined oracle case**: commit `fbc2962593d0170e08ed2d5d4c9e904216ddc8a8`, `labs/XOR_QUOTIENT_SELF_INFERRED_PREREG_20261117.md`.

## Actual autonomous synthetic experiment
- Unnamed 24 input bits, query-only private oracle subprocess. Three different source laws and six target laws. The secret formulas and mixing masks were NOT passed to the learner.
- Instead of enumerating possible signed permutations, the learner constructs an empirical GF(2) algebraic normal form from 0, 24 singletons, 276 pairs, then 64 out-of-basis falsifying tests. It derives the rank-4 bilinear polar form and automatically synthesizes 5 **XOR mixtures of raw controls** by symplectic factorization. There is no pre-enumerated list of the true XOR masks.
- Actual clean source and target laws have **13–18** influential *raw* input bits, but factor through **5 synthesized latent XOR features** each. A simple 5-input permutation from the previous lab cannot describe them.
- 3/3 source and 3/3 clean target systems were reconstructed as the same five-argument Boolean quadratic abstraction; **3,072/3,072** genuinely reserved predictions correct. `target_rare` also passes 1,024 holdout points but has a verified fixed hidden exception at input 978436, so NO global truth can be claimed.
- Negative controls: `target_cubic` generated observable cubic terms, so automatic degree-2 candidate was refuted and transfer refused (2,389 oracle calls). `target_rank2` has bilinear rank 2 rather than 4, so transfer refused (365 calls).
- Source/target/rare normal discovery uses 365 oracle calls each. Across **all nine** oracles, **5,309** discovery/challenge oracle responses were recorded.
- **Independent Python checker PASS**: independently replayed all 5,309 source answers; reconstructed all 301 empirical ANF coefficients for each case; checked all five latent coordinate masks and their low-degree algebraic identity for seven accepted models, 3,072 correct clean heldout labels and 1,024 rare-case holdout labels, both negative-control refusals and actual fixed rare exception. Independent receipt: `INDEPENDENT_XOR_COORDINATE_ABSTRACTION_PASS`.

## Lean theorem check
GitHub workflow `.github/workflows/insacermo-xor-quotient-lean.yml` compiled `labs/XorCoordinateAlgebra.lean` with **Lean 4.33.1**. Real archived GitHub diagnosis `labs/xor_quotient_lean_results_20261117/status.txt` states **lean_exit=0, result=PASS**, with exact proof SHA256 `c7c5c9a7bb60247b0d563e8bea9c6dca023a17bfb301dbf9c090c091089f4f9b`. Lean proves the general Boolean pair polarization, affine-shift expansion, five-coordinate quadratic decomposition, abstraction transport when features agree, and the unavoidable unqueried exception counterexample. It does **not** compile the Python search algorithm or prove that an unobserved natural law is quadratic.

## Strong boundaries
- Synthetic oracles were **designed** to belong to a common quadratic class; this is NOT a scientific novelty or unrestricted discovery from nature.
- Generic Boolean algebra GF(2), degree ladder (≤3), and symplectic reduction are **programmed methods**, not concepts created from nothing.
- No assumption-free 24-bit universal-law certificate: every verdict **REFUSE_UNCONDITIONAL**.
- No independent ground-truth physical dataset, no established query-cost advantage, no proof of optimal model discovery.

## Complete current-conversation reproducible ZIP
`INSACERMO_CORE_XOR_LATENT_REPRESENTATION_20261117.zip`, SHA256 `ced8a3694d70da1cea46b64dd550972aa86ba33748cb2232306826724f80bdcf`; source code, hidden oracle, independently implemented checker, sealed model/traces, results, generic Lean certificate source, README and checksums. Reproduce with `python learner.py && python independent_audit.py`.

**Next ONLY conceptual obstacle:** generalized self-generated representations outside GF(2) quadratic forms, with genuine external validation. Keep frozen historical engine intact.
