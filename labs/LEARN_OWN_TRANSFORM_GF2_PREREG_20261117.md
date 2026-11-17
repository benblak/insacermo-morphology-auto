# INSACERMO CORE — Self-discovering a *new* transformation beyond signed permutations
Pre-registration frozen **BEFORE RUNNING THE NEW HIDDEN ORACLES** on 2026-11-17.
Historical INSACERMO MAX TOTAL, C3 and all previous certificates remain untouched.

## The exact scientific question
The prior learner knows how to identify a 5-variable shared Boolean abstraction under signed variable permutations/complementations. Now an independent 24-bit oracle hides that *same* previously mined 32-entry abstraction, but its 5 latent bits are:
1. distributed across **8 or 9 active physical bits**, with a nontrivial XOR-linear kernel; and
2. on some cases distorted by a **nonlinear, degree-2 reversible coordinate shear**, not representable by the previous signed-permutation family or a linear bijection.

Can a target-blind learner **discover a smaller quotient via observed translation invariances**, infer the required representation type from the observed ANF degree, then find a witness map to the frozen prior abstraction? No target coordinates, kernel basis, masks, affine map, nonlinear shear position, secret case class, or target expression supplied to learner.

**Source abstraction frozen from previous validated orbit study:** 5-bit canonical truth table decimal `56032425`, SHA and witness in previous final Lean source `labs/OrbitCert.lean`. The full source table is known to the researcher but none of the new embeddings are.

## Five secret, fixed-generator cases
Deterministic seed 71411, all over 24-bit Boolean input vectors. Their sources are private subprocess oracles with case names only:
- `affine_8`: exactly 8 active bits (5 effective XOR dimensions), linear mixing + a hidden invertible 5x5 binary basis transformation and polarity.
- `shear_8`: exactly 8 active bits but a single degree-2 triangular Boolean shear is applied to five quotient coordinates before the invertible linear map. Must NOT be affine-equivalent to the source 5-bit function, as its algebraic degree should increase from 2 to 3. If degree fails to increase, verdict FAILED_STRUCTURE_ASSUMPTION, no change to seed/case.
- `shear_9`: exactly 9 active bits, four-dimensional observed translation kernel, otherwise a different hidden triangular shear with the same invariance requirements.
- `needle_8`: same law as `affine_8` except a single predeclared hidden 24-bit flipped-input exception. Learner must not certify global law even if it never probes the needle.
- `negative_8`: deterministic unrelated pseudo-random 8-variable Boolean table, no designed 5-dimensional linear quotient; should refuse transfer.

All oracle parameters are deterministic from case name and seed, fixed before results. Private oracle definition is not imported into learner. Auditor can inspect it **only after all models and query transcripts are sealed**.

## Falsifiable, fixed protocol
1. For each target, 24 initial full-input random contexts; at each context ask the result and all 24 single-bit flips (so support detection only from actual binary responses, not from source program). A duplicate answer consumes no new oracle call. Require 5<= detected support <=9, else refuse.
2. Ask the oracle every bit assignment on the detected physical support with all other 24-bit controls fixed to zero. Thus up to 512 full-support truth-table observations. This exhausts only the **selected finite projection**, NOT the original 16,777,216-point law.
3. Inspect the entire observed table for XOR translation invariances: `K={d: ∀x, f(x⊕d)=f(x)}`. Discover its basis by Gaussian elimination and construct a 5-bit quotient without being given its basis. Require `dim(K)=support_size-5`, and all quotient classes exactly consistent. Negative control expected refusal.
4. On the 5-bit quotient calculate algebraic normal form (ANF) degree via direct Möbius transform. Prior H has degree 2. First try to solve for an invertible affine coordinate re-encoding `q↦Aq⊕b` by **observation-based partial-basis backtracking** (no list of candidate equations supplied).
5. Only IF affine solve fails AND observed degree is greater than 2: generate generic minimal degree-2 Boolean coordinate corrections `q_j ↦ q_j XOR (q_a AND q_b)`, with `j,a,b` chosen by the learner, and retry the exact affine witness search. If still no witness, REFUSE_TRANSFER (no arbitrary posthoc grammar changes).
6. Seal all discovered supports, invariance bases, transformation witnesses, all transcript pairs and conditional verdicts **BEFORE** evaluating final 2,048 independent randomly selected 24-bit heldout inputs per target (disjoint from all oracle training queries).
7. Independent auditor reimplements the truth check and verifies 2,048 heldout answers, support/kernel rank, quotient factorization, affine/shear witnesses, ANF degree, and the true needle input revealed **only after scoring**.
8. All global truth verdicts **REFUSE_UNCONDITIONAL**. An arbitrary exceptional input can always remain unqueried.

No source query-cost advantage is presupposed. The quotient is empirically verified on its observed finite subspace; irrelevance of outside variables remains unproved.

## Predeclared success conditions
- `affine_8`: correct kernel dim3, affine witness, exactly 2,048/2,048 heldout successes.
- `shear_8`: correct kernel dim3, affine hypothesis must FAIL, degree rises above 2; learner creates a quadratic shear witness, 2,048/2,048 heldout success.
- `shear_9`: correct kernel dim4, affine hypothesis must FAIL, shear repair successful, 2,048/2,048 heldout success.
- `needle_8`: same discovered *finite* quotient as clean, with universal REFUSE. If queried, report detected exception without changing rules.
- `negative_8`: refuses unsupported five-dimensional quotient/transfer.
Report every failure, no cherry-picking or retuning after holdout.

## Lean proof contract
A separate Lean file SHALL prove universal Boolean-linear kernel factorization *conditional on observed translation invariance*, plus finite exact 256/512-point quotient equalities and all discovered affine/shear witnesses. It SHALL NOT claim unrestricted physical truth, free mathematics invention, or universally correct learner. Every CI compilation status published with exact Lean source SHA256.

## Crucial limits
This is a SYNTHETIC finite Boolean laboratory, not natural science or a new theorem of physics. The **general operations** XOR, Gaussian elimination, Shannon truth tables, ANF degree, affine-basis synthesis and an allowed quadratic shear grammar are designed by humans. The learner chooses the needed transform and its parameters **from data**, rather than the precise transform being preloaded. This is a bounded but meaningful step beyond coordinate permutations.
