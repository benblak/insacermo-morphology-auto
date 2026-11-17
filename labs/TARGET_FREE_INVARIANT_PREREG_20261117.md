# INSACERMO — target-free empirical invariant search, frozen experimental contract
Date: 2026-11-17. Commit BEFORE executing automated search and reporting its held-out scores. Isolated lab; historic C3 and Lean engine remain FROZEN.

## New bottleneck (distinct from repeated supervised predictive models)
The experimenter is given a whole array of authentic measurements, **no target feature and no requested equation**. It must choose WHICH measurable quantity to explain, formulate a compact relation from the other quantities, choose further observations of its target, try to falsify its best equation, and test the equation in a previously excluded physical/biological regime.

## Authenticated archives
- Sklearn built-in Wisconsin Diagnostic Breast Cancer cytology data: 569 real samples, 30 physical cell-image measurements. Source `sklearn.datasets.load_breast_cancer()`. On installed sklearn 1.8.0, SHA256 raw NumPy array `6b202a2072f9a0385f405a8f8605b1b06f6f36ae6d23d9cd6cbbc0974a416bc7` and labels `1763c0f8cd3f454b9eda72031113884593bb382411c0cd511e3ec6e7ac85cddb`.
- Two independent **directions** of regime-transfer validation, one experiment on each microscopy image-derived clinical diagnostic group withheld whole. These labels only serve to divide evaluation groups; the researcher sees only unnamed numeric measurement channels.
- An external negative/transfer control on UCI wine chemistry array from `sklearn.datasets.load_wine()`, 178 samples, 13 chemistry measurements, group 2 excluded entirely. Feature array hash `8edcf3903afd97c64d51e0212eb10b213f7943da650574d1c055b836c5c35d37`, label hash `b6514e07a6d27854e0da000ca82d8d8cc3d0cb904c51600344ca34f1ee04884b`.
- IMPORTANT provenance caveat: before preregistration, the experiment designer explored geometric ratios between radius, area and perimeter for WDBC, including group medians. Therefore this is an **exploratory, not human-blind** WDBC demonstration. The program itself must not be told those relationships. Never describe it as a new historical physics discovery or independent prospective confirmation.

## Frozen algorithm (identical across all three runs)
For WDBC, train regime A = class 1 / holdout regime B = class 0, then reverse. For Wine, discovery+challenge from groups 0 and 1 / entire group 2 held out. Pre-split the training regime by deterministic hash SHA256(`insacermo-target-free-20261117:<row_id>`) and select first floor(0.7*train_n) for discovery, rest challenge. Diagnostic labels are NOT available to the searcher, except that the evaluated rows were preselected.

Only discovery rows initially visible in full. Given p channels, automatically construct every directed candidate `Y_j ≈ c·X_i^q`, with i≠j, q in {-2, -1, -0.5, 0.5, 1, 2}, if all discovery feature values involved strictly positive. Coefficient c determined from the median of Y_j / X_i^q on discovery. The learner is not given j, i, q, c. Candidate scoring: median abs log residual + .35 × 90th percentile abs log residual + .001 × |q-1|. Candidate ranking on discovery only. Choose the best (j,i,q) by score then deterministic lexicographic tie-breaking. No semantic feature labels given during search. Candidate language is nevertheless supplied and restricted.

Fix the *chosen target j* after discovery, hide Y_j for all challenge and withheld-regime rows. Expose challenge X except Y_j to the question-selector. Budget exactly 20 challenge target readings (if challenge size supports it). At each step refit the coefficient of the leading model; rerank ALL q/source combinations for the fixed target from the currently observed labeled rows. Query one challenge row maximizing disagreement of the top three candidates' predictions (standard deviation divided by their median absolute magnitude, cap extreme ratios at 3); deterministic lowest row ID on tie. Provisional hypotheses and their failures logged after each query. Zero reading of held-out regime target or class labels until all models and query traces sealed.

**Eight** fixed-seed random challenge policies (seeds 17,31,43,59,71,89,101,127) use same 20-label budget and rerank the same target candidates after each observation. All model parameters and queried row IDs are sealed in one JSON before holdout evaluation.

## Holdout and acceptance
On a held-out regime, assess target feature prediction with relative error `|truth-predicted|/truth` on ALL of its rows (invalid or nonpositive target is a failure), report median, mean, 90th percentile, fraction within 10%, and RMSE in target units. Baselines use constant median target from same labeled discovery+20 rows and best 1-feature pure proportional `cX` fitted on the same information. All 8 random policies evaluated; no picking best seed.
`ACCEPT_TRANSFER_INVARIANT` iff (1) median relative error ≤4%, (2) ≥90% holdout rows have ≤10% relative error, (3) ≥50% improvement in median relative error versus constant-median predictor. Otherwise `REFUSE_INVARIANT_TRANSFER`.
Automatic scoring may identify trivial measurement redundancy, not physical causality or a fundamental law. No claims of a novel biological/medical diagnostic tool.

## Proof and audit
Separate verifier reruns exact held-out metrics, reconstructs target choice from discovery-only rows and checks challenge indices, compares all 8 random seeds, and checks source bytes hash. If successful, a finite integer/rational error-count certificate can be supplied separately to Lean, but no Lean certification of biological mechanisms.

## Change control
Results on exposed heldout cannot be used to tune grammar/thresholds or rename failure as success. If 20 queries infeasible for some condition, mark infeasible and refuse, don't silently change budget. Historic INSACERMO engine/Lean/site remain frozen.
