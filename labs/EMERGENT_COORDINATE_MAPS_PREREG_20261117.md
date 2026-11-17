# INSACERMO — self-generated Boolean-coordinate maps after falsification
**Protocol committed before running the new hidden-oracle evaluation, 2026-11-17.** Isolated lab. MAX TOTAL, historical C3 and their Lean proofs are frozen and untouched.

## ONE core research question
In the previous successful test, a five-input latent concept was reused across input permutations, sign inversions and output flips; **the family of allowed transformations was explicitly supplied**. Can a learner given ONLY membership-query data find that family insufficient, construct new reversible input maps by enumerating **generic small truth-table operators**, and explain previously unmatched target functions without receiving named XOR/AND/OR transformation rules or the answer?

This is a bounded, programmed **metagrammar** (all 16 binary Boolean truth tables, 5-bit variable updates), not free invention of every conceivable mathematical operator.

## Sealed benchmark design
- Universe of oracle inputs: 24 Boolean variables, 16,777,216 configurations.
- Legacy latent five-bit truth table for source: integer `56032425`, **only the private oracle receives that constant**. Learner source is oracle-only, no secret imports.
- Generated cases using a source permutation and polarity (deterministic RNG seed **230117**), plus:
  1. source same latent law, on new coordinates (signed-permutation equivalent);
  2. target-1: composition with one *nonlinear* reversible two-control Boolean shear (target bit toggled by a two-input gate on other bits);
  3. target-2: composition with **two** such reversible shears (a genuine two-repair challenge);
  4. target-3: another nonlinear reversible shear under different permutation/polarities;
  5. negative control: an unrelated five-bit truth table of **the same Hamming weight**, RNG seed **99173**; do not change this seed after failure.
  6. needle: same law as one transferred target plus a precommitted single 24-bit exceptional input unseen by finite training/holdout.
- The private oracle chooses five nonoverlapping coordinate positions for source/targets using PRNG seed 230117. No learner access to positions, permutations, polarity, gate truth table or hidden exception.
- Important: by design the learner knows the existence of a **five-variable quotient and an oracle supplying bit inputs and outputs**; it does NOT know how those five features are embedded. The secret generator is synthetic.

## Fixed information and query budget
For each oracle: 32 deterministic uniform input contexts (seed **812811**) and 24 one-bit intervention neighbors per context, then identify support as all bits showing a change; refuse if support !=5. Query all 32 assignments to that support against a fixed background. Seal all source/target truth tables before any final evaluation.
- Source symmetry class is the complete signed-coordinate group of size `5! × 2^5 × 2 = 7,680`, not assumed sufficient.
- Stage A: direct lookup against signed-permutation orbit, and mark FAIL when no match.
- Stage B: derive a **new reversible feature map** by scanning every 5-variable position and every pair of OTHER coordinates, trying **all 16 possible two-input Boolean truth tables** as a binary gate and applying it as `x_i := x_i XOR truth(x_j,x_k)`. Gate tables are represented only as 0..15 and inferred through the 32 observed truth values. Allow at most two such gates; BFS with stable ordering by depth, lexicographic updates and gates. Do NOT give learner named logical gate recipes, secret gates, target embeddings or success labels.
- A solved target must present concrete witness maps, the transformed truth table, and the source-orbit witness. Predeclare stage B success >=2/3 nonlinear positive targets and strict refusal on the unrelated negative; at least one target should need two gate edits. If a target fails, report FAIL and DO NOT adjust gate budget or generator.
- Negative control must not be declared transfer solely because output populations agree.
- Reserve **1024 fresh full 24-bit contexts** per target (seed **43891**) and verify target predictions using **its sealed inferred complete five-input truth table**. These tests confirm the finite quotient, NOT extrapolation to excluded variables. Rare needle must remain REFUSE_UNCONDITIONAL even if unseen.
- Cap at 1024 oracle calls per source/target for discovery+quotient; gate search itself is offline synthesis over already observed 32-value tables. Report actual costs, no fictitious query saving.
- Independent evaluator (separate source file) replays every query and truth-table projection, checks all learned gate witnesses, verifies target examples and emits a counterexample for the rare exceptional law after sealing. Critically audit same abstract Hamming weight negative control.
- Historic INSACERMO remains unchanged; **never claim historical new physics, theorem about nature, absolute uniqueness, or Lean-certified correctness unless compiled**.

## Formal proof obligation
Lean should formally prove that ANY binary gate `h` gives a reversible 5-bit map `update(x,i,j,k,h)` whenever `i,j,k` are distinct, and that applying it twice is identity on the 32-element domain. Separately generate finite witnesses and verify them by `decide`; failure must be archived. This proves a mathematical property of the generated feature map, NOT unrestricted autonomous invention or hidden-oracle truth.

## Essential caveat
The learner still has a deliberately programmed universal *local map generator* (one output bit updated via 16 possible truth tables), and knows a five-variable quotient is meaningful. This is a deeper adaptive search than a signed-permutation catalog, **not** full self-invention of mathematical language. Report number of discovered operator kinds and whether they are non-affine; do not use novelty rhetoric.
