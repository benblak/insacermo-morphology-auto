# Frozen protocol — INSACERMO core representation repair, 2026-11-17
This checkpoint is committed BEFORE running any new hidden-oracle experiments.

The complete pre-registered local protocol resides in the conversation artifact
`INSACERMO_CORE_CONTRASTIVE_20261117/PREREG.md`
SHA256 `dbe6fe9939d0da44bbf28ce2be7628a8d3f818f6114ba01388ee63e6fa7a5526`.

**Only goal:** no more known-law re-detection. Does a target-free Boolean law learner uncover a **previously unknown compound-variable dependency** by automatically generating non-local experiments after its projected Shannon decision graph is contradicted?

N=24 binary inputs. Fixed 6000 oracle calls per case.
Exactly 301 low-Hamming-weight initial probes (weights 0,1,2), discover
locally relevant variables from observed edges, reconstruct reduced Shannon DAG.
Generic all-ones challenge tests projection under a distant context.
On contradiction use generic contrastive counterexample minimization / coordinate
elimination; don't give the learner predefined majority, parity, or repair operators.
Expand support, regenerate DAG, challenge support-irrelevance with projected
bit-toggle interventions and 256 fresh random queries. Up to 5 repairs.
Never claim unconditional law absent exhaustive 2^24 observations.

Four private synthetic oracles seeded 2301: parity of 3 hidden variables;
same parity XOR threshold >=3 of 4 further unknown hidden variables;
same parity XOR conjunction of 5 further unknown variables;
clean parity with one precommitted rare flipped input.
No source import or secret reveal to the learner. Independent auditor checks
projected truth and 2048 random fresh points after sealing, 3/3 clean support
recovery gate, plus designed first-step single-toggle blind spot for 3-of-4.

All outcomes including failure frozen. The generic Shannon primitive and
contrastive query algorithm remain programmed; this does NOT prove unrestricted
mathematical invention, a natural law, or universal truth. Historical
INSACERMO MAX TOTAL/C3/Lean engine completely unchanged.
