# INSACERMO CORE: coordinate-free reusable Boolean abstraction, frozen preregistration 2026-11-17
Full local protocol: /mnt/data/insacermo_isomorphism_20261117/PREREG.md, SHA256 **e4a2d5eab438b5da8b94dfc33beea74ecded852959e8a0de1f8da717bd0c58f1**.

**Question only:** can an oracle-only program recognize the same unknown 5-bit nonlinearity when it has been transferred to DIFFERENT input bits, reordered, bitwise polarity-flipped, and output-flipped, without hand-supplying the embeddings or latent concept?

- Synthetic 24-bit inputs; generator seed **46331**. Three source oracles embed one 5-bit nonlinear latent function on distinct randomized coordinates plus an external Boolean gate. Five target oracles: three fresh embeddings (including one two-gate case), one embedded law with one precommitted rare exception, and one unrelated 7-bit negative control.
- Learner sees ONLY oracle membership answers, no hidden generators, source/target formulas, embeddings or masks.
- Sources and targets: 20 random input contexts + 24 one-bit flips per context to infer sensitivity, followed by the full projected truth table on ≤8 observed variables. Produce cofactor 5-bit functions by fixing one active input.
- Try exact coordinate-aligned cofactor match first (previous laboratory), and only when it fails expand its candidate description to **input permutation + input polarity XOR + output XOR**. Generate canonical 32-row truth table via complete orbit enumeration, 5!×2^5×2 transformations; require a common 5-bit orbit in all three sources.
- Target discovery: reconstruct projected truth; find common orbit and recover actual input/output transformation witness, or refuse transfer. All learner models and query answers sealed before 1024 fresh 24-bit holdout queries per target.
- Predeclared pass criteria: shared macro 3/3 sources, 3/3 clean target matches and correct whole projected table + 1024/1024 holdout, unrelated control REFUSE, rare exception REFUSE_UNCONDITIONAL; every nonexhaustive law globally REFUSE_UNCONDITIONAL.
- Independent Python auditor replay queries and actual oracle from source only after sealing, check all correspondences and metrics; additionally Lean must compile a generic theorem about invertibility of renaming + output XOR and finite 32-row witness checks (no new Lean mathematical theorem about unrestricted discovery).
- No source query or representation cost saving claimed: querying full quotient gives a straightforward baseline, which must be acknowledged.
- Both the **synthetic common latent structure** and the **general symmetry-search class** are deliberately provided by the experimental design. This is NOT free invention of mathematics, a physical-law discovery, universal certitude, or optimal query efficiency. Historical INSACERMO MAX TOTAL/C3/Lean code remains FROZEN.

This file is committed before computing any newly constructed oracle result.