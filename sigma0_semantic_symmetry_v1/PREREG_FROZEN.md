# INSACERMO Sigma0 — Semantic Symmetry V1 (frozen protocol)

Date frozen: 2026-09-27
Branch: insacermo-sigma0-semantic-symmetry-v1

## Goal

Test a single application-level conjecture without modifying the INSACERMO V1 kernel:

> A symbolic message can preserve a decision without conventional labels only when the residual symmetries of the transmitted relational structure do not move the contract-relevant meaning.

This is **not** a theorem about universal language, extraterrestrial intelligence, cosmology, or consciousness.
It is a finite exact stress test of a "last message" construction under explicit decoder ambiguity.

## Model

A message contains:
- a finite set of symbols V = {0,...,n-1};
- an unlabeled binary relation E between symbols;
- one intended contract-relevant symbol t ("the target meaning");
- optional grounded anchors A ⊆ V \\ {t}.

A possible decoder is any permutation p of V that preserves E and fixes every grounded anchor.

For a decoder-world p, the correct concrete action is p(t).

INSACERMO receives:
- worlds = all decoder permutations consistent with the anchors;
- actions = V;
- all actions available;
- admissible(p,a) iff a = p(t);
- one observation fiber containing every decoder-world.

Therefore the frozen engine returns ACT exactly when all surviving decoder-worlds agree on the same image of t.

## Frozen structures

All anchor searches exclude the target itself; otherwise the problem is trivial.

1. EMPTY6
   - n = 6
   - E = ∅
   - target = 0
   - maximal label symmetry.

2. CYCLE6
   - n = 6
   - E = cycle (0-1-2-3-4-5-0)
   - target = 0.

3. PATH6
   - n = 6
   - E = path (0-1-2-3-4-5)
   - target = 0.

4. ASYM6
   - n = 6
   - E = {(0,2),(0,3),(0,5),(1,2),(1,4),(2,3)}
   - target = 0.
   - This graph was frozen because exhaustive permutation checking gives a trivial automorphism group; the runner recomputes that fact from scratch.

## Primary endpoints

For each structure:
1. exact automorphism count;
2. exact minimum number of non-target grounded anchors needed for ACT;
3. one lexicographically first minimum anchor witness;
4. number of decoder-worlds remaining at that witness;
5. engine verdict before anchoring and at the minimum witness.

## Falsification / integrity criteria

- The unmodified file insacermo_actionability_engine_v1.py must be used.
- No generic INSACERMO theorem or engine criterion may be changed.
- Automorphisms are enumerated exhaustively over all n! permutations.
- Anchor subsets are searched in increasing cardinality.
- ACT must be obtained from audit_observation, not hard-coded from group theory.
- The run fails if the independently computed "all p(t) agree" condition differs from the engine verdict.

## Interpretation boundary

A positive result shows only this finite fact:

> under an explicitly declared family of decoder symmetries, enough relational asymmetry or grounding can make a contract-relevant target invariant.

It does not establish that any physical or mathematical symbol is universally understood.
It does not establish a universal message.
It does not claim novelty over automorphism groups, distinguishing sets, graph individualization, or related symmetry-breaking mathematics.

The INSACERMO-specific question is operational:
how much grounding must remain before all still-possible decoders admit one common contract-safe action?
