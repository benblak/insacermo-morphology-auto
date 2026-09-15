# INSACERMO Post-V4 Frontier Audit

Date: 2026-09-12
Status: research roadmap after V4 finite-theory freeze

## Purpose

Do not modify the frozen finite kernel to force agreement with broader literature or future experiments. The next stage is to test exactly which parts of the V4 skeleton survive when assumptions are relaxed.

Frozen skeleton:

`Contract -> Actionability / Obstructions -> Planner`

## Immediate literature frontier

### 1. Blackwell informativeness

Blackwell compares information structures through their decision performance. INSACERMO must position its capability-relative axis carefully: V4 often holds the representation fixed while changing the executable capability set, then asks which observational quotients remain action-sufficient.

Audit question: can the capability-relative SafeRep order be represented as a standard Blackwell decision problem by absorbing capability into the payoff/action model, and if so, what remains structurally new in the explicit capability-relative family and planner semantics?

### 2. Viability theory / controlled invariance

Viability theory studies states from which admissible controls can keep a dynamic system inside constraints. This is a major neighbor for dynamic INSACERMO.

Audit question: does dynamic SafeRep become a quotient-level viability kernel, and can PROBE/REPAIR be interpreted as changing information/capability coordinates before entering the viability kernel?

### 3. POMDP / active sensing

POMDPs jointly represent stochastic dynamics, partial observations and action choice, and active-sensing work explicitly optimizes information-gathering actions.

Audit question: can stochastic INSACERMO be reduced to a constrained POMDP with an explicit refusal state, or does the obstruction/capability-relative representation criterion produce a distinct structural certificate useful before/inside POMDP planning?

### 4. Rough sets / discernibility / reducts

Rough-set decision systems already use discernibility matrices and reducts; deterministic INSACERMO weighted-hitting formulations are close in spirit.

Audit question: identify exact equivalence and non-equivalence between deterministic actionability reducts and decision reducts. Do not claim the hitting-set primitive as novel.

### 5. Zero-error information / graph and hypergraph coding

Zero-error coding, confusability graphs and side-information design are close to fiber collision and exact action preservation.

Audit question: formulate deterministic SafeRep as zero-error computation/action coding and determine whether capability-relative obstruction hypergraphs correspond to known characteristic/confusability hypergraphs.

### 6. Adaptive submodularity / stochastic coverage

Adaptive submodularity provides greedy guarantees for certain information-gathering and stochastic coverage objectives. V4 already contains a capability-gain witness violating diminishing returns in a binary safety indicator.

Audit question: characterize when INSACERMO probe/repair gain is submodular, supermodular, neither, or adaptively submodular. This determines when greedy planning is justified versus provably unsafe.

## V5 target: stochastic actionability, not a new architecture

Replace Boolean `Good(s,a)` by a risk-sensitive admissibility predicate derived from an outcome law.

Candidate abstraction:

`Law(s,a)` = distribution of outcomes under world s and action a.

`RiskAcceptable(s,a;theta)` = declared risk functional of `Law(s,a)` is below threshold theta.

Then define:

`SafeRep_risk(B,C,h)` iff every realized fiber has some common action a in C that is risk-acceptable for every world in that fiber.

This preserves the finite V4 syntax while moving uncertainty inside the contract predicate.

### First theorem target

Capability monotonicity should survive immediately if admissibility remains action-local:

`C subset C' -> SafeRep_risk(C) subset SafeRep_risk(C')`.

### Harder theorem target

For stochastic model uncertainty / posterior beliefs, determine whether a minimal-obstruction characterization survives:

- finite support: likely yes after converting risk admissibility to a Boolean contract at fixed threshold;
- distributionally robust ambiguity: obstruction sets become ambiguity-dependent;
- chance constraints / expected utility: common-action intersections remain set-theoretic after thresholding;
- policies that learn while acting: static fiber hypergraphs may no longer be sufficient and must be lifted to histories/beliefs.

## Dynamic extension target

State at time t should include at minimum:

- ambiguity/belief state;
- current capability set;
- resource state;
- retained memory/representation state;
- future contract state if nonstationary.

Planner transitions include:

- PROBE: observation update;
- REPAIR: capability transition;
- ACT: controlled system transition;
- PRESERVE legality: forbid memory coarsenings that break declared future safety;
- REFUSE: terminal or safe abstention action under contract.

The critical comparison is with viability/POMDP theory. Dynamic INSACERMO should not be claimed as separate merely because notation differs.

## Falsification criteria for the generalization program

The finite theory should be considered structurally limited if any of the following occurs without a principled replacement:

1. stochastic actionability cannot be represented by a common-action criterion on uncertainty classes;
2. dynamic safety requires history information that cannot be expressed through a contract-relative state sufficient statistic;
3. capability expansion can invalidate an already-safe state once capability costs/interactions are included directly in the safety predicate, showing monotonicity requires stronger hypotheses;
4. no useful obstruction certificate survives beyond the finite exact setting;
5. the full planner reduces exactly to a standard existing framework with no additional theorem, certificate, or design object.

## Research rule

Future work must distinguish:

- exact theorem;
- formal verification;
- computational enumeration;
- frozen/preregistered empirical result;
- exploratory result;
- analogy to prior literature;
- candidate novelty.

No result should be promoted across these categories without new evidence.
