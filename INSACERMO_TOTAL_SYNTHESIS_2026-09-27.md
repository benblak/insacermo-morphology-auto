# INSACERMO — Total Synthesis and Closure State
## 27 September 2026

### Status

This document freezes the scientific interpretation of the deterministic finite INSACERMO kernel after the Total Closure milestone.

Machine-verified reference:
- branch: `insacermo-total-closure-kernel-v1`
- audited commit: `8917974781182fed71c7d2e4fac538622c63d2d2`
- GitHub Actions run: `36339127455` — SUCCESS
- frozen branch: `insacermo-total-closure-kernel-v1-freeze`

The CI checks the Lean build, rejects `sorry`, `admit`, and added custom `axiom` declarations in the audited source directories, and runs an explicit axiom audit.

---

# 1. What INSACERMO is now

INSACERMO is a contract-relative theory of future-preserving actionability.

Its core question is:

> What information, distinction, memory, context, communication, or capability may be destroyed now while preserving what the system must still be able to guarantee later?

A compact architecture is:

[
	ext{CONTRACT}
ightarrow
	ext{ADMISSIBILITY}
ightarrow
	ext{ACTIONABILITY}
ightarrow
	ext{COMPRESSION / COVER / OBSTRUCTION}
ightarrow
	ext{CERTIFIED MESSAGES}
ightarrow
	ext{INTERFACES}
ightarrow
	ext{RECURSIVE COMPOSITION}
ightarrow
	ext{FUTURE-SAFE BEHAVIOR}.
]

The current kernel is deterministic and finite. It does not claim that every stochastic, continuous, learned, or physical system is already covered.

---

# 2. Formal chain now machine-verified

## 2.1 Fibers and common-action safety

An observation may merge several worlds. A fiber is safe only when one currently available action is admissible for every world in that fiber.

This is the operational meaning of preserving the future after information loss.

## 2.2 Information = cover = obstruction

The finite kernel connects:
- safe encodings,
- action covers,
- obstruction coloring.

At the minimum level, the corresponding cardinalities coincide under the kernel hypotheses.

This makes compression operational: an information symbol is not merely a label; it may be decoded to a certified action.

## 2.3 Frontier universality

For an abstract resource preorder, every upward-closed feasibility region can be represented as an INSACERMO safety region.

Consequence: without extra structure there is no universal smooth scalar tradeoff law. Frontiers can contain branches, plateaus, jumps, synergy, and incomparable minima.

## 2.4 Product and separator decomposition

Independent systems factor exactly.

Systems sharing an exactly observed separator decompose conditionally when all left/right coupling is mediated by that separator.

The result was generalized from two components to arbitrary component families.

## 2.5 Interface signatures are sound but not generally minimal

The complete set of admissible actions at an interface state is a sufficient behavioral signature.

However, the kernel contains an exact three-state counterexample where:
- three complete signatures exist,
- only two safe messages are required,
- two optimal two-message encodings are incomparable,
- they have no safe common coarsening.

Therefore a unique canonical coarsest safe quotient need not exist in general.

## 2.6 Certified messages

A certified protocol consists of:

[
encode : World 	o Message
]

and

[
decode : Message 	o Action
]

such that the decoded action is available and admissible at every world assigned to that message.

Finite certified messages are exactly action covers, and on nonempty world spaces they are exactly safe information symbols.

## 2.7 Context can be kept, erased, or partially compressed

Three regimes are formally present:

1. indexed semantics: the decoder depends on the full separator context;
2. uniform semantics: the decoder is independent of context and the separator can be erased;
3. summary semantics: only a quotient / summary (q(k)) of the separator is retained.

There is an exact witness where full context is unnecessary but total erasure is impossible.

## 2.8 Context-message Pareto frontier

Minimizing context cardinality alone is degenerate because information can be moved into the message channel.

The correct local resource object is the joint region

[
mathcal B_Gamma
=
{(q,m):q	ext{ context symbols and }m	ext{ message symbols suffice}}.
]

This region is upward closed.

There is an exact witness with two incomparable Pareto minima:

[
(2,1)
quad	ext{and}quad
(1,2),
]

while ((1,1)) is impossible.

Thus the general interface invariant is naturally a Pareto frontier, not necessarily one scalar.

## 2.9 Distributed message passing

A leaf may retain information locally, certify its own action, and send a smaller upstream message.

An exact witness shows:
- one upstream symbol is sufficient in a distributed two-level protocol,
- a centralized protocol for the full global action needs exactly two symbols.

Thus information necessary locally need not be information necessary globally.

## 2.10 Recursive finite-tree certification

A single certified local rule can be reused at every node of an arbitrary finite binary tree.

By structural induction, every node of every finite tree is certified.

Each node sees only:
- its own local state,
- root messages emitted by its children.

It never needs the internal states of child subtrees.

## 2.11 Context congruence and replacement

A finite tree context with one hole (C[\cdot]) was formalized.

If two certified subtrees emit the same interface message, then for every finite ancestor context:

[
M(C[T_1])=M(C[T_2]),
]

the root action is identical, and whole-tree certification is equivalent.

This is a genuine substitutability theorem under arbitrary finite ancestor environments.

## 2.12 Total closure

The Total Closure theorem combines the recursive and contextual results:

A single certified local protocol induces:
1. certification of every node of every finite tree;
2. a future-sound interface abstraction for arbitrary finite ancestor contexts.

A future equivalence relation was defined and proved reflexive, symmetric, and transitive.

Equal certified interface messages imply future equivalence.

The context-message Pareto budgets were also linked back to concrete `GlobalSafe` observations.

This closes the current deterministic finite local-to-global kernel.

---

# 3. What is NOT proved

The following claims must not be attributed to the current Lean kernel:

- universal optimality for arbitrary physical systems;
- stochastic / Bayesian / belief-state closure;
- continuous-state or continuous-time closure;
- cyclic graph decomposition beyond the present tree / separator results;
- a unique canonical minimal quotient in general;
- a universal scalar “INSACERMO width”;
- a Lean-certified NP-hardness reduction from Set Cover;
- empirical causal claims from observational datasets;
- deployment safety or industrial certification;
- worldwide priority / proof that no equivalent theory exists anywhere in the literature.

These remain separate research questions.

---

# 4. Closest literature families and the exact distinction

The following are not competitors to be dismissed. They are the main neighboring theories that must be cited and compared.

## Viability theory / controlled invariance

Aubin’s viability theory studies whether trajectories can remain in state and control constraints.

Closest overlap:
- future feasibility under constraints,
- admissible controls,
- viability kernels.

INSACERMO-specific emphasis:
- what information may be merged/destroyed while preserving a common certifying action;
- resource frontiers involving information, communication, context, and capability.

Reference:
J.-P. Aubin, “A Survey of Viability Theory”, SIAM Journal on Control and Optimization.
DOI: 10.1137/0328044

## Assume-guarantee contracts and interface theories

Interface Automata and later contract theories support compatibility, refinement, substitution, and compositional verification.

Closest overlap:
- components,
- interfaces,
- contracts,
- local-to-global reasoning,
- replacement under contracts.

INSACERMO-specific emphasis:
- optimization of how much information/context/message must survive to preserve actionability;
- explicit destruction / compression question;
- common-action fiber criterion and Pareto resource frontiers.

References:
L. de Alfaro and T. A. Henzinger, “Interface Automata”, ESEC/FSE 2001.
DOI: 10.1145/503271.503226

L. de Alfaro and T. A. Henzinger, “Interface Theories for Component-Based Design”, EMSOFT 2001.

J. Cobleigh, D. Giannakopoulou, C. S. Pasareanu, “Learning Assumptions for Compositional Verification”, 2003.
DOI: 10.1007/3-540-36577-X_24

## Abstract interpretation

Abstract interpretation studies sound abstraction and order-theoretic approximation.

Closest overlap:
- forgetting details while preserving properties;
- abstraction/refinement orders;
- monotone fixpoint structures.

INSACERMO-specific emphasis:
- the abstraction criterion is explicitly future actionability under a declared contract;
- finite messages decode into actions;
- the resource frontier of abstraction itself is part of the object.

Reference:
P. Cousot and R. Cousot, “Abstract interpretation: a unified lattice model…”, POPL 1977.
DOI: 10.1145/512950.512973

## Bisimulation / abstraction-based controller synthesis

Symbolic control and bisimulation abstractions preserve controller-existence or temporal specifications.

This is one of the closest technical neighbors.

Closest overlap:
- quotienting states while preserving control objectives;
- correct-by-design controller synthesis;
- behavioral substitutability.

INSACERMO-specific emphasis:
- a common available action must certify an information fiber;
- no unique minimal quotient is assumed;
- information, context, communication, and capability are jointly optimized.

Representative references:
A. Girard, “Controller synthesis for safety and reachability via approximate bisimulation”, Automatica 48(5), 2012.
DOI: 10.1016/j.automatica.2012.02.037

J. Krook, R. Malik, S. Mohajerani, M. Fabian, “Robust stutter bisimulation for abstraction and controller synthesis with disturbance”, Automatica 160, 2024.
DOI: 10.1016/j.automatica.2023.111394

## Myhill–Nerode and tree automata congruence

Tree automata define contextual congruence by indistinguishability under all tree contexts.

Closest overlap:
- one-hole contexts;
- substitutability;
- finite-index congruence;
- bottom-up summaries.

INSACERMO-specific emphasis:
- equivalence is judged by future-safe actionability/certification rather than language acceptance;
- the kernel deliberately distinguishes sound message equivalence from globally unique minimal quotient claims.

Reference:
H. Comon et al., “Tree Automata Techniques and Applications”, Myhill–Nerode theorem for recognizable tree languages.

## Zero-error coding with side information

Witsenhausen showed that zero-error side-information coding can reduce to graph coloring.

Closest overlap:
- minimum alphabet size;
- exact, zero-error preservation;
- side information;
- graph/coloring structure.

INSACERMO-specific emphasis:
- the decoder returns an action certificate, not necessarily a reconstruction of the source;
- the contract specifies which future capabilities must remain possible.

Reference:
H. S. Witsenhausen, “The zero-error side information problem and chromatic numbers”, IEEE Transactions on Information Theory 22(5), 1976.
DOI: 10.1109/TIT.1976.1055607

## Coding for computing / functional compression

Orlitsky and Roche ask how much information must be communicated to compute a function rather than reconstruct all data.

This is another very close neighbor.

Closest overlap:
- task-relative compression;
- graph-based equivalence / colorings;
- side information.

INSACERMO-specific emphasis:
- the preserved object is not a predetermined output function but the existence of a certifying available action under a future contract;
- several incomparable safe compressions can exist.

Reference:
A. Orlitsky and J. R. Roche, “Coding for Computing”, IEEE Transactions on Information Theory 47(3), 2001.
DOI: 10.1109/18.915643

## Multi-resource rate regions

Gray–Wyner type formulations describe attainable multi-dimensional rate regions.

Closest overlap:
- Pareto/rate regions rather than one scalar;
- common and private information resources.

INSACERMO-specific emphasis:
- resource feasibility is defined by future actionability and safety certification rather than rate-distortion or exact source coding.

Reference:
R. M. Gray and A. D. Wyner, “Source Coding for a Simple Network”, Bell System Technical Journal 53(9), 1974.
DOI: 10.1002/j.1538-7305.1974.tb02812.x

## Junction trees / treewidth / dynamic programming

Junction-tree and tree-decomposition methods propagate local summaries across separators.

Closest overlap:
- tree-local messages;
- separator interfaces;
- local-to-global computation;
- complexity linked to interface state size.

INSACERMO-specific emphasis:
- message semantics is a future-action certificate;
- internal distinctions may be discarded when they cannot affect future certification;
- the relevant interface complexity is contract-relative and may be a Pareto frontier rather than raw separator cardinality.

## Blackwell comparison of experiments

Blackwell’s ordering compares information structures by the decision risks they permit.

This is conceptually important because it is explicitly decision-relative.

Closest overlap:
- information is valuable through decisions it enables;
- one information structure may dominate another across decision problems.

INSACERMO-specific emphasis:
- finite deterministic common-action certification;
- explicit future contracts;
- destruction, capability, communication, interface composition, and recursive tree certificates.

Reference:
D. Blackwell, “Equivalent Comparisons of Experiments”, Annals of Mathematical Statistics 24(2), 1953.
DOI: 10.1214/aoms/1177729032

---

# 5. Novelty position that is defensible today

A defensible statement is:

> Targeted literature review finds strong precedents for each major ingredient separately — viability, abstraction, contracts, compositional verification, contextual congruence, functional compression, side-information coding, rate regions, and tree message passing. We have not found an exact prior framework that combines them around one contract-relative question: determine which information/context/communication/capability resources may be removed while still guaranteeing a common admissible future action, and propagate those certified abstractions compositionally through finite interfaces and trees.

This is a positioning statement, not proof of worldwide novelty.

The novelty claim should therefore concern the architecture and the exact theorem chain, not the invention of its classical ingredients.

---

# 6. Empirical status

The formal kernel and empirical experiments remain separate proof levels.

The strongest current external industrial anchor is MetroAT:
- public TU Wien / Wiener Linien benchmark;
- 105 variables;
- approximately 25 million observations;
- official train/test split;
- real metro pneumatic system;
- one year of operation.

The existing INSACERMO holdout experiment froze rules on TRAIN and applied them to TEST without retuning. The short synthesis records nonzero actionability and a monotone restoration of future certifiability under information refinement on the tested family.

This is evidence that the information/actionability mechanism appears on real industrial data. It is not a proof of universality or causality.

Other existing empirical branches include ModeChoice, biological data, AI-learning preservation, and signal / temporal-regime experiments. These should be presented as separate validation families, not blended into the Lean proof.

---

# 7. The next empirical program

The goal is no longer to produce many unrelated demonstrations. It is to falsify the new kernel aggressively.

## Test A — exhaustive finite enumeration

For small numbers of worlds/actions/context symbols/messages:
- enumerate every admissibility relation;
- enumerate every encoding;
- compute exact safe-message minima;
- compute context-message Pareto fronts;
- compare exhaustive Python results against Lean theorems and witness predictions.

This is the highest-priority computational audit because it tests the mathematical engine directly.

## Test B — component-aware MetroAT holdout

Use the official TRAIN/TEST split.

Freeze on TRAIN:
- component grouping,
- contract thresholds,
- interface topology,
- admissibility rules,
- candidate summary/message construction.

Apply unchanged to TEST.

Measure:
- Pareto front stability;
- number of context symbols needed per interface;
- number of certified messages;
- local-vs-centralized communication;
- monotonicity violations;
- unsupported horizons.

## Test C — independent pneumatic replication

Repeat the same frozen protocol design on MetroPT or another independent pneumatic benchmark.

The objective is replication of the structural phenomenon, not parameter matching.

## Test D — adversarial nulls

For every real-data test:
- permute component identities;
- permute temporal blocks;
- destroy cross-component coupling;
- randomize the declared interface;
- use impossible or vacuous contracts;
- inject irrelevant sensors;
- deliberately mis-specify topology.

A useful INSACERMO engine must fail visibly on these controls.

## Test E — scaling

Measure exact / approximate frontier computation against:
- number of worlds;
- number of actions;
- number of components;
- separator size;
- message alphabet;
- tree depth.

This will separate mathematical existence from practical computability.

---

# 8. Engine architecture to implement now

The website/motor should no longer expose REPAIR as the conceptual center.

The stable engine should be layered:

## Layer 1 — CONTRACT

Input:
- worlds/states or rows;
- future requirements;
- available actions/capabilities;
- optional component topology.

Output:
- admissibility relation (Adm(x,a)).

## Layer 2 — ACTIONABILITY

Compute:
- ACT: current observation fiber already has a common available admissible action;
- PROBE: a permitted refinement can restore actionability;
- REPAIR: a permitted capability/action addition can restore actionability;
- REFUSE: the declared contract cannot be certified under allowed operations.

## Layer 3 — INFORMATION / COVER

Compute:
- safe fibers;
- obstructions;
- action covers;
- minimum certified-message count when tractable;
- certificates/witnesses.

## Layer 4 — INTERFACE

For componentized systems compute:
- context summaries;
- message alphabets;
- context-message feasibility region;
- Pareto-minimal interface budgets.

## Layer 5 — COMPOSITION

For tree-structured decompositions:
- bottom-up child certificates;
- local actions;
- parent messages;
- replacement-safe subtree summaries.

## Layer 6 — PLANNER

Optimize over allowed PROBE / REPAIR / communication choices.

The planner must consume the certified structures; it must not redefine them.

## Output discipline

Every result should expose:
- contract;
- proof level;
- action certificate;
- what was forgotten;
- what remained necessary;
- minimality status;
- whether the result is exact, exhaustive, heuristic, or empirical.

---

# 9. Public presentation

The public site should lead with the current question, not the older coherence-only language.

Recommended headline:

> Preserve the future. Prove what may be forgotten.

Recommended one-paragraph definition:

> INSACERMO is a contract-relative theory and engine for future actionability. It asks what information, distinctions, context, communication, or capabilities must remain so that a system can still guarantee the actions required by a declared future contract. In the finite deterministic kernel, safe compression, action covers, interface messages, Pareto resource frontiers, and recursive tree certificates are connected by machine-checked theorems. Empirical datasets are used separately to test whether the same structures appear in real systems.

Recommended warning:

> Machine-checked mathematical results do not automatically validate a physical model, a dataset interpretation, or a deployed decision. Formal, computational, and empirical evidence are reported separately.

---

# 10. Publication strategy

Do not split the deterministic finite core into many small papers.

A stronger strategy is one flagship theory paper:

## Candidate title

**INSACERMO: Future-Preserving Actionability, Certified Compression, and Compositional Interfaces**

Core structure:
1. problem and definitions;
2. fiber safety;
3. information-cover-obstruction equivalence;
4. resource frontiers and non-submodularity;
5. factorization and separators;
6. interface messages and context summaries;
7. Pareto context-message frontier;
8. recursive tree certificates;
9. contextual substitutability;
10. total closure;
11. relation to literature;
12. formal verification inventory.

A second paper can then be empirical / systems-oriented:

**INSACERMO Engine: Contract-Relative Actionability on Real Data**

with MetroAT as the central prospective holdout benchmark and independent replications.

---

# 11. Final scientific claim

The strongest concise claim currently justified is:

> INSACERMO provides a finite deterministic mathematical framework in which future requirements are represented as contracts, information loss is safe exactly when the resulting uncertainty still admits a common available action, minimal safe abstractions can be represented as action covers/certified messages and multi-resource Pareto frontiers, and these certificates compose recursively over finite tree-structured systems. Equal certified interface messages support substitution under arbitrary finite ancestor contexts.

This claim is strong enough.

It does not require saying that the theory is universal, unique, or unprecedented in every ingredient.

---

# 12. Final interpretation

The current deterministic finite kernel is mathematically closed enough to be treated as a coherent theory rather than an unfinished collection of ideas.

The remaining work is engineering and science around the kernel:

1. publish the theory cleanly;
2. perform a documented systematic literature review;
3. run exhaustive finite falsification tests;
4. extend the existing MetroAT holdout to interfaces and Pareto fronts;
5. replicate on independent systems;
6. implement the six-layer engine;
7. only then extend the formal kernel to stochastic/belief-state and cyclic settings.

The core should now be frozen while those layers are developed.

One sentence:

> **INSACERMO studies the boundary between what a system must still know, what it must still be able to do, and what it may safely destroy while keeping its declared future possible.**
