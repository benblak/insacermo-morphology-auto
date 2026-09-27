# INSACERMO — Rigorous Literature Positioning Audit
## 27 September 2026

This is a targeted literature comparison, not proof of worldwide novelty.

The goal is to identify the closest established frameworks and state precisely where INSACERMO overlaps and where its current theorem chain differs.

---

## 1. Symbolic control / feedback refinement relations

### Representative work
Gunther Reissig, Alexander Weber, Matthias Rungger,
**Feedback Refinement Relations for the Synthesis of Symbolic Controllers**,
IEEE Transactions on Automatic Control 62(4), 2017.
DOI: 10.1109/TAC.2016.2593947

Giordano Pola, Antoine Girard, Paulo Tabuada,
**Approximately bisimilar symbolic models for nonlinear control systems**,
Automatica 44(10), 2008.
DOI: 10.1016/j.automatica.2008.02.021

Giordano Pola, Paulo Tabuada,
**Symbolic Models for Nonlinear Control Systems: Alternating Approximate Bisimulations**,
SIAM Journal on Control and Optimization 48(2), 2009.
DOI: 10.1137/070698580

### Strong overlap
These frameworks explicitly construct quantized / symbolic abstractions of control systems and prove that controllers synthesized on the abstraction can enforce specifications on the concrete plant. Feedback refinement relations are particularly close because the abstract controller operates from quantized state information and the abstraction relation is designed to preserve implementable control.

### Difference in the current INSACERMO kernel
INSACERMO starts from a finite contract-relative admissibility relation and asks which states may be deliberately merged because **one common currently available action** certifies the declared future for the whole information fiber.

The current distinctive chain is not simply:
[
	ext{plant} 	o 	ext{symbolic abstraction} 	o 	ext{controller}.
]

It is:
[
	ext{contract}
	o
	ext{common-action fibers}
	o
	ext{cover / obstruction}
	o
	ext{certified messages}
	o
	ext{context-message Pareto frontier}
	o
	ext{recursive interface composition}.
]

Important caution:
Symbolic-control literature already contains canonical abstractions and correct-by-design controller refinement. INSACERMO should not claim invention of sound control abstraction.

---

## 2. Viability theory

### Representative work
Viability theory studies states from which there exists a control trajectory that continues to satisfy constraints.

Representative sources include work on viability kernels and robust viability maps.

### Strong overlap
Both viability and INSACERMO ask whether future admissibility can still be maintained by suitable actions.

### Difference
A viability kernel is primarily a set of states from which viable evolutions exist.

INSACERMO additionally places **information loss itself** inside the object:
after several concrete states have been merged by an observation, one common action must remain valid for all states in the resulting uncertainty fiber.

Thus INSACERMO's primitive is not only:
[
exists a 	ext{ for each state},
]
but:
[
exists a 	ext{ common to every state that the retained information can no longer distinguish}.
]

This is the source of the cover / message / obstruction structure.

---

## 3. Sufficient information in decentralized control

### Representative work
Hamidreza Tavafoghi, Yi Ouyang, Demosthenis Teneketzis,
**A Sufficient Information Approach to Decentralized Decision Making**,
CDC 2018.
DOI: 10.1109/CDC.2018.8619040

Ashutosh Nayyar, Aditya Mahajan, Demosthenis Teneketzis,
**Decentralized Stochastic Control with Partial History Sharing: A Common Information Approach**,
IEEE Transactions on Automatic Control 58(7), 2013.
DOI: 10.1109/TAC.2013.2239000

### Strong overlap
This is a very important neighbor.

The sufficient-information literature explicitly compresses private/common histories into information states that retain everything required for decentralized optimal decision making, and develops sequential decompositions.

### Difference
The current finite deterministic INSACERMO kernel is not an optimal stochastic-team formulation.

Its exact object is a **zero-error actionability certificate under a declared contract**:
a retained symbol is sufficient when one available action is guaranteed for every concrete world represented by that symbol.

INSACERMO also explicitly optimizes multiple resource dimensions:
- retained context,
- transmitted message,
- capability,
- information.

The closest future extension of INSACERMO toward belief states should cite this literature centrally.

---

## 4. Task-oriented communication / Action-Based State Aggregation

### Representative work
Arsham Mostaani et al.,
**Centralized Control of a Multi-Agent System Via Distributed and Bit-Budgeted Communications**,
IEEE WCNC 2023.

Arsham Mostaani et al.,
**Task-Effective Compression of Observations for the Centralized Control of a Multi-Agent System Over Bit-Budgeted Channels**.

### Strong overlap
This work compresses observations specifically according to their utility for downstream control decisions rather than according to reconstruction fidelity. Action-Based State Aggregation is conceptually especially close to INSACERMO's idea that states can be merged when the control consequences permit it.

### Difference
The cited task-effective work optimizes average stage reward / task performance under communication budgets.

INSACERMO's present kernel uses an exact contract-relative safety criterion:
[
	ext{a message is valid only if its decoded available action is admissible for every world assigned to it}.
]

Thus current INSACERMO is a zero-error / certificate-oriented theory, not an expected-return compression method.

This is one of the most important literatures to cite when presenting the engine.

---

## 5. Zero-error coding with side information

### Representative work
H. S. Witsenhausen,
**The zero-error side information problem and chromatic numbers**,
IEEE Transactions on Information Theory 22(5), 1976.
DOI: 10.1109/TIT.1976.1055607

Recent side-information design work continues to formulate zero-error coding through characteristic / confusion graphs and graph colorings.

### Strong overlap
The combinatorial similarity is deep:
- indistinguishable states;
- forbidden merges;
- graph / hypergraph colorings;
- minimum alphabets;
- side information changing required communication.

This is the closest classical analogue to the obstruction-coloring side of INSACERMO.

### Difference
The zero-error decoder is typically required to reconstruct data or compute a prescribed function exactly.

INSACERMO instead requires the decoder to return **an available action that guarantees the future contract**. Several concrete worlds may remain unreconstructed forever if they share a certifying action.

---

## 6. Coding for computing / functional compression

### Representative work
Alon Orlitsky, James R. Roche,
**Coding for Computing**,
IEEE Transactions on Information Theory 47(3), 2001.
DOI: 10.1109/18.915643

### Strong overlap
Functional compression asks how much information must be sent when the decoder only needs a function of the source, not the source itself.

This is structurally close to:
“do not preserve the world; preserve only what is needed for the future task.”

### Difference
INSACERMO does not begin with one fixed output function (f(x)).

The admissible action set may contain several acceptable actions, and safety of a fiber requires only a **nonempty common intersection** of admissible available actions.

This produces:
- nonunique optimal safe partitions;
- incomparable optimal encodings;
- no guaranteed unique coarsest quotient.

That distinction should be made explicit in publications.

---

## 7. Interface automata / compositional contracts

### Representative work
Luca de Alfaro, Thomas A. Henzinger,
**Interface Automata**, ESEC/FSE 2001.
DOI: 10.1145/503271.503226

Later interface theories support composition, refinement, hiding, quotient, and substitutivity.

### Strong overlap
Very close concepts:
- component interfaces;
- compatibility;
- refinement;
- composition;
- hiding;
- substitutivity.

### Difference
INSACERMO's interface object is explicitly optimized according to what future-action information must cross it.

The theory asks:
[
	ext{how much context/message/capability must remain}
]
rather than only whether two component specifications compose or refine.

---

## 8. Tree automata and Myhill–Nerode contextual congruence

### Representative source
Comon et al.,
**Tree Automata Techniques and Applications**.

For recognizable tree languages, contextual equivalence is defined using all one-hole tree contexts, and equal automaton states induce a congruence under context substitution.

### Strong overlap
This is the closest formal analogue to INSACERMO's:
[
M(T_1)=M(T_2)
Rightarrow
M(C[T_1])=M(C[T_2]).
]

### Difference
Classical tree-automata congruence preserves language recognition.

INSACERMO's contextual relation preserves:
- root action under the certified protocol;
- whole-tree certification under the declared actionability contract.

This is an application-specific congruence, not a new invention of contextual equivalence.

---

## 9. Gray-Wyner and multi-resource rate regions

### Representative work
Robert M. Gray, Aaron D. Wyner,
**Source Coding for a Simple Network**,
Bell System Technical Journal 53(9), 1974.
DOI: 10.1002/j.1538-7305.1974.tb02812.x

### Strong overlap
A multi-resource information problem should generally be represented by an attainable rate region, not by a single arbitrary scalar.

This is directly analogous to the INSACERMO context-message feasibility region:
[
mathcal B_Gamma(q,m).
]

### Difference
INSACERMO's feasible region is induced by zero-error future-action certificates, not source reconstruction rates.

The Pareto geometry is therefore a shared mathematical pattern, not itself a novelty claim.

---

# 10. Positioning conclusion

The strongest defensible novelty statement after this audit is:

> Established literature already contains strong theories for viability, correct-by-design abstraction, sufficient information, task-oriented communication, zero-error side-information coding, functional compression, component interfaces, contextual congruence, and multidimensional information-rate regions. The current INSACERMO contribution is the particular integration of these ideas around a contract-relative common-action criterion: identify exactly which distinctions, context, communication and capabilities may be removed while a common available future-certifying action remains, characterize finite minima through covers/messages/obstructions and Pareto frontiers, and propagate certified abstractions compositionally through finite tree interfaces.

This is a **targeted-review positioning statement**, not a proof that no exact equivalent exists anywhere.

# 11. Strongest neighboring challenge

The most important comparison for the flagship paper should not be a superficial list.

The paper should directly compare the INSACERMO finite kernel against at least:
1. Feedback Refinement Relations / symbolic control;
2. sufficient-information decentralized control;
3. Action-Based State Aggregation / task-oriented communication;
4. Witsenhausen / Orlitsky-Roche zero-error functional compression;
5. interface theories;
6. tree-automata contextual congruence.

For each, the paper should state:
- what the classical theory preserves;
- what its abstraction object is;
- whether exact reconstruction is required;
- whether actions can be set-valued;
- whether information/capability/context/communication are optimization resources;
- whether composition across interfaces is formalized;
- whether a unique canonical quotient exists.

That comparison is the correct test of INSACERMO's scientific identity.
