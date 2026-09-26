# INSACERMO — Architecture-Level Literature Positioning

**Date:** 2026-09-26  
**Status:** literature positioning after kernel verification of `CertificateDomain`  
**Purpose:** distinguish classical ingredients from the potentially distinctive INSACERMO architecture.

## 1. What INSACERMO is not

INSACERMO should not claim to have invented:

- viability kernels or controlled invariance;
- recursive feasibility in MPC;
- assume-guarantee contracts;
- Farkas certificates, IIS/MUS, Helly-type obstruction size, or conflict hypergraphs;
- signed-graph balance or unbalanced girth;
- Petri/resource-capacity reasoning;
- empowerment, relative reachability, attainable-utility preservation, or the general idea of preserving future options;
- reject/abstain decisions;
- value of information, active sensing, sequential testing, POMDP belief states, Bayesian filtering, or Bellman recursion;
- plan repair or resilience/recovery;
- formal runtime shields.

All of those have substantial prior literatures.

The scientific question is therefore not whether INSACERMO contains known mathematics. It does.

The relevant question is whether the **organization of these ingredients around one semantic object — a contract over future capabilities — together with the interfaces between layers, the certificate-derived audit horizon, and the action/repair/planning semantics, already exists as a single theory.**

## 2. The architecture being positioned

The current INSACERMO architecture is:

[
oxed{
	ext{FUTURE / REQUIREMENT FAMILY}
	o
	ext{CONTRACT}
	o
	ext{PRESERVATION}
	o
	ext{ACTIONABILITY}
	o
	ext{DOMAIN CERTIFICATES}
	o
	ext{PRE-AUDIT DEPTH}
	o
	ext{ACT / PROBE / REFUSE}
	o
	ext{REPAIR}
	o
	ext{PLANNER}
}
]

with extensions toward:

[
oxed{
	ext{UNKNOWN FUTURE}
	o
	ext{SENSING}
	o
	ext{BELIEF STATE}
	o
	ext{BAYES FILTER}
	o
	ext{BELLMAN}
	o
	ext{LEARNING}
}
]

The central semantic question is:

> What may be transformed, forgotten, consumed, or destroyed now while retaining the future capabilities that a declared contract may later require?

This differs from asking only whether the present state is safe, whether the current task is feasible, or whether a fixed reward is optimized.

## 3. Closest literature family A — viability theory and controlled invariance

Viability theory asks whether a dynamical system can remain inside an admissible set under available controls. Controlled-invariant sets and viability kernels therefore represent a major ancestor of INSACERMO's preservation layer.

Modern MPC work similarly emphasizes **recursive feasibility**: after taking the current action, the next optimization problem must remain feasible. K-step invariant sets and robust terminal sets are explicit mechanisms for preserving future feasibility.

Representative sources:

- Aubin's viability-theory tradition; see modern summary in:  
  https://www.sciencedirect.com/science/article/abs/pii/S0303264726002121
- K-step control-invariant NMPC and recursive feasibility:  
  https://www.sciencedirect.com/science/article/pii/S0947358024001006
- Robust preview MPC with a feasibility governor:  
  https://www.sciencedirect.com/science/article/pii/S0167691124000239

### Overlap

Very strong overlap with:

[
	ext{current action}
	o
	ext{preservation of future feasibility}.
]

### Difference currently visible

Classical viability/MPC normally fixes a state constraint, target, admissible set, or receding-horizon optimization problem.

INSACERMO's contract layer is intended to represent a **family of future queries/tasks/capabilities** whose distinctions may be preserved, destroyed, probed, repaired, or traded. The later certificate and obstruction layers reason about *why* a collection of future requirements becomes jointly impossible and how deep such incompatibilities can be.

Thus viability is a strong ancestor and potential special case / backend, not an obvious duplicate of the whole stack.

## 4. Closest literature family B — future-option preservation

This is the most important prior art for INSACERMO's motivating intuition.

### Relative reachability and attainable utility preservation

Krakovna et al. developed side-effect penalties based on changes in reachability. Turner and collaborators developed attainable-utility preservation. These methods explicitly attempt to avoid destroying options.

Representative source:

- Krakovna et al., "Penalizing side effects using stepwise relative reachability"  
  https://arxiv.org/abs/1806.01186
- Attainable Utility Preservation conceptual work:  
  https://turntrout.com/attainable-utility-preservation-concepts

### Future tasks

The closest direct statement to the INSACERMO intuition is:

Victoria Krakovna, Laurent Orseau, Richard Ngo, Miljan Martic, Shane Legg,  
**"Avoiding Side Effects By Considering Future Tasks," NeurIPS 2020.**

https://proceedings.neurips.cc/paper/2020/hash/dc1913d422398c25c5f0b81cab94cc87-Abstract.html

Their auxiliary objective rewards an agent for retaining the ability to complete possible future tasks. This explicitly formalizes preservation of future options and addresses interference incentives via a baseline policy.

Therefore INSACERMO must **not** claim that the basic idea "preserve ability to perform unknown future tasks" is new.

### Difference currently visible

The NeurIPS future-task approach is primarily an auxiliary-reward construction for avoiding side effects in an MDP.

INSACERMO instead develops a contract-level semantics and then asks additional questions that are not central to that work:

- which finite sets of future requirements are jointly feasible;
- what certificate proves infeasibility;
- what is the maximal/minimal obstruction depth;
- how far must auditing go before it is complete;
- whether one should ACT, PROBE, or REFUSE;
- what repair restores a lost capability;
- how these operations compose over time;
- and how to expose domain-specific mathematics through a common certificate interface.

This is a candidate difference of **architecture and theorem interfaces**, not of the future-option intuition itself.

## 5. Closest literature family C — anticipatory planning for long-lived agents

Dhakal, Talukder, and Stein explicitly study agents that receive tasks one at a time in a persistent environment and may damage the cost of unknown future tasks.

Key source:

- Roshan Dhakal, Md Ridwan Hossain Talukder, Gregory J. Stein,  
  **"Anticipatory Planning: Improving Long-Lived Planning by Estimating Expected Cost of Future Tasks," ICRA 2023.**  
  https://arxiv.org/abs/2305.04692

Follow-up:

- **"Anticipatory Task and Motion Planning"**  
  https://arxiv.org/abs/2407.13694

These works are conceptually close to INSACERMO's planner layer. They estimate expected future task cost and use it to choose current plans that leave the environment in better states for later tasks.

### Difference currently visible

Anticipatory planning estimates expected future cost, often with learned models, and selects better plans.

INSACERMO's present formal core instead emphasizes **capability preservation and impossibility structure**:

[
	ext{future contract}
	o
	ext{minimal obstruction}
	o
	ext{certificate}
	o
	ext{audit depth}
	o
	ext{decision / repair}.
]

These are complementary viewpoints:

[
	ext{expected future cost}
quad	ext{vs}quad
	ext{certified future feasibility / destruction}.
]

A future research direction is to connect them explicitly: expected anticipatory cost could operate *inside* the feasible region certified by INSACERMO.

## 6. Closest literature family D — contract-based design

Assume-guarantee contracts are a mature formal-methods framework. They support compositional specification, refinement, compatibility, consistency, and implementation.

Representative sources:

- Nuzzo, Iannopollo, Tripakis, Sangiovanni-Vincentelli, relational interfaces / assume-guarantee contracts:  
  https://www2.eecs.berkeley.edu/Pubs/TechRpts/2014/EECS-2014-21.html
- Assume-guarantee contracts for continuous-time systems:  
  https://www.sciencedirect.com/science/article/pii/S0005109821004337
- Contract-based cyber-physical-system design:  
  https://escholarship.org/uc/item/5hk5w3bg

### Overlap

The word "contract" in INSACERMO must not be presented as itself novel.

### Difference currently visible

Contract-based design usually asks whether components or implementations satisfy assumptions and guarantees and how contracts compose/refine.

INSACERMO uses a future contract as the semantic source for a different downstream chain:

[
	ext{contract}
	o
	ext{what information/capability must survive}
	o
	ext{actionability}
	o
	ext{obstruction certificates}
	o
	ext{repair/planning}.
]

The candidate novelty is not contracts, but their role as the root object of a future-preservation engine.

## 7. Closest literature family E — shields and safe RL

Shield synthesis enforces safety properties at runtime and minimizes deviation from a nominal controller.

Representative source:

- Bloem/Könighofer et al., **Shield Synthesis**:  
  https://link.springer.com/article/10.1007/s10703-017-0276-9
- Safe RL via shielding:  
  https://arxiv.org/abs/1708.08611
- Adaptive shielding with Hamilton-Jacobi reachability:  
  https://proceedings.mlr.press/v283/lu25a.html

### Overlap

Strong overlap with the ACT/REFUSE boundary: an action may be prevented because it violates a specification.

### Difference currently visible

A shield normally protects declared safety properties. INSACERMO attempts to reason not only about current safety but about the **remaining future capability set**, including incompatibilities between future requirements, information acquisition, and repair after capability loss.

Thus a shield could plausibly be one executable realization of the INSACERMO decision layer.

## 8. Closest literature family F — information and PROBE

The PROBE branch is not novel by itself.

Classical and modern ancestors include:

- Blackwell comparison of experiments — information source A dominates B if it can do at least as well for every decision problem:  
  https://doi.org/10.1214/aoms/1177729032
- value of information;
- sequential hypothesis testing;
- active feature acquisition;
- active sensing;
- POMDP information-gathering actions.

Representative sources:

- Active feature-value acquisition:  
  https://research.ibm.com/publications/active-feature-value-acquisition
- Survey of information gathering in decision-theoretic planning:  
  https://doi.org/10.1145/3583068
- POMDP value of information for monitoring/inspection:  
  https://www.sciencedirect.com/science/article/pii/S0951832016300771

### Overlap

The choice between acting now and acquiring more information is deeply classical.

### Difference currently visible

INSACERMO's PROBE semantics is meant to be generated relative to a **future-preservation contract**, rather than only classification confidence, expected reward, or state estimation.

The interesting question is therefore whether information is valuable because it resolves uncertainty about which future distinctions/actions may safely be collapsed.

## 9. Closest literature family G — reject / abstain / refuse

Reject-option classification goes back at least to Chow's theory. Selective prediction and abstention are mature topics.

Representative discussion:

https://academic.oup.com/bioinformatics/article/24/17/1889/263502

Sequential hypothesis testing also has the familiar three-way structure:

[
	ext{decide }H_0,quad
	ext{decide }H_1,quad
	ext{continue observing}.
]

Therefore the existence of ACT/PROBE/REFUSE-like decision partitions is not itself novel.

The potentially distinctive part is how INSACERMO **derives** its decision partition from contract feasibility geometry and future-preservation semantics.

## 10. Closest literature family H — repair and resilience

Repair is a broad field:

- CSP min-conflicts;
- IIS diagnosis and infeasibility resolution;
- planning-domain repair;
- plan repair after execution failure;
- resilient control and infrastructure restoration.

Representative sources:

- Minton et al., min-conflicts repair:  
  https://www.sciencedirect.com/science/article/abs/pii/000437029290007K
- infeasibility diagnosis / resolution:  
  https://www.sciencedirect.com/science/article/abs/pii/S0305054806001924
- automated goal-conflict resolution:  
  https://link.springer.com/chapter/10.1007/978-3-031-30826-0_1
- autonomous spacecraft plan repair:  
  https://www.mdpi.com/2226-4310/9/1/40

Resilience engineering also explicitly studies preserving/adapting/recovering functionality under unforeseen disturbances.

Representative sources:

- Woods, four concepts of resilience:  
  https://doi.org/10.1016/j.ress.2015.03.018
- engineering resilience under unknown future events:  
  https://doi.org/10.1002/sys.21491

### Difference currently visible

INSACERMO's repair question is contract-relative:

[
	ext{what minimal modification restores the specific future capability that was destroyed?}
]

The proposed unification with obstruction certificates and actionability is more specific than generic resilience or plan repair.

## 11. Closest literature family I — empowerment and option capacity

Empowerment measures the information-theoretic capacity of an agent's action channel and has long been interpreted as a measure of control / number of optional future states.

Representative source:

- Klyubin, Polani, Nehaniv, 2005:  
  https://researchprofiles.herts.ac.uk/en/publications/empowerment-a-universal-agent-centric-measure-of-control/

This is a major ancestor of any claim about "amount of future possibility."

### Difference currently visible

Empowerment is task-agnostic and values controllability itself.

INSACERMO is contract-relative: two future states may be equivalent if no admissible future requirement distinguishes them. Thus INSACERMO is interested not necessarily in preserving *all* state control, but in preserving exactly the distinctions/capabilities required by a declared or uncertain contract.

This is an important conceptual distinction.

## 12. Closest literature family J — belief-state planning and Bellman recursion

POMDP belief states, Bayesian filtering, dynamic programming, and Bellman equations are classical.

INSACERMO must not claim novelty for extending a deterministic decision process to beliefs and Bellman recursion.

The candidate contribution is instead the **state variable being propagated**: contract-relative future capability / destruction / recoverability information.

In other words, the mathematics of belief planning is inherited; the proposed object inserted into it may be INSACERMO-specific.

## 13. Where the architecture currently appears distinctive

After this review, the strongest candidate contribution is not any node in the stack.

It is the **sequence of typed interfaces between nodes**.

The architecture can be summarized as:

[
oxed{
egin{array}{c}
	ext{Future requirements define a contract}\
downarrow\
	ext{The contract defines which distinctions/capabilities matter}\
downarrow\
	ext{Transformations are judged by what contracted futures they destroy}\
downarrow\
	ext{Domain-specific certificates explain joint future infeasibility}\
downarrow\
	ext{Certificate geometry bounds how deep an audit must search}\
downarrow\
	ext{Actionability maps the result to ACT / PROBE / REFUSE}\
downarrow\
	ext{Repair restores lost contracted capability}\
downarrow\
	ext{Planning composes these choices over time}\
downarrow\
	ext{Unknown futures are lifted to robust / probabilistic / belief semantics}
end{array}
}
]

The literature contains strong ancestors for every individual arrow's endpoints.

What has **not** been identified in this review is a prior framework that instantiates this complete chain with:

1. a future-contract semantic root;
2. contract-relative preservation rather than generic state preservation;
3. arbitrary domain-specific infeasibility certificates behind a common formal interface;
4. certificate-local pre-audit depth separated from true obstruction depth;
5. a theorem transferring certificate depth to actual obstruction depth;
6. cross-certificate closure for exact depth;
7. ACT / PROBE / REFUSE semantics driven by the same contract;
8. repair of destroyed future capability;
9. sequential planning over those objects;
10. formal verification of core interface theorems.

This is an **absence-of-identified-prior-art statement**, not a proof that no such framework exists.

## 14. The closest direct conceptual threat

The closest conceptual threat is not Helly, Farkas, or viability in isolation.

It is the combination of:

- **Krakovna et al. 2020 future-task preservation**, and
- **Dhakal et al. 2023+ anticipatory planning**.

Those works already say, in substance:

> present actions should be evaluated partly by what they leave possible or costly for tasks not yet assigned.

That overlaps directly with INSACERMO's motivating intuition.

Therefore INSACERMO's scientific claim must begin *after* that shared intuition.

The strongest current boundary is:

> INSACERMO turns future preservation from an auxiliary reward / expected future-cost heuristic into a contract-oriented structural theory of capability equivalence, infeasibility certificates, obstruction depth, decision semantics, repair, and planning.

This statement should itself be stress-tested further.

## 15. Novelty should be claimed at the seams, not the bricks

The emerging positioning is:

[
oxed{	ext{classical bricks} + 	ext{newly formalized seams}}
]

Potentially distinctive seams include:

### Seam A — CONTRACT → PRESERVATION

The contract determines exactly which distinctions are allowed to be forgotten or collapsed.

### Seam B — PRESERVATION → ACTIONABILITY

Preservation is not only a static property; it determines which actions remain admissible.

### Seam C — ACTIONABILITY → CERTIFICATE DOMAIN

Infeasibility is delegated to domain mathematics without changing the generic semantics.

### Seam D — CERTIFICATE → PRE-AUDIT DEPTH

The certificate family determines the audit horizon before brute-force bundle enumeration.

### Seam E — OBSTRUCTION → REPAIR

The same obstruction that explains impossibility defines what must be restored.

### Seam F — REPAIR → PLANNER

Repair and preservation are propagated through time rather than solved as isolated failures.

### Seam G — KNOWN FUTURE → UNKNOWN FUTURE

The same contract object is lifted from exact requirements to families/distributions/beliefs instead of replacing the framework.

These seams are the most promising targets for theorem-level novelty.

## 16. Current defensible positioning sentence

A conservative but strong formulation is:

> INSACERMO is a contract-oriented framework for reasoning about how present transformations alter future capability. It integrates contract-relative preservation, domain-specific infeasibility certificates, certificate-derived audit depth, action/probe/refuse semantics, capability repair, and sequential planning. Its individual mathematical ingredients have substantial precedents, but this review has not identified a prior framework exposing the same end-to-end architecture or the same certificate-to-audit-depth interface.

## 17. What should be proved next

The next research step should not be another benchmark.

It should be **bridge theorems to the closest literatures**, so that INSACERMO's boundary becomes mathematical rather than rhetorical.

Priority bridges:

1. **Future-task bridge**  
   Show how a deterministic future-task family induces an INSACERMO contract, and characterize when preserving all contracted tasks coincides with relative reachability / future-task preservation.

2. **Viability bridge**  
   For state-safety contracts, show when INSACERMO actionability reduces to a viability-kernel or controlled-invariance condition.

3. **Helly/IIS bridge**  
   Show when minimal-failure depth becomes a Helly number / conflict-hypergraph rank and identify conditions under which certificate pre-audit depth is strictly different.

4. **Blackwell bridge**  
   Characterize when one probe dominates another for every future contract, connecting INSACERMO probe ordering to Blackwell informativeness.

5. **Anticipatory-planning bridge**  
   Separate hard future-capability preservation from soft expected future-cost optimization. A natural composition is:
   [
   	ext{INSACERMO feasible envelope}
   +
   	ext{anticipatory cost optimization inside the envelope}.
   ]

6. **Repair duality bridge**  
   Relate minimal capability restoration to hitting sets / IIS repair / goal-conflict resolution.

If these bridges are proved, the literature positioning becomes much stronger: INSACERMO would not merely cite neighboring theories; it would provide explicit translations showing which are special cases, which are incomparable, and which layers are genuinely additional.

## 18. Bottom line

The review changes the claim in a healthy way.

The strongest statement is not:

[
	ext{"nobody thought about future options before."}
]

That is false.

Nor is it:

[
	ext{"INSACERMO invented contracts, viability, certificates, probes, repair, or Bellman."}
]

Also false.

The emerging claim is:

[
oxed{
	ext{INSACERMO may be distinctive because it makes future capability the common semantic currency}
}
]

and then connects, in one formally typed architecture:

[
oxed{
	ext{specification}
	o
	ext{preservation}
	o
	ext{infeasibility explanation}
	o
	ext{audit depth}
	o
	ext{decision}
	o
	ext{repair}
	o
	ext{planning}.
}
]

That is the claim that now deserves theorem-level stress testing.
