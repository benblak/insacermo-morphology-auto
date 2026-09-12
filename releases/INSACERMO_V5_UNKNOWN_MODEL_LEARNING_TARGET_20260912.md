# INSACERMO V5 — Unknown-Model Bayesian Learning Target

Date frozen: 2026-09-12

## Question

Does the existing INSACERMO architecture survive when the environment model is not known exactly in advance and the agent must learn which model is plausible from action-dependent evidence?

The frozen architecture remains:

`Contract -> Actionability / Obstructions -> Planner`

No new runtime layer is introduced unless learning creates an irreducible operational function that cannot be represented as information-state evolution plus the existing planner.

## Frozen first learning model

This first target isolates **finite Bayesian model uncertainty**.

- finite model-hypothesis type `Theta`;
- finite evidence/outcome type `O`;
- finite action / experiment type `A`;
- prior `b : FiniteLaw Theta`;
- known likelihood family `L : A -> Theta -> FiniteLaw O`;
- the latent model parameter is static across updates;
- choosing an action/experiment changes the evidence law and therefore can change the posterior over models.

The latent model itself is unknown, but the finite candidate family and its likelihoods are part of the declared contract.

## Frozen formal targets

1. Construct a finite exact Dirac law and the static latent-model transition kernel.
2. Prove that prediction under the static model kernel preserves the prior exactly.
3. Define exact model evidence and the positive-evidence posterior using the already verified finite Bayes filter.
4. Prove the closed posterior-mass formula

   `posterior(theta) = prior(theta) * likelihood(a,theta,o) / evidence(a,o)`.

5. Define posterior Bayes-risk action admissibility by expected model-relative loss:

   `ModelRiskGood(b,a) <-> sum_theta b(theta) * loss(theta,a) <= threshold`.

6. Instantiate the unchanged `SafeRep` kernel on posterior/model-belief states and prove capability, information-refinement, and threshold monotonicity.
7. Prove exact history-to-model-posterior sufficiency when the history contract is defined through the generated posterior.
8. For a finite indexed family of reachable/postulated model beliefs, recover the exact minimal-obstruction hypergraph characterization.
9. Connect a declared candidate graph of information/capability states to the existing sequential planner, so posterior-learning situations can still route to ACT / REFUSE / optimal PROBE-REPAIR-PROBE+REPAIR.

## Interpretation target

The intended reduction is:

`unknown finite model -> posterior over model hypotheses -> admissibility contract -> SafeRep -> planner`.

Learning actions are information-changing capabilities: an action can be valuable because it changes the posterior, not only because it changes the physical state.

A key conceptual boundary to test is whether INSACERMO needs the true model to be identified. The expected answer in this finite target is no: it only needs enough posterior resolution that the current information fiber has a common admissible available action.

## Guardrails

This target does NOT yet prove:

- arbitrary unknown transition or observation kernels outside a declared finite hypothesis class;
- nonparametric learning;
- continuous parameter spaces;
- posterior consistency / asymptotic identification;
- regret bounds;
- PAC or sample-complexity bounds;
- exploration optimality;
- full Bayes-adaptive MDP/POMDP equivalence;
- model misspecification robustness;
- historical novelty.

A later target may combine model uncertainty with hidden physical state by augmenting the latent state to `(Theta, S)` and may then study Bayes-adaptive Bellman planning. That is not silently assumed here.

## Falsification discipline

Do not redefine `SafeRep` or add an ad hoc learning layer merely to make this target pass. If Bayesian model uncertainty cannot be represented as an information state feeding the existing actionability kernel, record that as an architectural failure.
