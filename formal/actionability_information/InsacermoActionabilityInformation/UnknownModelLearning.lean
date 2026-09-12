import InsacermoActionabilityInformation.FiniteBayesFilter
import InsacermoActionabilityInformation.SequentialPlanner

namespace InsacermoActionabilityInformation

/-- Exact Dirac law on a finite type. -/
def diracLaw {X : Type*} [Fintype X] [DecidableEq X] (x0 : X) : FiniteLaw X where
  mass := fun x => if x = x0 then 1 else 0
  nonneg := by
    intro x
    split_ifs <;> norm_num
  total_one := by
    classical
    simp

/-- Static latent-model transition: the unknown model parameter does not change. -/
def staticModelKernel {Theta A : Type*} [Fintype Theta] [DecidableEq Theta]
    (_a : A) (theta : Theta) : FiniteLaw Theta :=
  diracLaw theta

/-- Prediction under a static latent model preserves the prior exactly. -/
theorem predictMass_staticModel_eq_prior
    {Theta A : Type*} [Fintype Theta] [DecidableEq Theta]
    (b : FiniteLaw Theta) (a : A) (theta' : Theta) :
    predictMass (staticModelKernel (Theta := Theta) (A := A)) b a theta' = b.mass theta' := by
  classical
  unfold predictMass staticModelKernel diracLaw
  simp

/-- Action-dependent likelihood of evidence under each latent model hypothesis. -/
abbrev ModelLikelihood (Theta A O : Type*) [Fintype O] :=
  A → Theta → FiniteLaw O

/-- Exact predictive evidence probability under model uncertainty. -/
abbrev modelEvidence
    {Theta A O : Type*} [Fintype Theta] [DecidableEq Theta] [Fintype O]
    (L : ModelLikelihood Theta A O)
    (b : FiniteLaw Theta) (a : A) (o : O) : ℚ :=
  evidence (staticModelKernel (Theta := Theta) (A := A)) L b a o

/-- Positive-evidence posterior over latent model hypotheses. -/
def modelPosterior
    {Theta A O : Type*} [Fintype Theta] [DecidableEq Theta] [Fintype O]
    (L : ModelLikelihood Theta A O)
    (b : FiniteLaw Theta) (a : A) (o : O)
    (hpos : 0 < modelEvidence L b a o) : FiniteLaw Theta :=
  bayesUpdate (staticModelKernel (Theta := Theta) (A := A)) L b a o hpos

/-- Closed-form posterior mass for a static latent model. -/
theorem modelPosterior_mass_formula
    {Theta A O : Type*} [Fintype Theta] [DecidableEq Theta] [Fintype O]
    (L : ModelLikelihood Theta A O)
    (b : FiniteLaw Theta) (a : A) (o : O)
    (hpos : 0 < modelEvidence L b a o) (theta : Theta) :
    (modelPosterior L b a o hpos).mass theta =
      b.mass theta * (L a theta).mass o / modelEvidence L b a o := by
  classical
  unfold modelPosterior bayesUpdate posteriorWeight
  change predictMass (staticModelKernel (Theta := Theta) (A := A)) b a theta *
      (L a theta).mass o / modelEvidence L b a o =
    b.mass theta * (L a theta).mass o / modelEvidence L b a o
  rw [predictMass_staticModel_eq_prior]

/-- Posterior expected loss of taking action `a` under model belief `b`. -/
def ModelExpectedLoss
    {Theta A : Type*} [Fintype Theta]
    (loss : Theta → A → ℚ) (b : FiniteLaw Theta) (a : A) : ℚ :=
  Finset.univ.sum (fun theta => b.mass theta * loss theta a)

/-- Model-relative Bayes-risk admissibility. -/
def ModelRiskGood
    {Theta A : Type*} [Fintype Theta]
    (loss : Theta → A → ℚ) (threshold : ℚ)
    (b : FiniteLaw Theta) (a : A) : Prop :=
  ModelExpectedLoss loss b a ≤ threshold

/-- Safe representation over posterior/model-belief states. -/
def ModelRiskSafeRep
    {Theta A Y : Type*} [Fintype Theta]
    (loss : Theta → A → ℚ) (threshold : ℚ)
    (B : Set (FiniteLaw Theta)) (C : Set A)
    (h : FiniteLaw Theta → Y) : Prop :=
  SafeRep (ModelRiskGood loss threshold) B C h

/-- Capability expansion cannot destroy model-risk actionability. -/
theorem modelRiskSafeRep_capability_mono
    {Theta A Y : Type*} [Fintype Theta]
    {loss : Theta → A → ℚ} {threshold : ℚ}
    {B : Set (FiniteLaw Theta)} {C C' : Set A}
    {h : FiniteLaw Theta → Y}
    (hsafe : ModelRiskSafeRep loss threshold B C h)
    (hcap : C ⊆ C') :
    ModelRiskSafeRep loss threshold B C' h := by
  exact safeRep_capability_mono hsafe hcap

/-- Finer external representation cannot destroy model-risk actionability. -/
theorem modelRiskSafeRep_information_mono
    {Theta A YFine YCoarse : Type*} [Fintype Theta]
    {loss : Theta → A → ℚ} {threshold : ℚ}
    {B : Set (FiniteLaw Theta)} {C : Set A}
    {fine : FiniteLaw Theta → YFine}
    {coarse : FiniteLaw Theta → YCoarse}
    (hsafe : ModelRiskSafeRep loss threshold B C coarse)
    (href : Refines fine coarse) :
    ModelRiskSafeRep loss threshold B C fine := by
  exact safeRep_information_mono hsafe href

/-- Relaxing the posterior expected-loss threshold cannot destroy safety. -/
theorem modelRiskSafeRep_threshold_mono
    {Theta A Y : Type*} [Fintype Theta]
    {loss : Theta → A → ℚ} {theta theta' : ℚ}
    {B : Set (FiniteLaw Theta)} {C : Set A}
    {h : FiniteLaw Theta → Y}
    (hsafe : ModelRiskSafeRep loss theta B C h)
    (hth : theta ≤ theta') :
    ModelRiskSafeRep loss theta' B C h := by
  intro y hy
  rcases hsafe y hy with ⟨a, haC, hgood⟩
  refine ⟨a, haC, ?_⟩
  intro b hbB hby
  exact le_trans (hgood b hbB hby) hth

/-- A history contract defined solely through the generated model posterior is
exactly belief-sufficient for the model-risk contract. -/
theorem modelPosterior_history_sufficient
    {History Theta A : Type*} [Fintype Theta]
    (beta : History → FiniteLaw Theta)
    (loss : Theta → A → ℚ) (threshold : ℚ) :
    BeliefSufficient beta
      (HistoryGoodViaBelief beta (ModelRiskGood loss threshold))
      (ModelRiskGood loss threshold) := by
  exact historyGoodViaBelief_sufficient beta (ModelRiskGood loss threshold)

/-- Exact history/posterior SafeRep equivalence when the contract depends only
on the generated posterior. -/
theorem safeRep_historyViaModelPosterior_iff_modelBelief
    {History Theta A Y : Type*} [Fintype Theta]
    {beta : History → FiniteLaw Theta}
    {loss : Theta → A → ℚ} {threshold : ℚ}
    {BH : Set History} {C : Set A}
    {r : FiniteLaw Theta → Y} :
    SafeRep
      (HistoryGoodViaBelief beta (ModelRiskGood loss threshold))
      BH C (fun h => r (beta h)) ↔
    SafeRep
      (ModelRiskGood loss threshold)
      (BeliefImage beta BH) C r := by
  exact safeRep_historyViaBelief_iff_belief

/-- Finite indexed model-belief families inherit the exact hypergraph
characterization of actionability. -/
theorem modelRiskSafeRep_indexed_iff_hypergraphSafe
    {I Theta A Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype Theta]
    (belief : I → FiniteLaw Theta)
    (loss : Theta → A → ℚ) (threshold : ℚ)
    (BI : Set I) (C : Set A) (h : I → Y) :
    SafeRep (fun i a => ModelRiskGood loss threshold (belief i) a) BI C h ↔
      HypergraphSafe (fun i a => ModelRiskGood loss threshold (belief i) a) BI C h := by
  exact safeRep_iff_hypergraphSafe

/-- Declared planner candidate over model-belief information/capability states. -/
def ModelLearningCandidateSafe
    {I Theta A Y : Type*} [Fintype Theta]
    (loss : Theta → A → ℚ) (threshold : ℚ)
    (B : Set (FiniteLaw Theta))
    (caps : I → Set A)
    (obs : I → FiniteLaw Theta → Y)
    (i : I) : Prop :=
  ModelRiskSafeRep loss threshold B (caps i) (obs i)

/-- Existing INSACERMO router remains complete on a declared learning-state
candidate graph. Learning changes information state; the router semantics do
not need a new runtime layer. -/
theorem modelLearningPlanner_router_complete
    {I Theta A Y : Type*} [Fintype Theta]
    (loss : Theta → A → ℚ) (threshold : ℚ)
    (B : Set (FiniteLaw Theta))
    (caps : I → Set A)
    (obs : I → FiniteLaw Theta → Y)
    (BaseAllowed PreserveOK : I → Move I → Prop)
    (i : I) :
    ModelLearningCandidateSafe loss threshold B caps obs i ∨
      (¬ ModelLearningCandidateSafe loss threshold B caps obs i ∧
        ¬ ReachableSafe
          (ModelLearningCandidateSafe loss threshold B caps obs)
          (LegalStep BaseAllowed PreserveOK) i) ∨
      (¬ ModelLearningCandidateSafe loss threshold B caps obs i ∧
        ReachableSafe
          (ModelLearningCandidateSafe loss threshold B caps obs)
          (LegalStep BaseAllowed PreserveOK) i ∧
        ∃ k, OptimalFrontierKind
          (ModelLearningCandidateSafe loss threshold B caps obs)
          (LegalStep BaseAllowed PreserveOK) i k) := by
  exact planner_router_complete
    (ModelLearningCandidateSafe loss threshold B caps obs)
    (LegalStep BaseAllowed PreserveOK) i

end InsacermoActionabilityInformation
