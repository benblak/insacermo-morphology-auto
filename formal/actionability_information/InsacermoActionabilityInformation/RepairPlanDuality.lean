import InsacermoActionabilityInformation.TemporalJointContractComplex

namespace InsacermoActionabilityInformation

namespace RepairPlanDuality

/-- A finite future bundle is feasible when one complete plan satisfies every
future in the bundle.  The plan may encode an entire continuation, not merely
the first action. -/
def BundleFeasible {Q Plan : Type*} [DecidableEq Q]
    (Good : Plan → Q → Prop) (F : Finset Q) : Prop :=
  ∃ p : Plan, ∀ q, q ∈ F → Good p q

/-- The future signature realized by a complete plan. -/
def PlanSignature {Q Plan : Type*}
    (Good : Plan → Q → Prop) (p : Plan) : Set Q :=
  {q | Good p q}

/-- The futures failed by a complete plan. -/
def PlanFailureSet {Q Plan : Type*}
    (Good : Plan → Q → Prop) (p : Plan) : Set Q :=
  {q | ¬ Good p q}

/-- Exact plan-facet representation: a bundle is feasible iff it is contained
in the future signature of some complete plan. -/
theorem bundleFeasible_iff_subset_planSignature
    {Q Plan : Type*} [DecidableEq Q]
    {Good : Plan → Q → Prop} {F : Finset Q} :
    BundleFeasible Good F ↔
      ∃ p : Plan, (↑F : Set Q) ⊆ PlanSignature Good p := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    intro q hq
    exact hp q hq
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    intro q hq
    exact hp hq

/-- Dual blocker form: a bundle is infeasible iff every complete plan fails at
least one future from the bundle. -/
theorem not_bundleFeasible_iff_hits_every_planFailure
    {Q Plan : Type*} [DecidableEq Q]
    {Good : Plan → Q → Prop} {F : Finset Q} :
    ¬ BundleFeasible Good F ↔
      ∀ p : Plan, ∃ q, q ∈ F ∧ q ∈ PlanFailureSet Good p := by
  classical
  constructor
  · intro h p
    by_contra hno
    push_neg at hno
    apply h
    refine ⟨p, ?_⟩
    intro q hq
    by_contra hbad
    exact hno q hq hbad
  · intro h hfeas
    rcases hfeas with ⟨p, hp⟩
    rcases h p with ⟨q, hqF, hqbad⟩
    exact hqbad (hp q hqF)

/-- Inclusion-minimal joint infeasibility. -/
def MinimalBundleObstruction {Q Plan : Type*} [DecidableEq Q]
    (Good : Plan → Q → Prop) (F : Finset Q) : Prop :=
  ¬ BundleFeasible Good F ∧
    ∀ G : Finset Q, G ⊂ F → BundleFeasible Good G

/-- Private-witness certificate for every vertex of a minimal obstruction.
For every future q in a minimal obstruction F, there exists one complete plan
that satisfies every other future of F but fails q itself.  Hence every future
in a minimal obstruction is genuinely indispensable. -/
theorem minimalBundleObstruction_privateWitness
    {Q Plan : Type*} [DecidableEq Q]
    {Good : Plan → Q → Prop} {F : Finset Q}
    (hmin : MinimalBundleObstruction Good F)
    {q : Q} (hq : q ∈ F) :
    ∃ p : Plan,
      (∀ r, r ∈ F → r ≠ q → Good p r) ∧
      ¬ Good p q := by
  have hproper : F.erase q ⊂ F := Finset.erase_ssubset hq
  rcases hmin.2 (F.erase q) hproper with ⟨p, hp⟩
  refine ⟨p, ?_, ?_⟩
  · intro r hrF hrne
    exact hp r (Finset.mem_erase.mpr ⟨hrne, hrF⟩)
  · intro hpq
    apply hmin.1
    refine ⟨p, ?_⟩
    intro r hrF
    by_cases hrq : r = q
    · subst r
      exact hpq
    · exact hp r (Finset.mem_erase.mpr ⟨hrq, hrF⟩)

/-- A plan that satisfies at least all futures satisfied by another plan
dominates it for purposes of the future complex. -/
def PlanDominates {Q Plan : Type*}
    (Good : Plan → Q → Prop) (p p' : Plan) : Prop :=
  PlanSignature Good p' ⊆ PlanSignature Good p

/-- Replacing a witnessing plan by a dominating plan preserves feasibility. -/
theorem feasible_of_dominating_witness
    {Q Plan : Type*} [DecidableEq Q]
    {Good : Plan → Q → Prop} {F : Finset Q}
    {p p' : Plan}
    (hF : (↑F : Set Q) ⊆ PlanSignature Good p')
    (hdom : PlanDominates Good p p') :
    BundleFeasible Good F := by
  apply bundleFeasible_iff_subset_planSignature.mpr
  exact ⟨p, Set.Subset.trans hF hdom⟩


/-! ## Budget filtration -/

/-- Plans whose cost is within a fixed budget. -/
def BudgetPlan {Plan : Type*} (cost : Plan → ℕ) (budget : ℕ) :=
  {p : Plan // cost p ≤ budget}

/-- A finite bundle is feasible within a budget when one budget-admissible plan
satisfies every future in the bundle. -/
def BudgetBundleFeasible {Q Plan : Type*} [DecidableEq Q]
    (Good : Plan → Q → Prop) (cost : Plan → ℕ)
    (budget : ℕ) (F : Finset Q) : Prop :=
  ∃ p : Plan, cost p ≤ budget ∧ ∀ q, q ∈ F → Good p q

/-- More budget cannot destroy bundle feasibility. -/
theorem budgetBundleFeasible_mono
    {Q Plan : Type*} [DecidableEq Q]
    {Good : Plan → Q → Prop} {cost : Plan → ℕ}
    {b b' : ℕ} {F : Finset Q}
    (hbb : b ≤ b')
    (h : BudgetBundleFeasible Good cost b F) :
    BudgetBundleFeasible Good cost b' F := by
  rcases h with ⟨p, hcost, hgood⟩
  exact ⟨p, Nat.le_trans hcost hbb, hgood⟩

/-- Budget feasibility is ordinary plan feasibility on the subtype of plans
whose cost is within the budget. -/
theorem budgetBundleFeasible_iff_bundleFeasible_subtype
    {Q Plan : Type*} [DecidableEq Q]
    {Good : Plan → Q → Prop} {cost : Plan → ℕ}
    {budget : ℕ} {F : Finset Q} :
    BudgetBundleFeasible Good cost budget F ↔
      BundleFeasible
        (fun p : BudgetPlan cost budget => fun q => Good p.1 q) F := by
  constructor
  · rintro ⟨p, hcost, hgood⟩
    exact ⟨⟨p, hcost⟩, hgood⟩
  · rintro ⟨p, hgood⟩
    exact ⟨p.1, p.2, hgood⟩

/-- Every minimal obstruction at a fixed budget has a private budget-admissible
witness for each of its futures. -/
theorem budgetMinimalObstruction_privateWitness
    {Q Plan : Type*} [DecidableEq Q]
    {Good : Plan → Q → Prop} {cost : Plan → ℕ}
    {budget : ℕ} {F : Finset Q}
    (hmin : MinimalBundleObstruction
      (fun p : BudgetPlan cost budget => fun q => Good p.1 q) F)
    {q : Q} (hq : q ∈ F) :
    ∃ p : Plan,
      cost p ≤ budget ∧
      (∀ r, r ∈ F → r ≠ q → Good p r) ∧
      ¬ Good p q := by
  rcases minimalBundleObstruction_privateWitness hmin hq with
    ⟨p, hothers, hfail⟩
  exact ⟨p.1, p.2, hothers, hfail⟩

/-! ## Exact bridge to the existing temporal joint complex -/

open TemporalJointContractComplex

/-- A certified temporal joint plan is a future bundle together with a kernel-
checked witness that this whole bundle is jointly recoverable by horizon H. -/
def CertifiedJointPlan {Q X : Type*}
    (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) :=
  {R : Set Q // JointRecoverable Avail Step H x R}

/-- A certified joint plan supports exactly the futures in its certified
recoverable bundle. -/
def CertifiedJointPlanGood
    {Q X : Type*}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X}
    (p : CertifiedJointPlan Avail Step H x) (q : Q) : Prop :=
  q ∈ p.1

/-- Exact temporal bridge: a finite future bundle has one certified common plan
iff it is jointly recoverable in the existing temporal semantics. -/
theorem jointRecoverable_iff_bundleFeasible_certifiedPlan
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {F : Finset Q} :
    JointRecoverable Avail Step H x (↑F : Set Q) ↔
      BundleFeasible
        (CertifiedJointPlanGood
          (Avail := Avail) (Step := Step) (H := H) (x := x)) F := by
  constructor
  · intro hF
    refine ⟨⟨(↑F : Set Q), hF⟩, ?_⟩
    intro q hq
    exact hq
  · rintro ⟨p, hp⟩
    apply jointRecoverable_downward H x p.2
    intro q hq
    exact hp q hq

/-! ## Chain-collapse for single mandatory repair signatures -/

/-- Atomic repairs required by a bundle when each future q has one mandatory
repair signature Req q. -/
def RequiredRepairs {Q A : Type*} [DecidableEq Q]
    (Req : Q → Set A) (F : Finset Q) : Set A :=
  {a | ∃ q, q ∈ F ∧ a ∈ Req q}

/-- If one future qMax in the bundle has a repair signature containing every
other signature in the bundle, then the whole bundle requires exactly qMax's
signature. This is the abstract chain-collapse mechanism observed in Mathlib. -/
theorem requiredRepairs_eq_topSignature
    {Q A : Type*} [DecidableEq Q]
    {Req : Q → Set A} {F : Finset Q} {qMax : Q}
    (hqMax : qMax ∈ F)
    (hTop : ∀ q, q ∈ F → Req q ⊆ Req qMax) :
    RequiredRepairs Req F = Req qMax := by
  ext a
  constructor
  · rintro ⟨q, hqF, ha⟩
    exact hTop q hqF ha
  · intro ha
    exact ⟨qMax, hqMax, ha⟩

/-- Any set-valued cost functional therefore collapses to the top signature
under the same hypothesis. -/
theorem requiredRepairCost_eq_topCost
    {Q A C : Type*} [DecidableEq Q]
    {Req : Q → Set A} {F : Finset Q} {qMax : Q}
    (Cost : Set A → C)
    (hqMax : qMax ∈ F)
    (hTop : ∀ q, q ∈ F → Req q ⊆ Req qMax) :
    Cost (RequiredRepairs Req F) = Cost (Req qMax) := by
  rw [requiredRepairs_eq_topSignature hqMax hTop]

end RepairPlanDuality

end InsacermoActionabilityInformation
