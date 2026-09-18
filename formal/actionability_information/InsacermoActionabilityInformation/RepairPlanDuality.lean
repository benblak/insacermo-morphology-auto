import Mathlib

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

end RepairPlanDuality

end InsacermoActionabilityInformation
