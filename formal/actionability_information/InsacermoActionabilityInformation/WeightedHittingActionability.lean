import InsacermoActionabilityInformation.MaximalFeasibility

namespace InsacermoActionabilityInformation

/-- Observation retained by a finite selection of probes/features. The output
is the tuple of selected probe values, indexed by the selected finite set. -/
def SelectedObs {I S Y : Type*} [DecidableEq I]
    (obs : I → S → Y) (H : Finset I) : S → ({i // i ∈ H} → Y) :=
  fun s i => obs i.1 s

/-- A selected probe set hits every incompatible world-pair when every pair
requiring different deterministic actions is separated by at least one
selected probe. This is the discernibility / hitting-set predicate. -/
def HitsIncompatiblePairs {I S A Y : Type*} [DecidableEq I]
    (B : Set S) (label : S → A) (obs : I → S → Y) (H : Finset I) : Prop :=
  ∀ s, s ∈ B → ∀ t, t ∈ B → label s ≠ label t →
    ∃ i, i ∈ H ∧ obs i s ≠ obs i t

/-- Exact deterministic equivalence: under complete action capability, a
selected observation tuple is SafeRep iff the selected probes hit every
cross-action incompatible pair. -/
theorem safeRep_selectedObs_iff_hitsIncompatiblePairs
    {I S A Y : Type*} [DecidableEq I]
    {B : Set S} {C : Set A} {label : S → A} {obs : I → S → Y}
    {H : Finset I}
    (hcap : ∀ s, s ∈ B → label s ∈ C) :
    SafeRep (DeterministicGood label) B C (SelectedObs obs H) ↔
      HitsIncompatiblePairs B label obs H := by
  constructor
  · intro hsafe
    have hfiber := (safeRep_deterministic_iff_fiberConstant hcap).mp hsafe
    intro s hsB t htB hdiff
    by_contra hno
    have hall : ∀ i, i ∈ H → obs i s = obs i t := by
      intro i hi
      by_contra hneq
      exact hno ⟨i, hi, hneq⟩
    have halias : SelectedObs obs H s = SelectedObs obs H t := by
      funext i
      exact hall i.1 i.2
    exact hdiff (hfiber s hsB t htB halias)
  · intro hhits
    apply (safeRep_deterministic_iff_fiberConstant hcap).mpr
    intro s hsB t htB halias
    by_contra hdiff
    rcases hhits s hsB t htB hdiff with ⟨i, hi, hsep⟩
    have heq : obs i s = obs i t := congrFun halias ⟨i, hi⟩
    exact hsep heq

/-- Additive cost of a finite probe selection. For the resolution experiments,
`cost i` can be the bit-cost of the corresponding feature-resolution option. -/
def SelectionCost {I : Type*} [DecidableEq I]
    (cost : I → Nat) (H : Finset I) : Nat :=
  ∑ i in H, cost i

/-- There exists an admissible selected representation that is safe within a
specified budget. `Valid` can encode arbitrary side constraints, including
"at most one resolution option per feature" or nested-resolution contracts. -/
def ActionSafeWithinBudget {I S A Y : Type*} [DecidableEq I]
    (B : Set S) (C : Set A) (label : S → A) (obs : I → S → Y)
    (Valid : Finset I → Prop) (cost : I → Nat) (budget : Nat) : Prop :=
  ∃ H : Finset I,
    Valid H ∧
    SelectionCost cost H ≤ budget ∧
    SafeRep (DeterministicGood label) B C (SelectedObs obs H)

/-- Constrained weighted hitting-set feasibility for the same contract. -/
def WeightedHittingSetWithinBudget {I S A Y : Type*} [DecidableEq I]
    (B : Set S) (label : S → A) (obs : I → S → Y)
    (Valid : Finset I → Prop) (cost : I → Nat) (budget : Nat) : Prop :=
  ∃ H : Finset I,
    Valid H ∧
    SelectionCost cost H ≤ budget ∧
    HitsIncompatiblePairs B label obs H

/-- Budget-by-budget equivalence. Under a deterministic contract with all
required actions available, searching for a safe representation under any
finite weighted selection constraint is exactly the corresponding constrained
weighted hitting-set problem on incompatible world-pairs. -/
theorem actionSafeWithinBudget_iff_weightedHittingSetWithinBudget
    {I S A Y : Type*} [DecidableEq I]
    {B : Set S} {C : Set A} {label : S → A} {obs : I → S → Y}
    {Valid : Finset I → Prop} {cost : I → Nat} {budget : Nat}
    (hcap : ∀ s, s ∈ B → label s ∈ C) :
    ActionSafeWithinBudget B C label obs Valid cost budget ↔
      WeightedHittingSetWithinBudget B label obs Valid cost budget := by
  constructor
  · rintro ⟨H, hvalid, hcost, hsafe⟩
    exact ⟨H, hvalid, hcost,
      (safeRep_selectedObs_iff_hitsIncompatiblePairs hcap).mp hsafe⟩
  · rintro ⟨H, hvalid, hcost, hhits⟩
    exact ⟨H, hvalid, hcost,
      (safeRep_selectedObs_iff_hitsIncompatiblePairs hcap).mpr hhits⟩

/-- `k` is the exact minimum actionability cost when a safe admissible
selection exists at budget `k` and no smaller budget is feasible. -/
def IsMinimumActionabilityCost {I S A Y : Type*} [DecidableEq I]
    (B : Set S) (C : Set A) (label : S → A) (obs : I → S → Y)
    (Valid : Finset I → Prop) (cost : I → Nat) (k : Nat) : Prop :=
  ActionSafeWithinBudget B C label obs Valid cost k ∧
    ∀ j, j < k → ¬ ActionSafeWithinBudget B C label obs Valid cost j

/-- `k` is the exact minimum constrained weighted hitting-set cost. -/
def IsMinimumWeightedHittingCost {I S A Y : Type*} [DecidableEq I]
    (B : Set S) (label : S → A) (obs : I → S → Y)
    (Valid : Finset I → Prop) (cost : I → Nat) (k : Nat) : Prop :=
  WeightedHittingSetWithinBudget B label obs Valid cost k ∧
    ∀ j, j < k → ¬ WeightedHittingSetWithinBudget B label obs Valid cost j

/-- Exact optimization theorem: the minimum deterministic actionability cost
is exactly the minimum constrained weighted hitting-set cost. This is the
formal version of the resolution-budget optimization used in the empirical
V1 experiments. -/
theorem minimumActionabilityCost_iff_minimumWeightedHittingCost
    {I S A Y : Type*} [DecidableEq I]
    {B : Set S} {C : Set A} {label : S → A} {obs : I → S → Y}
    {Valid : Finset I → Prop} {cost : I → Nat} {k : Nat}
    (hcap : ∀ s, s ∈ B → label s ∈ C) :
    IsMinimumActionabilityCost B C label obs Valid cost k ↔
      IsMinimumWeightedHittingCost B label obs Valid cost k := by
  constructor
  · rintro ⟨hk, hmin⟩
    refine ⟨(actionSafeWithinBudget_iff_weightedHittingSetWithinBudget hcap).mp hk, ?_⟩
    intro j hj hhit
    exact hmin j hj
      ((actionSafeWithinBudget_iff_weightedHittingSetWithinBudget hcap).mpr hhit)
  · rintro ⟨hk, hmin⟩
    refine ⟨(actionSafeWithinBudget_iff_weightedHittingSetWithinBudget hcap).mpr hk, ?_⟩
    intro j hj hsafe
    exact hmin j hj
      ((actionSafeWithinBudget_iff_weightedHittingSetWithinBudget hcap).mp hsafe)

end InsacermoActionabilityInformation
