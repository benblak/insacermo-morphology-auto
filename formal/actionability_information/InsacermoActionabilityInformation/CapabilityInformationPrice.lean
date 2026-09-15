import InsacermoActionabilityInformation.WeightedHittingActionability

namespace InsacermoActionabilityInformation

/-- Budget-feasible actionability for an arbitrary Good relation. The same
finite observation-selection language and additive information cost are used
as in `WeightedHittingActionability`, but capability can now change which
common actions are available on each observation fiber. -/
def GeneralActionSafeWithinBudget {I S A Y : Type*} [DecidableEq I]
    (Good : S → A → Prop) (B : Set S) (C : Set A)
    (obs : I → S → Y) (Valid : Finset I → Prop)
    (cost : I → Nat) (budget : Nat) : Prop :=
  ∃ H : Finset I,
    Valid H ∧
    SelectionCost cost H ≤ budget ∧
    SafeRep Good B C (SelectedObs obs H)

/-- Capability expansion cannot destroy feasibility at a fixed information
budget: the very same selected representation remains safe. -/
theorem generalActionSafeWithinBudget_mono_capability
    {I S A Y : Type*} [DecidableEq I]
    {Good : S → A → Prop} {B : Set S} {C C' : Set A}
    {obs : I → S → Y} {Valid : Finset I → Prop}
    {cost : I → Nat} {budget : Nat}
    (hcap : C ⊆ C') :
    GeneralActionSafeWithinBudget Good B C obs Valid cost budget →
      GeneralActionSafeWithinBudget Good B C' obs Valid cost budget := by
  rintro ⟨H, hvalid, hcost, hsafe⟩
  have href : Refines (SelectedObs obs H) (SelectedObs obs H) := by
    exact ⟨fun x => x, fun s => rfl⟩
  exact ⟨H, hvalid, hcost,
    safeRep_of_refines_of_capabilitySubset hsafe href hcap⟩

/-- `k` is the exact minimum information-selection cost needed for actionability
under capability set `C`. -/
def IsMinimumGeneralActionabilityCost {I S A Y : Type*} [DecidableEq I]
    (Good : S → A → Prop) (B : Set S) (C : Set A)
    (obs : I → S → Y) (Valid : Finset I → Prop)
    (cost : I → Nat) (k : Nat) : Prop :=
  GeneralActionSafeWithinBudget Good B C obs Valid cost k ∧
    ∀ j, j < k → ¬ GeneralActionSafeWithinBudget Good B C obs Valid cost j

/-- Quantitative capability-information law. If `C ⊆ C'`, and exact minimum
information costs exist at both capability levels, then the minimum information
cost under the larger capability set cannot be higher.

This is the optimization-level form of capability-information monotonicity:
more available action capability can only preserve or lower the price of the
information required to justify action. -/
theorem minimumInformationCost_antitone_capability
    {I S A Y : Type*} [DecidableEq I]
    {Good : S → A → Prop} {B : Set S} {C C' : Set A}
    {obs : I → S → Y} {Valid : Finset I → Prop}
    {cost : I → Nat} {k k' : Nat}
    (hcap : C ⊆ C')
    (hk : IsMinimumGeneralActionabilityCost Good B C obs Valid cost k)
    (hk' : IsMinimumGeneralActionabilityCost Good B C' obs Valid cost k') :
    k' ≤ k := by
  rcases hk with ⟨hkSafe, _hkMin⟩
  rcases hk' with ⟨_hk'Safe, hk'Min⟩
  by_contra hnot
  have hlt : k < k' := Nat.lt_of_not_ge hnot
  have hkSafe' : GeneralActionSafeWithinBudget Good B C' obs Valid cost k :=
    generalActionSafeWithinBudget_mono_capability hcap hkSafe
  exact (hk'Min k hlt) hkSafe'

/-- Equivalent verbal orientation: shrinking capability cannot lower the exact
minimum information cost, whenever both minima exist. -/
theorem minimumInformationCost_mono_capabilityLoss
    {I S A Y : Type*} [DecidableEq I]
    {Good : S → A → Prop} {B : Set S} {C C' : Set A}
    {obs : I → S → Y} {Valid : Finset I → Prop}
    {cost : I → Nat} {k k' : Nat}
    (hcap : C ⊆ C')
    (hk : IsMinimumGeneralActionabilityCost Good B C obs Valid cost k)
    (hk' : IsMinimumGeneralActionabilityCost Good B C' obs Valid cost k') :
    k ≤ k' → k = k' := by
  intro hreverse
  exact Nat.le_antisymm hreverse
    (minimumInformationCost_antitone_capability hcap hk hk')

end InsacermoActionabilityInformation
