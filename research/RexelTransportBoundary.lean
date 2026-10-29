/-! INSACERMO isolated lab: transport needs explicit contract invariance. -/
namespace InsacermoTransportLab
universe u v w
theorem transport_if_observation_and_contract_invariant
    {World : Type u} {Observation : Type v} {Action : Type w}
    (oldScope newScope : World → Prop)
    (observation : World → Observation)
    (good : World → Action → Prop)
    (choose : Observation → Action)
    (oldSafe : ∀ x, oldScope x → good x (choose (observation x)))
    (covered : ∀ x, newScope x →
      ∃ y, oldScope y ∧ observation y = observation x)
    (invariant : ∀ x y, newScope x → oldScope y →
      observation y = observation x →
      ∀ a, good y a → good x a) :
    ∀ x, newScope x → good x (choose (observation x)) := by
  intro x hx
  obtain ⟨y, hy, hobs⟩ := covered x hx
  have hg : good y (choose (observation y)) := oldSafe y hy
  have htx : good x (choose (observation y)) :=
    invariant x y hx hy hobs (choose (observation y)) hg
  simpa [hobs] using htx
theorem matching_observation_does_not_force_matching_outcome :
    ∃ (observation outcome : Bool → Bool),
      observation false = observation true ∧
      outcome false ≠ outcome true := by
  refine ⟨(fun _ => false), (fun b => b), ?_, ?_⟩
  · rfl
  · decide
theorem impossible_to_classify_both_opposite_labels
    {World : Type u} {Observation : Type v}
    (x y : World) (observe : World → Observation)
    (label : World → Bool)
    (same : observe x = observe y)
    (opposite : label x ≠ label y) :
    ¬ ∃ classifier : Observation → Bool,
      classifier (observe x) = label x ∧
      classifier (observe y) = label y := by
  intro h
  obtain ⟨classifier, hx, hy⟩ := h
  apply opposite
  calc
    label x = classifier (observe x) := hx.symm
    _ = classifier (observe y) := congrArg classifier same
    _ = label y := hy
end InsacermoTransportLab
