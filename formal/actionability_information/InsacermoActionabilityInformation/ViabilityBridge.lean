import InsacermoActionabilityInformation.DecisionSemantics
import Mathlib

namespace InsacermoActionabilityInformation

namespace ViabilityBridge

open TemporalRecoverabilityEnvelope
open DecisionSemantics

variable {X : Type*}

/-- Encode an ordinary state-safety set as a one-future INSACERMO
availability map.  The unique future is available exactly in safe states. -/
def StateSafetyAvail (Safe : Set X) (x : X) : Set Unit :=
  fun _ : Unit => x ∈ Safe

@[simp] theorem unit_mem_stateSafetyAvail_iff
    {Safe : Set X} {x : X} :
    () ∈ StateSafetyAvail Safe x ↔ x ∈ Safe := by
  rfl

/-- A strict one-future INSACERMO PRESERVE judgment is exactly membership in
the classical state-safety set. -/
theorem preserve_singleton_iff_safe
    {Safe : Set X} {x : X} :
    PRESERVE ({()} : Set Unit) (StateSafetyAvail Safe) x ↔ x ∈ Safe := by
  constructor
  · intro hpres
    have hunit : () ∈ StateSafetyAvail Safe x := hpres (by simp)
    exact unit_mem_stateSafetyAvail_iff.mp hunit
  · intro hx q hq
    have hqUnit : q = () := Subsingleton.elim q ()
    subst q
    exact unit_mem_stateSafetyAvail_iff.mpr hx

/-- Classical one-step viability: the current state is safe and there exists
an admissible successor that is also safe. -/
def OneStepViable
    (Safe : Set X) (Step : X → X → Prop) (x : X) : Prop :=
  x ∈ Safe ∧ ∃ y, Step x y ∧ y ∈ Safe

/-- One-step viability is exactly existence of an admissible successor that
satisfies the strict INSACERMO preservation contract. -/
theorem oneStepViable_iff_preserving_successor
    {Safe : Set X} {Step : X → X → Prop} {x : X} :
    OneStepViable Safe Step x ↔
      x ∈ Safe ∧
        ∃ y, Step x y ∧
          PRESERVE ({()} : Set Unit) (StateSafetyAvail Safe) y := by
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨hx, y, hxy, preserve_singleton_iff_safe.mpr hy⟩
  · rintro ⟨hx, y, hxy, hpres⟩
    exact ⟨hx, y, hxy, preserve_singleton_iff_safe.mp hpres⟩

/-- Standard controlled-invariance condition stated relationally. -/
def ControlledInvariant
    (Safe : Set X) (Step : X → X → Prop) : Prop :=
  ∀ x, x ∈ Safe → ∃ y, Step x y ∧ y ∈ Safe

/-- Controlled invariance is exactly the statement that every safe state has
an admissible successor satisfying the strict one-future INSACERMO contract. -/
theorem controlledInvariant_iff_contract_preserving_successor
    {Safe : Set X} {Step : X → X → Prop} :
    ControlledInvariant Safe Step ↔
      ∀ x, x ∈ Safe →
        ∃ y, Step x y ∧
          PRESERVE ({()} : Set Unit) (StateSafetyAvail Safe) y := by
  constructor
  · intro hinv x hx
    rcases hinv x hx with ⟨y, hxy, hy⟩
    exact ⟨y, hxy, preserve_singleton_iff_safe.mpr hy⟩
  · intro hins x hx
    rcases hins x hx with ⟨y, hxy, hpres⟩
    exact ⟨y, hxy, preserve_singleton_iff_safe.mp hpres⟩

/-- INSACERMO deadline preservation is strictly a recoverability semantics,
not merely hard state invariance: an unsafe current state may still satisfy
the one-future contract within one step when a safe successor is reachable. -/
theorem unsafe_now_but_preserved_within_one
    {Safe : Set X} {Step : X → X → Prop}
    {x y : X}
    (hx : x ∉ Safe)
    (hxy : Step x y)
    (hy : y ∈ Safe) :
    ¬ PRESERVE ({()} : Set Unit) (StateSafetyAvail Safe) x ∧
      PRESERVE_WITHIN ({()} : Set Unit)
        (StateSafetyAvail Safe) Step 1 x := by
  constructor
  · intro hpres
    exact hx (preserve_singleton_iff_safe.mp hpres)
  · apply safeWithin_iff_required_subset_recoverableEnvelope.mpr
    intro q hq
    have hqUnit : q = () := by
      simpa using hq
    subst q
    exact Or.inr ⟨y, hxy, unit_mem_stateSafetyAvail_iff.mpr hy⟩

/-- Hence strict viability-style preservation implies the deadline form, but
the deadline form can hold even outside the hard safety set. -/
theorem preserve_strictly_stronger_than_recoverability_witness
    {Safe : Set X} {Step : X → X → Prop}
    {x y : X}
    (hx : x ∉ Safe)
    (hxy : Step x y)
    (hy : y ∈ Safe) :
    (¬ PRESERVE ({()} : Set Unit) (StateSafetyAvail Safe) x) ∧
      PRESERVE_WITHIN ({()} : Set Unit)
        (StateSafetyAvail Safe) Step 1 x :=
  unsafe_now_but_preserved_within_one hx hxy hy

end ViabilityBridge

end InsacermoActionabilityInformation
