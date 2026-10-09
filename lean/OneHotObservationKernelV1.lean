import Std

/-!
INSACERMO One-Hot Observation Kernel V1

This kernel formalizes the one-hot observation *soundness equivalence*
used by V5/V6. It does NOT yet formalize the graph interpreter, the
minimum cardinality optimization, the Bellman planner, or certificates
for individual OpenFlights instances.

No sorry/admit/custom axioms.
-/

namespace Insacermo.OneHot

universe u v

variable {World : Type u} {Action : Type v}

def SameObservations (S : List World) (x y : World) : Prop :=
  ∀ p, p ∈ S → (p = x ↔ p = y)

def GloballySound (S : List World) (act : World → Action) : Prop :=
  ∀ x y, SameObservations S x y → act x = act y

def UnprobedSameAction (S : List World) (act : World → Action) : Prop :=
  ∀ x y, x ∉ S → y ∉ S → act x = act y

theorem sameObservations_of_both_unprobed
    (S : List World) (x y : World)
    (hx : x ∉ S) (hy : y ∉ S) :
    SameObservations S x y := by
  intro p hp
  constructor
  · intro hpx
    have hxS : x ∈ S := hpx ▸ hp
    exact False.elim (hx hxS)
  · intro hpy
    have hyS : y ∈ S := hpy ▸ hp
    exact False.elim (hy hyS)

theorem globallySound_of_unprobedSameAction
    (S : List World) (act : World → Action)
    (h : UnprobedSameAction S act) :
    GloballySound S act := by
  intro x y hsig
  by_cases hx : x ∈ S
  · have hxy : x = y := (hsig x hx).mp rfl
    exact congrArg act hxy
  · by_cases hy : y ∈ S
    · have hyx : y = x := (hsig y hy).mpr rfl
      exact congrArg act hyx.symm
    · exact h x y hx hy

theorem globallySound_iff_unprobedSameAction
    (S : List World) (act : World → Action) :
    GloballySound S act ↔ UnprobedSameAction S act := by
  constructor
  · intro h x y hx hy
    exact h x y (sameObservations_of_both_unprobed S x y hx hy)
  · exact globallySound_of_unprobedSameAction S act

theorem opposite_actions_require_observing_one
    (S : List World) (act : World → Action)
    (sound : GloballySound S act)
    (x y : World) (hdiff : act x ≠ act y) :
    x ∈ S ∨ y ∈ S := by
  by_contra hnone
  have hx : x ∉ S := by
    intro hx
    exact hnone (Or.inl hx)
  have hy : y ∉ S := by
    intro hy
    exact hnone (Or.inr hy)
  exact hdiff (sound x y (sameObservations_of_both_unprobed S x y hx hy))

end Insacermo.OneHot
