import Lean.Elab.Tactic.Omega

namespace INSACERMO.MinimumProofAcquisitionV1

def proofDeficit (rho U : Nat) : Nat :=
  if U < rho then 0 else U - rho + 1

theorem proof_deficit_zero_iff
    (rho U : Nat) :
    proofDeficit rho U = 0 ↔ U < rho := by
  unfold proofDeficit
  split <;> omega

theorem proof_deficit_exact
    (rho U G : Nat)
    (hrho : 0 < rho) :
    U - G < rho ↔ proofDeficit rho U ≤ G := by
  unfold proofDeficit
  split <;> omega

theorem act_restored_of_gain_covers_deficit
    (rho U G : Nat)
    (hrho : 0 < rho)
    (hgain : proofDeficit rho U ≤ G) :
    U - G < rho := by
  exact (proof_deficit_exact rho U G hrho).2 hgain

theorem gain_cover_is_necessary
    (rho U G : Nat)
    (hrho : 0 < rho)
    (hact : U - G < rho) :
    proofDeficit rho U ≤ G := by
  exact (proof_deficit_exact rho U G hrho).1 hact

theorem same_debt_two_bound_collapse
    (rho U₁ U₂ : Nat)
    (h : Nat.min U₁ U₂ < rho) :
    U₁ < rho ∨ U₂ < rho := by
  by_cases hle : U₁ ≤ U₂
  · left
    simpa [Nat.min_eq_left hle] using h
  · right
    have hle₂ : U₂ ≤ U₁ := by omega
    simpa [Nat.min_eq_right hle₂] using h

theorem same_debt_two_certificates_sound
    (D rho U₁ U₂ : Nat)
    (h₁ : D ≤ U₁)
    (h₂ : D ≤ U₂)
    (hact : Nat.min U₁ U₂ < rho) :
    D < rho := by
  have hm : D ≤ Nat.min U₁ U₂ := (Nat.le_min).2 ⟨h₁, h₂⟩
  omega

theorem additive_component_certificates_sound
    (D₁ D₂ U₁ U₂ rho : Nat)
    (h₁ : D₁ ≤ U₁)
    (h₂ : D₂ ≤ U₂)
    (hact : U₁ + U₂ < rho) :
    D₁ + D₂ < rho := by
  omega

theorem exact_component_tightening_restores_act
    (rho U post G : Nat)
    (hrho : 0 < rho)
    (haccount : post + G = U)
    (hgain : proofDeficit rho U ≤ G) :
    post < rho := by
  have hsub : U - G < rho :=
    act_restored_of_gain_covers_deficit rho U G hrho hgain
  omega

theorem insufficient_gain_cannot_restore
    (rho U G : Nat)
    (hrho : 0 < rho)
    (hsmall : G < proofDeficit rho U) :
    ¬ U - G < rho := by
  intro hact
  have hneed : proofDeficit rho U ≤ G :=
    gain_cover_is_necessary rho U G hrho hact
  omega

example : proofDeficit 100 130 = 31 := by decide
example : proofDeficit 100 90 = 0 := by decide
example : 130 - 31 < 100 := by decide
example : ¬ (130 - 30 < 100) := by decide

#print axioms proof_deficit_zero_iff
#print axioms proof_deficit_exact
#print axioms act_restored_of_gain_covers_deficit
#print axioms gain_cover_is_necessary
#print axioms same_debt_two_bound_collapse
#print axioms same_debt_two_certificates_sound
#print axioms additive_component_certificates_sound
#print axioms exact_component_tightening_restores_act
#print axioms insufficient_gain_cannot_restore

end INSACERMO.MinimumProofAcquisitionV1
