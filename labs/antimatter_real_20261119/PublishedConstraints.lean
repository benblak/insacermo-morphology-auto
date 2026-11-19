import Lean
import labs.refus_espoir_20261119.RefusEspoirBridge

namespace INSACERMO.PublishedBaryogenesisConstraints
open INSACERMO.RefusEspoir

/-!
Exact implications from numerical quantities TRANSCRIBED from published sources.
Lean proves the finite arithmetic consequences, not the truth/completeness of
the physical theories, the experimental confidence limits or the provenance.
The coarse observation example below is an explicitly DECLARED abstraction.
-/

/-- Liu Qin Bian 2026: the particular dimension-6 model uses two scales.
    A first-order transition is studied at Lambda 600-900 GeV.
    The eEDM constraint in the article implies Lambda_CPV ≳ 338 TeV.
    When these scales are identified no lambda can satisfy both intervals. -/
theorem common_scale_incompatible (lambda : Nat)
    (hEWPT : 600 ≤ lambda ∧ lambda ≤ 900)
    (hEDM : 338000 ≤ lambda) : False := by
  omega

/-- Removing the equality between two scales removes THIS simple
    contradiction; it does not establish that the physics then works. -/
theorem independent_scales_arithmetically_feasible :
    ∃ lam lamCPV : Nat,
      600 ≤ lam ∧ lam ≤ 900 ∧ 338000 ≤ lamCPV := by
  exact ⟨700, 338000, by decide, by decide, by decide⟩

/-- The 2018 leptogenesis example predicts a phase in (198°,225°).
    The PRELIMINARY 2026 Bari best-fit (1.19 pi) is 214.2 degrees.
    Inclusion of a BEST FIT is not evidence for the unique mechanism. -/
theorem cp_phase_best_fit_in_predicted_interval :
    (1980 ≤ 2142 ∧ 2142 ≤ 2250) := by decide

/-- A purely hypothetical future 240 plus or minus 5 degree tight result
    would be disjoint from this particular 198-225 degree prediction.
    No such future measurement is being claimed. -/
theorem hypothetical_phase_disjoint (p : Nat)
    (model : 198 ≤ p ∧ p ≤ 225)
    (future : 235 ≤ p ∧ p ≤ 245) : False := by
  omega

/-- Bari preliminary 2026.a central oscillation values:
    delta m^2 = m2^2-m1^2 = 0.00007465 eV^2,
    Delta m^2 = m3^2-(m1^2+m2^2)/2 = 0.0024720 eV^2.
    sin^2(theta12)=0.3047, sin^2(theta13)=0.02218.
    The mass-squared additive term in meV^2 is exactly
    77.89818043610 for these decimal input constants.
    Scaling by 10^11 keeps the arithmetic integer exact. -/
def betaSquaredMeVScaled (lightestMeV : Nat) : Nat :=
  lightestMeV * lightestMeV * 100000000000 + 7789818043610

/-- For the restricted published 2018 lightest-mass interval,
    m1 in {2,3,4} meV, 9.049 < m_beta < 9.691 meV.
    This is an arithmetic bound on central-input approximations. -/
theorem corrected_beta_bounds (m1 : Nat)
    (hrange : m1 = 2 ∨ m1 = 3 ∨ m1 = 4) :
    (9049*9049)*100000000000 <
      1000000 * betaSquaredMeVScaled m1 ∧
    1000000 * betaSquaredMeVScaled m1 <
      (9691*9691)*100000000000 := by
  rcases hrange with h | h | h
  · subst m1; decide
  · subst m1; decide
  · subst m1; decide

/-- A simplified upper-bound threshold of 40 meV is above every
    m_beta in this narrow model interval. This is NOT a validated
    Project 8 instrument response or sensitivity forecast. -/
theorem beta_below_40_meV (m1 : Nat)
    (hrange : m1 = 2 ∨ m1 = 3 ∨ m1 = 4) :
    betaSquaredMeVScaled m1 < 40*40*100000000000 := by
  rcases hrange with h | h | h
  · subst m1; decide
  · subst m1; decide
  · subst m1; decide

/-- Same source-limited coarse observations can be compatible with
    multiple candidate mechanisms. The second candidate's full physical
    predictions are NOT claimed to have been computed here. -/
def trueMechanism (w : Fin 2) (a : Fin 2) : Prop := w = a
def onlyCoarseConstraints (_w : Fin 2) : Bool := true

theorem no_unique_mechanism_from_coarse_constraints :
    ¬ Safe trueMechanism onlyCoarseConstraints := by
  apply collision_forces_refusal trueMechanism onlyCoarseConstraints
      (0 : Fin 2) (1 : Fin 2)
  · rfl
  · intro a h
    have h0 : (0 : Fin 2) = a := h.1
    have h1 : (1 : Fin 2) = a := h.2
    have hc : (0 : Fin 2) = (1 : Fin 2) := h0.trans h1.symm
    exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) hc

end INSACERMO.PublishedBaryogenesisConstraints
