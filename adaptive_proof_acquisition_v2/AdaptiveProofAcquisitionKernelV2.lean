import Lean.Elab.Tactic.Omega

namespace INSACERMO.AdaptiveProofAcquisitionV2

def proofDeficit (rho U : Nat) : Nat :=
  if U < rho then 0 else U - rho + 1

theorem proof_deficit_zero_iff (rho U : Nat) :
    proofDeficit rho U = 0 ↔ U < rho := by
  unfold proofDeficit
  split <;> omega

def binaryResidualDeficit (rho U₀ U₁ : Nat) : Nat :=
  Nat.max (proofDeficit rho U₀) (proofDeficit rho U₁)

theorem binary_probe_guarantees_act_iff
    (rho U₀ U₁ : Nat) :
    binaryResidualDeficit rho U₀ U₁ = 0 ↔
      U₀ < rho ∧ U₁ < rho := by
  unfold binaryResidualDeficit
  constructor
  · intro h
    have h0 : proofDeficit rho U₀ = 0 := by
      have : proofDeficit rho U₀ ≤ Nat.max (proofDeficit rho U₀) (proofDeficit rho U₁) :=
        Nat.le_max_left _ _
      omega
    have h1 : proofDeficit rho U₁ = 0 := by
      have : proofDeficit rho U₁ ≤ Nat.max (proofDeficit rho U₀) (proofDeficit rho U₁) :=
        Nat.le_max_right _ _
      omega
    exact ⟨(proof_deficit_zero_iff rho U₀).1 h0,
           (proof_deficit_zero_iff rho U₁).1 h1⟩
  · intro h
    have h0 := (proof_deficit_zero_iff rho U₀).2 h.1
    have h1 := (proof_deficit_zero_iff rho U₁).2 h.2
    simp [binaryResidualDeficit, h0, h1]

inductive Decision where
  | act
  | refuse
deriving DecidableEq

inductive CertTree where
  | act (upperBound : Nat)
  | refuse
  | probe (left right : CertTree)

def SafeDecision (D rho : Nat) : Decision → Prop
  | .act => D < rho
  | .refuse => True

def TreeSound (D rho : Nat) : CertTree → Prop
  | .act U => D ≤ U ∧ U < rho
  | .refuse => True
  | .probe l r => TreeSound D rho l ∧ TreeSound D rho r

def execute : CertTree → List Bool → Decision
  | .act _, _ => .act
  | .refuse, _ => .refuse
  | .probe _ _, [] => .refuse
  | .probe l r, b :: bs =>
      if b then execute r bs else execute l bs

theorem sound_tree_never_unsafe
    (D rho : Nat) (t : CertTree)
    (hs : TreeSound D rho t) :
    ∀ outcomes, SafeDecision D rho (execute t outcomes) := by
  induction t with
  | act U =>
      intro outcomes
      exact Nat.lt_of_le_of_lt hs.1 hs.2
  | refuse =>
      intro outcomes
      trivial
  | probe l r ihl ihr =>
      intro outcomes
      rcases hs with ⟨hl, hr⟩
      cases outcomes with
      | nil =>
          trivial
      | cons b bs =>
          cases b with
          | false =>
              exact ihl hl bs
          | true =>
              exact ihr hr bs

theorem act_leaf_requires_true_safety
    (D rho U : Nat)
    (hbound : D ≤ U)
    (hgate : U < rho) :
    D < rho := by
  exact Nat.lt_of_le_of_lt hbound hgate

theorem coarse_sound_bound_may_block_act
    (D rho U : Nat)
    (htrue : D < rho)
    (hsound : D ≤ U)
    (hcoarse : rho ≤ U) :
    proofDeficit rho U > 0 := by
  unfold proofDeficit
  split
  · omega
  · omega

#print axioms proof_deficit_zero_iff
#print axioms binary_probe_guarantees_act_iff
#print axioms sound_tree_never_unsafe
#print axioms act_leaf_requires_true_safety
#print axioms coarse_sound_bound_may_block_act

end INSACERMO.AdaptiveProofAcquisitionV2
