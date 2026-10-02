namespace INSACERMO.CertifiedOnlineDebtV1

def Safe {X : Type u}
    (bad0 : X → Prop) (d : X → X → Nat) (D : Nat) (x : X) : Prop :=
  ∀ b0, bad0 b0 → D < d x b0

theorem safe_of_certified_upper_bound
    {X : Type u}
    (bad0 badt : X → Prop)
    (d : X → X → Nat)
    (D U : Nat) (x : X)
    (hdebt : ∀ b, badt b → ∃ b0, bad0 b0 ∧ d b b0 ≤ D)
    (hDU : D ≤ U)
    (hreserve : Safe bad0 d U x) :
    ¬ badt x := by
  intro hx
  obtain ⟨b0, hb0, hcloseD⟩ := hdebt x hx
  have hcloseU : d x b0 ≤ U := Nat.le_trans hcloseD hDU
  have hfar : U < d x b0 := hreserve b0 hb0
  exact (Nat.not_lt_of_ge hcloseU) hfar

theorem no_free_debt_observation_only
    {World : Type u} {Obs : Type v}
    (obs : World → Obs)
    (debt : World → Nat)
    (bound : Obs → Nat)
    (x y : World)
    (hobs : obs x = obs y)
    (hhidden : bound (obs x) < debt y) :
    ¬ ∀ w, debt w ≤ bound (obs w) := by
  intro hsound
  have hy : debt y ≤ bound (obs y) := hsound y
  have hb : bound (obs x) = bound (obs y) := congrArg bound hobs
  have hgap : bound (obs y) < debt y := by
    rw [← hb]
    exact hhidden
  exact (Nat.not_lt_of_ge hy) hgap

theorem observation_only_reuse_can_be_unsafe
    {World : Type u} {Obs : Type v}
    (obs : World → Obs)
    (debt : World → Nat)
    (bound : Obs → Nat)
    (rho : Nat)
    (x y : World)
    (hobs : obs x = obs y)
    (hpermit : bound (obs x) < rho)
    (hunsafe : rho ≤ debt y) :
    bound (obs y) < debt y := by
  have hb : bound (obs x) = bound (obs y) := congrArg bound hobs
  have hp : bound (obs y) < rho := by
    rw [← hb]
    exact hpermit
  exact Nat.lt_of_lt_of_le hp hunsafe

structure DebtAuthority
    (World : Type u) (Obs : Type v)
    (obs : World → Obs) (debt : World → Nat) where
  bound : Obs → Nat
  sound : ∀ w, debt w ≤ bound (obs w)

theorem authority_bound_is_true_upper_bound
    {World : Type u} {Obs : Type v}
    (obs : World → Obs) (debt : World → Nat)
    (A : DebtAuthority World Obs obs debt)
    (w : World) :
    debt w ≤ A.bound (obs w) := by
  exact A.sound w

def tighter (u₁ u₂ : Nat) : Nat := if u₁ ≤ u₂ then u₁ else u₂

theorem same_debt_bounds_compose_by_tighter
    {D U₁ U₂ : Nat}
    (h₁ : D ≤ U₁) (h₂ : D ≤ U₂) :
    D ≤ tighter U₁ U₂ := by
  unfold tighter
  split
  · exact h₁
  · exact h₂

theorem component_bounds_add
    {D₁ D₂ U₁ U₂ : Nat}
    (h₁ : D₁ ≤ U₁) (h₂ : D₂ ≤ U₂) :
    D₁ + D₂ ≤ U₁ + U₂ := by
  exact Nat.add_le_add h₁ h₂

theorem iterated_growth_cap
    (debt : Nat → Nat) (g : Nat)
    (hstep : ∀ n, debt (Nat.succ n) ≤ debt n + g) :
    ∀ n, debt n ≤ debt 0 + g * n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        debt (Nat.succ n) ≤ debt n + g := hstep n
        _ ≤ (debt 0 + g * n) + g := Nat.add_le_add_right ih g
        _ = debt 0 + g * Nat.succ n := by
          simp [Nat.mul_succ, Nat.add_assoc]

inductive WitnessWorld where
  | low
  | high
deriving DecidableEq

def witnessObs : WitnessWorld → Nat
  | .low => 0
  | .high => 0

def witnessDebt : WitnessWorld → Nat
  | .low => 4
  | .high => 12

def witnessBound : Nat → Nat
  | _ => 4

theorem finite_no_free_debt_witness :
    ¬ ∀ w, witnessDebt w ≤ witnessBound (witnessObs w) := by
  exact no_free_debt_observation_only
    witnessObs witnessDebt witnessBound .low .high rfl (by decide)

#print axioms safe_of_certified_upper_bound
#print axioms no_free_debt_observation_only
#print axioms observation_only_reuse_can_be_unsafe
#print axioms authority_bound_is_true_upper_bound
#print axioms same_debt_bounds_compose_by_tighter
#print axioms component_bounds_add
#print axioms iterated_growth_cap
#print axioms finite_no_free_debt_witness

end INSACERMO.CertifiedOnlineDebtV1
