import Std

/-!
INSACERMO MAX DUAL CERTIFICATE V1 (2026-10-10).
A carefully delimited Lean projection of a 3-control coupled linear synthesis
example, its exact scaled repair, and its information impossibility boundary.
This is NOT a proof of the generic LP duality formula or the external runtime.
-/
namespace InsacermoMaxDual

/-- Three arbitrary lower bounds and a common upper sum; aggregating the
four inequalities produces a finite rational Farkas-like certificate after
scaling to integer arithmetic. -/
theorem aggregate_certificate
    (u v w r lo1 lo2 lo3 upper : Nat)
    (h1 : lo1 ≤ u + r)
    (h2 : lo2 ≤ v + r)
    (h3 : lo3 ≤ w + r)
    (h4 : u + v + w ≤ upper + r) :
    lo1 + lo2 + lo3 ≤ upper + 4*r := by
  omega

/-- This is a 3-dimensional example with 4 minimal conflicting constraints.
Each variable is scaled by 4. One repair unit represents 1/4 of the original
unscaled uniform relaxation. -/
def Feasible3 (u v w r : Nat) : Prop :=
  4 ≤ u+r ∧ 4 ≤ v+r ∧ 4 ≤ w+r ∧ u+v+w ≤ 8+r

theorem necessity (u v w r : Nat) (h : Feasible3 u v w r) :
    1 ≤ r := by
  rcases h with ⟨h1,h2,h3,h4⟩
  have hc := aggregate_certificate u v w r 4 4 4 8 h1 h2 h3 h4
  omega

/-- A directly constructed witness attains the bound. -/
theorem sufficient (r : Nat) (h : 1 ≤ r) :
    ∃ u v w : Nat, Feasible3 u v w r := by
  refine ⟨3, 3, 3, ?_⟩
  unfold Feasible3
  omega

theorem exact_minimal_repair (r : Nat) :
    (∃ u v w : Nat, Feasible3 u v w r) ↔ 1 ≤ r := by
  constructor
  · rintro ⟨u,v,w,h⟩
    exact necessity u v w r h
  · exact sufficient r

theorem no_zero_repair : ¬ ∃ u v w : Nat, Feasible3 u v w 0 := by
  intro h
  exact (Nat.not_succ_le_zero 0) ((exact_minimal_repair 0).mp h)

/-- All 4 leave-one-out subsystems have explicit witnesses. -/
theorem each_triple_feasible :
    (∃ u v w : Nat, 4 ≤ v ∧ 4 ≤ w ∧ u+v+w ≤ 8) ∧
    (∃ u v w : Nat, 4 ≤ u ∧ 4 ≤ w ∧ u+v+w ≤ 8) ∧
    (∃ u v w : Nat, 4 ≤ u ∧ 4 ≤ v ∧ u+v+w ≤ 8) ∧
    (∃ u v w : Nat, 4 ≤ u ∧ 4 ≤ v ∧ 4 ≤ w) := by
  constructor
  · exact ⟨0,4,4,by omega⟩
  constructor
  · exact ⟨4,0,4,by omega⟩
  constructor
  · exact ⟨4,4,0,by omega⟩
  · exact ⟨4,4,4,by omega⟩

/-- With indistinguishable worlds demanding opposite fixed controls, no
single controller can guarantee both. More laws or informative observations
are necessary for any stronger existential claim. -/
theorem identical_observations_cannot_select_opposites :
    ¬ ∃ control : Nat, control = 0 ∧ control = 1 := by
  rintro ⟨control,h0,h1⟩
  omega

theorem distinguishing_observation_allows_branch_controls :
    (∃ control : Nat, control = 0) ∧
    (∃ control : Nat, control = 1) := by
  exact ⟨⟨0,rfl⟩,⟨1,rfl⟩⟩

end InsacermoMaxDual
