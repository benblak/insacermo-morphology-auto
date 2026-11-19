import Lean

namespace INSACERMO.RefusEspoir

universe u v o

/-- A single choice of action for each observation, robust in every declared world. -/
def Safe {W : Type u} {A : Type v} {O : Type o}
    (R : W → A → Prop) (obs : W → O) : Prop :=
  ∃ policy : O → A, ∀ w : W, R w (policy (obs w))

/-- Every nonempty observation fibre has a common admissible action. -/
def FibresAdmitAction {W : Type u} {A : Type v} {O : Type o}
    (R : W → A → Prop) (obs : W → O) : Prop :=
  ∀ z : O, (∃ w : W, obs w = z) →
    ∃ a : A, ∀ w : W, obs w = z → R w a

/-- Exact observational criterion with unrestricted observation-conditioned policies. -/
theorem safe_iff_fibres {W : Type u} {A : Type v} {O : Type o}
    [Nonempty A] (R : W → A → Prop) (obs : W → O) :
    Safe R obs ↔ FibresAdmitAction R obs := by
  constructor
  · intro hs z _
    obtain ⟨policy, hp⟩ := hs
    refine ⟨policy z, ?_⟩
    intro w hw
    simpa [hw] using hp w
  · intro hf
    classical
    have hpick : ∀ z : O, ∃ a : A, ∀ w : W, obs w = z → R w a := by
      intro z
      by_cases hz : ∃ w : W, obs w = z
      · exact hf z hz
      · refine ⟨Classical.choice (inferInstance : Nonempty A), ?_⟩
        intro w hw
        exact False.elim (hz ⟨w, hw⟩)
    refine ⟨fun z => Classical.choose (hpick z), ?_⟩
    intro w
    exact Classical.choose_spec (hpick (obs w)) w rfl

/-- Identical observations and incompatible actions block every policy. -/
theorem collision_forces_refusal {W : Type u} {A : Type v} {O : Type o}
    (R : W → A → Prop) (obs : W → O) (w₀ w₁ : W)
    (heq : obs w₀ = obs w₁)
    (hbad : ∀ a : A, ¬ (R w₀ a ∧ R w₁ a)) :
    ¬ Safe R obs := by
  intro hs
  obtain ⟨policy, hp⟩ := hs
  apply hbad (policy (obs w₀))
  constructor
  · exact hp w₀
  · simpa [heq] using hp w₁

/-- When a world has no admissible action, observations alone cannot help. -/
theorem impossible_world_forces_refusal {W : Type u} {A : Type v} {O : Type o}
    (R : W → A → Prop) (obs : W → O)
    (hbad : ∃ w : W, ∀ a : A, ¬ R w a) :
    ¬ Safe R obs := by
  intro hs
  obtain ⟨policy, hp⟩ := hs
  obtain ⟨w, hw⟩ := hbad
  exact hw (policy (obs w)) (hp w)

/-- Perfect information is sufficient iff each world has some valid action. -/
theorem full_information_criterion {W : Type u} {A : Type v}
    (R : W → A → Prop) :
    Safe R (fun w : W => w) ↔ ∀ w : W, ∃ a : A, R w a := by
  constructor
  · intro hs w
    obtain ⟨policy, hp⟩ := hs
    exact ⟨policy w, hp w⟩
  · intro hw
    classical
    exact ⟨fun w => Classical.choose (hw w),
      fun w => Classical.choose_spec (hw w)⟩

/-- Strongest observation-only no-go when an identity probe is allowed.
    This does NOT forbid new actions, repairs or stronger models. -/
theorem perfect_information_refusal_iff_missing_capacity
    {W : Type u} {A : Type v} (R : W → A → Prop) :
    (¬ Safe R (fun w : W => w)) ↔
      ∃ w : W, ∀ a : A, ¬ R w a := by
  classical
  constructor
  · intro h
    by_cases hx : ∃ w : W, ∀ a : A, ¬ R w a
    · exact hx
    · have hall : ∀ w : W, ∃ a : A, R w a := by
        intro w
        by_cases ha : ∃ a : A, R w a
        · exact ha
        · exact False.elim (hx ⟨w, fun a hwa => ha ⟨a, hwa⟩⟩)
      exact False.elim (h ((full_information_criterion R).2 hall))
  · intro h
    exact impossible_world_forces_refusal R (fun w => w) h

def exampleGood (w : Fin 4) (a : Fin 3) : Prop := w.val % 2 = a.val
def sensorBlock (w : Fin 4) : Bool := decide (2 ≤ w.val)
def sensorParity (w : Fin 4) : Bool := decide (w.val % 2 = 1)

theorem first_sensor_refused : ¬ Safe exampleGood sensorBlock := by
  apply collision_forces_refusal exampleGood sensorBlock (0 : Fin 4) (1 : Fin 4)
  · decide
  · intro a h
    have h0 : (0 : Nat) = a.val := by simpa [exampleGood] using h.1
    have h1 : (1 : Nat) = a.val := by simpa [exampleGood] using h.2
    exact Nat.zero_ne_one (h0.trans h1.symm)

theorem second_sensor_lifts_refusal :
    Safe exampleGood (fun w => (sensorBlock w, sensorParity w)) := by
  refine ⟨fun z => if z.2 then (1 : Fin 3) else (0 : Fin 3), ?_⟩
  intro w
  rcases w with ⟨n, hn⟩
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · subst n; simp [exampleGood, sensorParity, sensorBlock]
  · subst n; simp [exampleGood, sensorParity, sensorBlock]
  · subst n; simp [exampleGood, sensorParity, sensorBlock]
  · subst n; simp [exampleGood, sensorParity, sensorBlock]

def impossibleGood (w : Fin 4) (a : Fin 3) : Prop :=
  w.val ≠ 1 ∧ w.val % 3 = a.val

theorem no_sensor_can_fix_missing_action {O : Type o}
    (obs : Fin 4 → O) : ¬ Safe impossibleGood obs := by
  apply impossible_world_forces_refusal impossibleGood obs
  refine ⟨(1 : Fin 4), ?_⟩
  intro a h
  exact h.1 rfl

end INSACERMO.RefusEspoir
