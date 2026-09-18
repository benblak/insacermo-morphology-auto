import InsacermoActionabilityInformation.FutureDepthSpectrum

namespace InsacermoActionabilityInformation

namespace FutureTransformationCalculus

open FutureDepthSpectrum

/-- Strict order on extended future depths. Every finite depth is strictly
below infinity; infinity is never strictly below anything. -/
def DepthLt : DepthValue → DepthValue → Prop
  | .finite d, .finite e => d < e
  | .finite _, .infinite => True
  | .infinite, .finite _ => False
  | .infinite, .infinite => False

/-- A future bundle is preserved when its depth is unchanged. -/
def Preserved (before after : DepthValue) : Prop := before = after

/-- A future bundle is accelerated/facilitated when its post-transformation
depth is strictly smaller than its pre-transformation depth. -/
def Accelerated (before after : DepthValue) : Prop := DepthLt after before

/-- A future bundle is delayed when its post-transformation depth is strictly
larger than its pre-transformation depth. -/
def Delayed (before after : DepthValue) : Prop := Accelerated after before

/-- A previously finite future becomes jointly irreversible. -/
def Destroyed (before after : DepthValue) : Prop :=
  ∃ d : ℕ, before = .finite d ∧ after = .infinite

/-- A previously jointly irreversible future becomes finitely recoverable. -/
def Created (before after : DepthValue) : Prop :=
  ∃ d : ℕ, before = .infinite ∧ after = .finite d

/-- At horizon H, a threshold gain means the future was unavailable before
but is available after the transformation. -/
def ThresholdGain (before after : DepthValue) (H : ℕ) : Prop :=
  ¬ DepthAtMost before H ∧ DepthAtMost after H

/-- At horizon H, a threshold loss means the future was available before but
is unavailable after the transformation. -/
def ThresholdLoss (before after : DepthValue) (H : ℕ) : Prop :=
  ThresholdGain after before H

/-- On finite depths, acceleration is exactly strict numerical depth decrease. -/
theorem finite_accelerated_iff {dBefore dAfter : ℕ} :
    Accelerated (.finite dBefore) (.finite dAfter) ↔ dAfter < dBefore := by
  rfl

/-- On finite depths, delay is exactly strict numerical depth increase. -/
theorem finite_delayed_iff {dBefore dAfter : ℕ} :
    Delayed (.finite dBefore) (.finite dAfter) ↔ dBefore < dAfter := by
  rfl

/-- Creation is an extreme acceleration from infinity to a finite depth. -/
theorem created_implies_accelerated
    {before after : DepthValue}
    (h : Created before after) :
    Accelerated before after := by
  rcases h with ⟨d, hbefore, hafter⟩
  subst before
  subst after
  simp [Accelerated, DepthLt]

/-- Destruction is an extreme delay from finite depth to infinity. -/
theorem destroyed_implies_delayed
    {before after : DepthValue}
    (h : Destroyed before after) :
    Delayed before after := by
  rcases h with ⟨d, hbefore, hafter⟩
  subst before
  subst after
  simp [Delayed, Accelerated, DepthLt]

/-- Creation necessarily creates a finite horizon at which availability is
gained. -/
theorem created_has_threshold_gain
    {before after : DepthValue}
    (h : Created before after) :
    ∃ H, ThresholdGain before after H := by
  rcases h with ⟨d, hbefore, hafter⟩
  subst before
  subst after
  refine ⟨d, ?_⟩
  simp [ThresholdGain, DepthAtMost]

/-- Destruction necessarily creates a finite horizon at which availability is
lost. -/
theorem destroyed_has_threshold_loss
    {before after : DepthValue}
    (h : Destroyed before after) :
    ∃ H, ThresholdLoss before after H := by
  rcases h with ⟨d, hbefore, hafter⟩
  subst before
  subst after
  refine ⟨d, ?_⟩
  simp [ThresholdLoss, ThresholdGain, DepthAtMost]

/-- A strict acceleration is exactly the existence of at least one finite
horizon threshold crossing from unavailable to available. -/
theorem accelerated_iff_exists_thresholdGain
    {before after : DepthValue} :
    Accelerated before after ↔ ∃ H, ThresholdGain before after H := by
  cases before with
  | finite dBefore =>
      cases after with
      | finite dAfter =>
          constructor
          · intro h
            change dAfter < dBefore at h
            refine ⟨dAfter, ?_⟩
            constructor
            · change ¬ dBefore ≤ dAfter
              exact Nat.not_le_of_gt h
            · change dAfter ≤ dAfter
              exact Nat.le_refl dAfter
          · rintro ⟨H, hnot, hyes⟩
            change ¬ dBefore ≤ H at hnot
            change dAfter ≤ H at hyes
            change dAfter < dBefore
            exact Nat.lt_of_le_of_lt hyes (Nat.lt_of_not_ge hnot)
      | infinite =>
          constructor
          · intro h
            change False at h
            contradiction
          · rintro ⟨H, _, hyes⟩
            change False at hyes
            contradiction
  | infinite =>
      cases after with
      | finite dAfter =>
          constructor
          · intro _
            refine ⟨dAfter, ?_⟩
            simp [ThresholdGain, DepthAtMost]
          · intro _
            simp [Accelerated, DepthLt]
      | infinite =>
          constructor
          · intro h
            change False at h
            contradiction
          · rintro ⟨H, hnot, hyes⟩
            change False at hyes
            contradiction

/-- A strict delay is exactly the existence of at least one finite horizon
threshold crossing from available to unavailable. -/
theorem delayed_iff_exists_thresholdLoss
    {before after : DepthValue} :
    Delayed before after ↔ ∃ H, ThresholdLoss before after H := by
  simpa [Delayed, ThresholdLoss] using
    (accelerated_iff_exists_thresholdGain (before := after) (after := before))

/-- Preservation means every finite-horizon availability answer is unchanged. -/
theorem preserved_implies_all_thresholds_equal
    {before after : DepthValue}
    (h : Preserved before after) :
    ∀ H, DepthAtMost before H ↔ DepthAtMost after H := by
  intro H
  unfold Preserved at h
  subst after
  exact Iff.rfl

/-- The three strict/equality outcomes exhaust every depth transformation. -/
theorem transformation_trichotomy (before after : DepthValue) :
    Preserved before after ∨ Accelerated before after ∨ Delayed before after := by
  cases before with
  | finite dBefore =>
      cases after with
      | finite dAfter =>
          rcases lt_trichotomy dAfter dBefore with hlt | heq | hgt
          · exact Or.inr (Or.inl (by
              change dAfter < dBefore
              exact hlt))
          · subst dAfter
            exact Or.inl rfl
          · exact Or.inr (Or.inr (by
              change dBefore < dAfter
              exact hgt))
      | infinite =>
          exact Or.inr (Or.inr (by
            simp [Delayed, Accelerated, DepthLt]))
  | infinite =>
      cases after with
      | finite dAfter =>
          exact Or.inr (Or.inl (by
            simp [Accelerated, DepthLt]))
      | infinite =>
          exact Or.inl rfl

/-- Extended-depth monotonicity implies horizon-sublevel monotonicity. -/
theorem depthAtMost_of_depthLe
    {a b : DepthValue} {H : ℕ}
    (hab : DepthLe a b)
    (hb : DepthAtMost b H) :
    DepthAtMost a H := by
  cases a with
  | finite da =>
      cases b with
      | finite db =>
          change da ≤ db at hab
          change db ≤ H at hb
          change da ≤ H
          exact Nat.le_trans hab hb
      | infinite =>
          change False at hb
          contradiction
  | infinite =>
      cases b with
      | finite db =>
          change False at hab
          contradiction
      | infinite =>
          change False at hb
          contradiction

/-- A whole future-depth spectrum is non-worsening when no finite bundle gets
deeper after transformation. This permits preservation, acceleration and
creation, but excludes delay and destruction. -/
def SpectrumNonWorsening {Q : Type*}
    (before after : Finset Q → DepthValue) : Prop :=
  ∀ F, DepthLe (after F) (before F)

/-- A whole future-depth spectrum is non-improving when no finite bundle gets
shallower after transformation. -/
def SpectrumNonImproving {Q : Type*}
    (before after : Finset Q → DepthValue) : Prop :=
  ∀ F, DepthLe (before F) (after F)

/-- Spectrum equality: every finite future bundle keeps exactly the same depth. -/
def SpectrumEquivalent {Q : Type*}
    (before after : Finset Q → DepthValue) : Prop :=
  ∀ F, before F = after F

/-- Under a non-worsening transformation, anything available by horizon H
before remains available by H after. -/
theorem nonWorsening_preserves_horizon_availability
    {Q : Type*}
    {before after : Finset Q → DepthValue}
    (h : SpectrumNonWorsening before after)
    {F : Finset Q} {H : ℕ}
    (hbefore : DepthAtMost (before F) H) :
    DepthAtMost (after F) H := by
  exact depthAtMost_of_depthLe (h F) hbefore

/-- Under a non-improving transformation, anything available after by horizon
H was already available before by H. -/
theorem nonImproving_reflects_horizon_availability
    {Q : Type*}
    {before after : Finset Q → DepthValue}
    (h : SpectrumNonImproving before after)
    {F : Finset Q} {H : ℕ}
    (hafter : DepthAtMost (after F) H) :
    DepthAtMost (before F) H := by
  exact depthAtMost_of_depthLe (h F) hafter

end FutureTransformationCalculus

end InsacermoActionabilityInformation
