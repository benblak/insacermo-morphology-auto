import InsacermoActionabilityInformation.FutureDamageCompositionLaw
import InsacermoActionabilityInformation.FutureRepairPrice

namespace InsacermoActionabilityInformation
namespace FirstFractureRepairLaw

open FutureDepthSpectrum
open FutureTransformationCalculus
open FutureTransformationComposition
open FutureDamageCompositionLaw
open EventualFutureGeometry
open FutureRepairPrice

/-- A finite chain of depth spectra is pointwise non-improving when every
adjacent step can only preserve or worsen depth. -/
def ChainNonImproving
    (d : Nat → DepthValue) (n : Nat) : Prop :=
  ∀ i, i < n → DepthLe (d i) (d (i + 1))

/-- A fracture occurs at step i when a finite future depth becomes infinite. -/
def FractureAt
    (d : Nat → DepthValue) (i : Nat) : Prop :=
  Destroyed (d i) (d (i + 1))

/-- If a non-improving chain starts finite and ends infinite, some adjacent
decision step destroys the future. -/
theorem chain_destruction_localizes
    (d : Nat → DepthValue) :
    ∀ n,
      ChainNonImproving d n →
      (∃ a, d 0 = .finite a) →
      d n = .infinite →
      ∃ i, i < n ∧ FractureAt d i := by
  intro n
  induction n with
  | zero =>
      intro _ h0 hn
      rcases h0 with ⟨a, hfin⟩
      rw [hfin] at hn
      contradiction
  | succ n ih =>
      intro hchain h0 hend
      cases hn : d n with
      | finite k =>
          refine ⟨n, Nat.lt_succ_self n, ?_⟩
          unfold FractureAt
          exact ⟨k, hn, by simpa using hend⟩
      | infinite =>
          have hprefix : ChainNonImproving d n := by
            intro i hi
            exact hchain i (Nat.lt_trans hi (Nat.lt_succ_self n))
          exact ih hprefix h0 hn

/-- There exists at least one fracture index under the hypotheses of the
localization theorem. -/
def HasFracture
    (d : Nat → DepthValue) (n : Nat) : Prop :=
  ∃ i, i < n ∧ FractureAt d i

/-- The first fracture index is the least adjacent step that destroys the
future. -/
noncomputable def FirstFractureIndex
    (d : Nat → DepthValue) (n : Nat)
    (h : HasFracture d n) : Nat :=
  Nat.find h

/-- The first fracture index is indeed a destructive step inside the chain. -/
theorem firstFractureIndex_spec
    (d : Nat → DepthValue) (n : Nat)
    (h : HasFracture d n) :
    FirstFractureIndex d n h < n ∧
      FractureAt d (FirstFractureIndex d n h) := by
  exact Nat.find_spec h

/-- No earlier adjacent decision step destroys the future. -/
theorem no_fracture_before_first
    (d : Nat → DepthValue) (n : Nat)
    (h : HasFracture d n) :
    ∀ j, j < FirstFractureIndex d n h → ¬ FractureAt d j := by
  intro j hj hfj
  have hjn : j < n := by
    exact Nat.lt_trans hj (firstFractureIndex_spec d n h).1
  have hle : FirstFractureIndex d n h ≤ j := by
    exact Nat.find_min' h ⟨hjn, hfj⟩
  exact (Nat.not_le_of_gt hj) hle

/-- The first fracture index is unique as the least destructive step. -/
theorem firstFractureIndex_unique_minimal
    (d : Nat → DepthValue) (n : Nat)
    (h : HasFracture d n)
    {i : Nat}
    (hi : i < n ∧ FractureAt d i)
    (hminimal : ∀ j, j < i → ¬ FractureAt d j) :
    i = FirstFractureIndex d n h := by
  have hfirst_le_i : FirstFractureIndex d n h ≤ i :=
    Nat.find_min' h hi
  have hi_le_first : i ≤ FirstFractureIndex d n h := by
    by_contra hnot
    have hlt : FirstFractureIndex d n h < i := Nat.lt_of_not_ge hnot
    exact hminimal (FirstFractureIndex d n h) hlt
      (firstFractureIndex_spec d n h).2
  exact Nat.le_antisymm hi_le_first hfirst_le_i

/-- Concrete n-step corollary: if a bundle is finite initially, infinite
finally, and every adjacent spectrum transformation is non-improving, then
there is a unique least decision step where the bundle is destroyed. -/
theorem spectrum_chain_has_unique_first_fracture
    {Q : Type*}
    (s : Nat → Finset Q → DepthValue)
    (n : Nat)
    (hchain : ∀ i, i < n → SpectrumNonImproving (s i) (s (i + 1)))
    (F : Finset Q)
    (hstart : ∃ a, s 0 F = .finite a)
    (hend : s n F = .infinite) :
    ∃ i, i < n ∧ FractureAt (fun k => s k F) i ∧
      ∀ j, j < i → ¬ FractureAt (fun k => s k F) j := by
  let d : Nat → DepthValue := fun k => s k F
  have hdepthChain : ChainNonImproving d n := by
    intro i hi
    exact hchain i hi F
  have hfract : HasFracture d n :=
    chain_destruction_localizes d n hdepthChain hstart hend
  let i := FirstFractureIndex d n hfract
  refine ⟨i, (firstFractureIndex_spec d n hfract).1,
    (firstFractureIndex_spec d n hfract).2, ?_⟩
  exact no_fracture_before_first d n hfract

/-- Any concrete repair that restores eventual recoverability immediately
after a destructive step is a genuine creation event from infinity to finite
depth in the master spectrum. -/
theorem repair_after_destruction_is_creation
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → Nat}
    {xBefore xAfter : X} {F : Finset Q} {r : Repair}
    (hdestr :
      Destroyed
        (Spectrum Avail Step xBefore F)
        (Spectrum Avail Step xAfter F))
    (hrepair :
      (EventualFutureComplex Avail Step (applyRepair r xAfter)).feasible F) :
    Created
      (Spectrum Avail Step xAfter F)
      (Spectrum Avail Step (applyRepair r xAfter) F) := by
  rcases hdestr with ⟨d, _, hafterInf⟩
  have hfinite :
      ∃ e, Spectrum Avail Step (applyRepair r xAfter) F = .finite e :=
    (eventualFutureComplex_feasible_iff_spectrum_finite).1 hrepair
  rcases hfinite with ⟨e, he⟩
  exact ⟨e, hafterInf, he⟩

/-- Therefore every successful repair after destruction is necessarily a
strict spectrum improvement (an acceleration from infinity to finite depth). -/
theorem repair_after_destruction_is_strict_improvement
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → Nat}
    {xBefore xAfter : X} {F : Finset Q} {r : Repair}
    (hdestr :
      Destroyed
        (Spectrum Avail Step xBefore F)
        (Spectrum Avail Step xAfter F))
    (hrepair :
      (EventualFutureComplex Avail Step (applyRepair r xAfter)).feasible F) :
    Accelerated
      (Spectrum Avail Step xAfter F)
      (Spectrum Avail Step (applyRepair r xAfter) F) := by
  exact created_implies_accelerated
    (repair_after_destruction_is_creation hdestr hrepair)

/-- The exact eventual repair price after destruction is a certified lower
bound on the cost of every repair that restores the destroyed future. -/
theorem repair_price_lower_bounds_every_successful_repair
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → Nat}
    {xAfter : X} {F : Finset Q}
    (hHas : HasEventualRepair Avail Step applyRepair cost xAfter F)
    {r : Repair}
    (hr : (EventualFutureComplex Avail Step (applyRepair r xAfter)).feasible F) :
    EventualRepairPrice Avail Step applyRepair cost xAfter F hHas ≤ cost r := by
  apply eventualRepairPrice_minimal hHas
  exact ⟨r, Nat.le_refl _, hr⟩

end FirstFractureRepairLaw
end InsacermoActionabilityInformation
