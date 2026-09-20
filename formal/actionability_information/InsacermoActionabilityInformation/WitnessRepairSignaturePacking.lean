import InsacermoActionabilityInformation.RepairDiversityDimension

namespace InsacermoActionabilityInformation
namespace WitnessRepairSignaturePacking

open FractureObstructionRepairBound

/-- A finite witness system equipped with the set of repair atoms needed to
restore each concrete witness after a transformation. -/
structure WitnessRepairSystem
    (F W I : Type*) [DecidableEq W] [DecidableEq I] where
  witnesses : F → Finset W
  signature : W → Finset I

namespace WitnessRepairSystem

variable {F W I : Type*} [DecidableEq W] [DecidableEq I]

/-- A repair support H restores future F when at least one pre-fracture witness
has all of its required restoration atoms contained in H. -/
def Restores
    (M : WitnessRepairSystem F W I)
    (future : F)
    (H : Finset I) : Prop :=
  ∃ w, w ∈ M.witnesses future ∧ M.signature w ⊆ H

/-- Union of all atoms appearing in a witness-derived restoration signature for
a future. -/
def RepairUniverse
    (M : WitnessRepairSystem F W I)
    (future : F) : Finset I :=
  (M.witnesses future).biUnion M.signature

theorem signature_subset_repairUniverse
    (M : WitnessRepairSystem F W I)
    {future : F} {w : W}
    (hw : w ∈ M.witnesses future) :
    M.signature w ⊆ M.RepairUniverse future := by
  intro i hi
  exact Finset.mem_biUnion.mpr ⟨w, hw, hi⟩

/-- A family P is witness-repair-disjoint when the complete restoration
universes of distinct futures in P are disjoint. -/
def RepairUniversePacking
    [DecidableEq F]
    (M : WitnessRepairSystem F W I)
    (P : Finset F) : Prop :=
  (P : Set F).PairwiseDisjoint M.RepairUniverse

/-- Every concrete witness restoring a future costs at least floor(future). -/
def WitnessCostFloor
    (M : WitnessRepairSystem F W I)
    (atomCost : I → Nat)
    (floor : F → Nat)
    (future : F) : Prop :=
  ∀ w, w ∈ M.witnesses future →
    floor future ≤ SelectionCost atomCost (M.signature w)

/-- WITNESS-DERIVED PACKING LOWER BOUND.
For a set P of futures whose complete repair universes are pairwise disjoint,
any single repair support H restoring every future in P costs at least the sum
of the per-future witness-cost floors.

This theorem starts from concrete pre-fracture witnesses and their restoration
signatures; it does not assume an obstruction-capability hypergraph as input.
-/
theorem packing_lower_bound
    [DecidableEq F]
    (M : WitnessRepairSystem F W I)
    (atomCost : I → Nat)
    (floor : F → Nat)
    (P : Finset F)
    (hpack : M.RepairUniversePacking P)
    (hlower : ∀ future, future ∈ P →
      M.WitnessCostFloor atomCost floor future)
    (H : Finset I)
    (hrestore : ∀ future, future ∈ P → M.Restores future H) :
    (∑ future ∈ P, floor future) ≤ SelectionCost atomCost H := by
  classical

  let pick : (future : F) → future ∈ P → W :=
    fun future hfuture => Classical.choose (hrestore future hfuture)

  have hpick_spec :
      ∀ future (hfuture : future ∈ P),
        pick future hfuture ∈ M.witnesses future ∧
        M.signature (pick future hfuture) ⊆ H := by
    intro future hfuture
    exact Classical.choose_spec (hrestore future hfuture)

  let S : F → Finset I := fun future =>
    if hfuture : future ∈ P then M.signature (pick future hfuture) else ∅

  have hS_eq :
      ∀ future (hfuture : future ∈ P),
        S future = M.signature (pick future hfuture) := by
    intro future hfuture
    simp [S, hfuture]

  have hS_sub_universe :
      ∀ future, future ∈ P → S future ⊆ M.RepairUniverse future := by
    intro future hfuture
    rw [hS_eq future hfuture]
    exact M.signature_subset_repairUniverse (hpick_spec future hfuture).1

  have hS_pairwise :
      (P : Set F).PairwiseDisjoint S := by
    intro f hf g hg hfg
    exact (hpack hf hg hfg).mono
      (hS_sub_universe f hf)
      (hS_sub_universe g hg)

  let U : Finset I := P.biUnion S

  have hU_sub_H : U ⊆ H := by
    intro i hi
    rcases Finset.mem_biUnion.mp hi with ⟨future, hfuture, hiS⟩
    rw [hS_eq future hfuture] at hiS
    exact (hpick_spec future hfuture).2 hiS

  have hsum_floor :
      (∑ future ∈ P, floor future) ≤
        ∑ future ∈ P, SelectionCost atomCost (S future) := by
    apply Finset.sum_le_sum
    intro future hfuture
    rw [hS_eq future hfuture]
    exact hlower future hfuture (pick future hfuture) (hpick_spec future hfuture).1

  have hsum_signatures :
      (∑ future ∈ P, SelectionCost atomCost (S future)) =
        SelectionCost atomCost U := by
    unfold SelectionCost
    dsimp [U]
    symm
    exact Finset.sum_biUnion hS_pairwise

  have hU_cost_le :
      SelectionCost atomCost U ≤ SelectionCost atomCost H := by
    unfold SelectionCost
    exact Finset.sum_le_sum_of_subset hU_sub_H

  exact hsum_floor.trans (hsum_signatures.trans_le hU_cost_le)

/-- Unit-cost corollary: if every witness for every packed future needs at
least one restoration atom, then any global repair uses at least |P| atoms. -/
theorem packing_card_lower_bound
    [DecidableEq F]
    (M : WitnessRepairSystem F W I)
    (P : Finset F)
    (hpack : M.RepairUniversePacking P)
    (hne : ∀ future, future ∈ P →
      ∀ w, w ∈ M.witnesses future → (M.signature w).Nonempty)
    (H : Finset I)
    (hrestore : ∀ future, future ∈ P → M.Restores future H) :
    P.card ≤ H.card := by
  have hlower :
      ∀ future, future ∈ P →
        M.WitnessCostFloor (fun _ : I => 1) (fun _ : F => 1) future := by
    intro future hfuture w hw
    have hpos : 1 ≤ (M.signature w).card :=
      Finset.one_le_card.mpr (hne future hfuture w hw)
    simpa [WitnessCostFloor, SelectionCost] using hpos

  have h :=
    packing_lower_bound
      M (fun _ : I => 1) (fun _ : F => 1)
      P hpack hlower H hrestore
  simpa [SelectionCost] using h

/-- If k packed futures each have witness-restoration cost at least c, then
every common repair costs at least k*c. -/
theorem uniform_packing_lower_bound
    [DecidableEq F]
    (M : WitnessRepairSystem F W I)
    (atomCost : I → Nat)
    (P : Finset F)
    (c : Nat)
    (hpack : M.RepairUniversePacking P)
    (hlower : ∀ future, future ∈ P →
      M.WitnessCostFloor atomCost (fun _ : F => c) future)
    (H : Finset I)
    (hrestore : ∀ future, future ∈ P → M.Restores future H) :
    P.card * c ≤ SelectionCost atomCost H := by
  have h :=
    packing_lower_bound
      M atomCost (fun _ : F => c) P hpack hlower H hrestore
  simpa [Finset.sum_const_nat] using h

end WitnessRepairSystem
end WitnessRepairSignaturePacking
end InsacermoActionabilityInformation
