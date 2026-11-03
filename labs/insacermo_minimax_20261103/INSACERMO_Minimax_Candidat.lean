import Mathlib

/-!
INSACERMO — independent Lean laboratory, 2026-11-03.
Finite robust minimax optimization. Mathematical, NOT physical.
No modifications to MAX TOTAL/C3 historical sources.
-/

namespace InsacermoMinimax
universe u v
variable {Config : Type u} {World : Type v}

def SafeOn (omega : Finset World) (good : Config → World → Prop) (c : Config) : Prop :=
  ∀ w ∈ omega, good c w

def Worst (omega : Finset World) (cost : Config → World → ℕ) (c : Config) : ℕ :=
  omega.sup (cost c)

def Total (omega : Finset World) (bits : Config → ℕ)
    (cost : Config → World → ℕ) (lambda : ℕ) (c : Config) : ℕ :=
  lambda * bits c + Worst omega cost c

noncomputable def SafeSet (C : Finset Config) (omega : Finset World)
    (good : Config → World → Prop) : Finset Config := by
  classical
  exact C.filter (fun c => SafeOn omega good c)

theorem mem_safeSet_iff (C : Finset Config) (omega : Finset World)
    (good : Config → World → Prop) (c : Config) :
    c ∈ SafeSet C omega good ↔ c ∈ C ∧ SafeOn omega good c := by
  classical
  simp [SafeSet]

theorem optimal_exists (C : Finset Config) (omega : Finset World)
    (good : Config → World → Prop) (bits : Config → ℕ)
    (cost : Config → World → ℕ) (lambda : ℕ)
    (h : ∃ c ∈ C, SafeOn omega good c) :
    ∃ c ∈ C, SafeOn omega good c ∧
      ∀ d ∈ C, SafeOn omega good d →
        Total omega bits cost lambda c ≤ Total omega bits cost lambda d := by
  classical
  have hn : (SafeSet C omega good).Nonempty := by
    obtain ⟨c, hc, hs⟩ := h
    exact ⟨c, (mem_safeSet_iff C omega good c).2 ⟨hc, hs⟩⟩
  obtain ⟨c, hc, hmin⟩ :=
    Finset.exists_min_image (SafeSet C omega good)
      (Total omega bits cost lambda) hn
  obtain ⟨hcC, hcSafe⟩ := (mem_safeSet_iff C omega good c).1 hc
  refine ⟨c, hcC, hcSafe, ?_⟩
  intro d hd hg
  exact hmin d ((mem_safeSet_iff C omega good d).2 ⟨hd, hg⟩)

theorem added_capability_never_hurts
    (C D : Finset Config) (omega : Finset World)
    (good : Config → World → Prop) (bits : Config → ℕ)
    (cost : Config → World → ℕ) (lambda : ℕ)
    (hsub : C ⊆ D) (h : ∃ c ∈ C, SafeOn omega good c) :
    ∃ d ∈ D, SafeOn omega good d ∧
      ∀ c ∈ C, SafeOn omega good c →
        Total omega bits cost lambda d ≤ Total omega bits cost lambda c := by
  have hD : ∃ c ∈ D, SafeOn omega good c := by
    obtain ⟨c, hc, hs⟩ := h
    exact ⟨c, hsub hc, hs⟩
  obtain ⟨d, hd, hsafe, hopt⟩ :=
    optimal_exists D omega good bits cost lambda hD
  refine ⟨d, hd, hsafe, ?_⟩
  intro c hc hg
  exact hopt c (hsub hc) hg

theorem fewer_worlds_never_hurts
    (C : Finset Config) (small large : Finset World)
    (good : Config → World → Prop) (bits : Config → ℕ)
    (cost : Config → World → ℕ) (lambda : ℕ)
    (hsub : small ⊆ large)
    (h : ∃ c ∈ C, SafeOn large good c) :
    ∃ c ∈ C, SafeOn small good c ∧
      ∀ d ∈ C, SafeOn large good d →
        Total small bits cost lambda c ≤ Total large bits cost lambda d := by
  have hs : ∃ c ∈ C, SafeOn small good c := by
    obtain ⟨d, hd, hg⟩ := h
    exact ⟨d, hd, by
      intro w hw
      exact hg w (hsub hw)⟩
  obtain ⟨c, hc, hgood, hopt⟩ :=
    optimal_exists C small good bits cost lambda hs
  refine ⟨c, hc, hgood, ?_⟩
  intro d hd hlarge
  have hsmall : SafeOn small good d := by
    intro w hw
    exact hlarge w (hsub hw)
  have hcost : Total small bits cost lambda d ≤
      Total large bits cost lambda d := by
    unfold Total Worst
    exact Nat.add_le_add_left (Finset.sup_mono hsub)
      (lambda * bits d)
  exact le_trans (hopt d hd hsmall) hcost

theorem increasing_memory_price
    (omega : Finset World) (bits : Config → ℕ)
    (cost : Config → World → ℕ) (c : Config)
    {l1 l2 : ℕ} (h : l1 ≤ l2) :
    Total omega bits cost l1 c ≤ Total omega bits cost l2 c := by
  unfold Total
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right (bits c) h) (Worst omega cost c)

def ThreeChoice (lambda : ℚ) : ℚ :=
  min 17 (min (9 + lambda) (2 + 2 * lambda))

theorem two_bits_best (lambda : ℚ) (h0 : 0 ≤ lambda)
    (h7 : lambda ≤ 7) : ThreeChoice lambda = 2 + 2 * lambda := by
  unfold ThreeChoice
  apply le_antisymm
  · exact le_trans (min_le_right _ _) (min_le_right _ _)
  · apply le_min
    · linarith
    · apply le_min
      · linarith
      · exact le_rfl

theorem one_bit_best (lambda : ℚ) (h7 : 7 ≤ lambda)
    (h8 : lambda ≤ 8) : ThreeChoice lambda = 9 + lambda := by
  unfold ThreeChoice
  apply le_antisymm
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · apply le_min
    · linarith
    · apply le_min
      · exact le_rfl
      · linarith

theorem zero_bits_best (lambda : ℚ) (h8 : 8 ≤ lambda) :
    ThreeChoice lambda = 17 := by
  unfold ThreeChoice
  apply le_antisymm
  · exact min_le_left _ _
  · apply le_min
    · exact le_rfl
    · apply le_min
      · linarith
      · linarith

theorem conditional_physical_transfer
    (omega : Finset World) (good realGood : Config → World → Prop)
    (c : Config) (actual : World)
    (hactual : actual ∈ omega)
    (hsafe : SafeOn omega good c)
    (htransfer : ∀ w ∈ omega, good c w → realGood c w) :
    realGood c actual := by
  exact htransfer actual hactual (hsafe actual hactual)

example : SafeOn ({false} : Finset Bool)
    (fun (_ : Unit) (w : Bool) => w = false) () := by
  intro w hw
  simpa using hw

example : ¬ ((fun (_ : Unit) (w : Bool) => w = false) () true) := by
  decide

#print axioms optimal_exists
#print axioms added_capability_never_hurts
#print axioms fewer_worlds_never_hurts
#print axioms increasing_memory_price
#print axioms two_bits_best
#print axioms one_bit_best
#print axioms zero_bits_best
#print axioms conditional_physical_transfer
end InsacermoMinimax
