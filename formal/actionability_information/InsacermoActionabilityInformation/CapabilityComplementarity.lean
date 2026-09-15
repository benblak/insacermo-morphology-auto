import InsacermoActionabilityInformation.CapabilityInformationPrice

namespace InsacermoActionabilityInformation

inductive SquareWorld
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Fintype

inductive SquareAction
  | a0 | a1 | a2 | a3
  deriving DecidableEq, Fintype

open SquareWorld SquareAction

/-- Four-world contract used to witness capability complementarity.
Each world admits exactly two actions. -/
def SquareGood : SquareWorld → SquareAction → Prop
  | w0, a0 => True
  | w0, a1 => True
  | w1, a0 => True
  | w1, a2 => True
  | w2, a2 => True
  | w2, a3 => True
  | w3, a1 => True
  | w3, a3 => True
  | _, _ => False

/-- Base capability set: actions a1 and a2. -/
def SquareBaseCaps : Set SquareAction :=
  fun a => a = a1 ∨ a = a2

/-- Base plus repair action a0. -/
def SquareCapsAdd0 : Set SquareAction :=
  fun a => a = a0 ∨ a = a1 ∨ a = a2

/-- Base plus repair action a3. -/
def SquareCapsAdd3 : Set SquareAction :=
  fun a => a = a1 ∨ a = a2 ∨ a = a3

/-- Base plus both repair actions. -/
def SquareCapsBoth : Set SquareAction := Set.univ

/-- Fine observation: all four worlds remain distinct. -/
def SquareFineObs : SquareWorld → SquareWorld := id

/-- One-bit coarse observation. Worlds {w0,w1} are aliased, as are {w2,w3}. -/
def SquareCoarseObs : SquareWorld → Bool
  | w0 => false
  | w1 => false
  | w2 => true
  | w3 => true

private theorem a0_not_base : a0 ∉ SquareBaseCaps := by
  intro h
  change a0 = a1 ∨ a0 = a2 at h
  rcases h with h | h <;> cases h

private theorem a3_not_base : a3 ∉ SquareBaseCaps := by
  intro h
  change a3 = a1 ∨ a3 = a2 at h
  rcases h with h | h <;> cases h

private theorem a3_not_add0 : a3 ∉ SquareCapsAdd0 := by
  intro h
  change a3 = a0 ∨ a3 = a1 ∨ a3 = a2 at h
  rcases h with h | h
  · cases h
  · rcases h with h | h <;> cases h

private theorem a0_not_add3 : a0 ∉ SquareCapsAdd3 := by
  intro h
  change a0 = a1 ∨ a0 = a2 ∨ a0 = a3 at h
  rcases h with h | h
  · cases h
  · rcases h with h | h <;> cases h

/-- The fine observation refines the one-bit coarse observation. -/
theorem squareFine_refines_coarse :
    Refines SquareFineObs SquareCoarseObs := by
  refine ⟨SquareCoarseObs, ?_⟩
  intro s
  rfl

/-- Under the base capabilities, retaining the full world identity is safe. -/
theorem squareFine_safe_base :
    SafeRep SquareGood Set.univ SquareBaseCaps SquareFineObs := by
  intro y hy
  rcases hy with ⟨s, _hsB, hsy⟩
  subst y
  cases s with
  | w0 =>
      refine ⟨a1, ?_, ?_⟩
      · exact Or.inl rfl
      · intro t _htB hEq
        change t = w0 at hEq
        subst t
        exact True.intro
  | w1 =>
      refine ⟨a2, ?_, ?_⟩
      · exact Or.inr rfl
      · intro t _htB hEq
        change t = w1 at hEq
        subst t
        exact True.intro
  | w2 =>
      refine ⟨a2, ?_, ?_⟩
      · exact Or.inr rfl
      · intro t _htB hEq
        change t = w2 at hEq
        subst t
        exact True.intro
  | w3 =>
      refine ⟨a1, ?_, ?_⟩
      · exact Or.inl rfl
      · intro t _htB hEq
        change t = w3 at hEq
        subst t
        exact True.intro

/-- The coarse one-bit observation is unsafe under the base capabilities. -/
theorem squareCoarse_unsafe_base :
    ¬ SafeRep SquareGood Set.univ SquareBaseCaps SquareCoarseObs := by
  intro hsafe
  rcases hsafe false ⟨w0, Set.mem_univ w0, rfl⟩ with ⟨a, ha, hall⟩
  have h0 := hall w0 (Set.mem_univ w0) rfl
  have h1 := hall w1 (Set.mem_univ w1) rfl
  cases a with
  | a0 => exact a0_not_base ha
  | a1 => exact h1
  | a2 => exact h0
  | a3 => exact a3_not_base ha

/-- Adding a0 alone does not buy the coarse observation: the upper fiber still
requires a3, which remains unavailable. -/
theorem squareCoarse_unsafe_add0 :
    ¬ SafeRep SquareGood Set.univ SquareCapsAdd0 SquareCoarseObs := by
  intro hsafe
  rcases hsafe true ⟨w2, Set.mem_univ w2, rfl⟩ with ⟨a, ha, hall⟩
  have h2 := hall w2 (Set.mem_univ w2) rfl
  have h3 := hall w3 (Set.mem_univ w3) rfl
  cases a with
  | a0 => exact h2
  | a1 => exact h2
  | a2 => exact h3
  | a3 => exact a3_not_add0 ha

/-- Adding a3 alone does not buy the coarse observation: the lower fiber still
requires a0, which remains unavailable. -/
theorem squareCoarse_unsafe_add3 :
    ¬ SafeRep SquareGood Set.univ SquareCapsAdd3 SquareCoarseObs := by
  intro hsafe
  rcases hsafe false ⟨w0, Set.mem_univ w0, rfl⟩ with ⟨a, ha, hall⟩
  have h0 := hall w0 (Set.mem_univ w0) rfl
  have h1 := hall w1 (Set.mem_univ w1) rfl
  cases a with
  | a0 => exact a0_not_add3 ha
  | a1 => exact h1
  | a2 => exact h0
  | a3 => exact h0

/-- Jointly adding a0 and a3 makes the one-bit observation safe: use a0 on the
lower fiber and a3 on the upper fiber. -/
theorem squareCoarse_safe_both :
    SafeRep SquareGood Set.univ SquareCapsBoth SquareCoarseObs := by
  intro y hy
  cases y with
  | false =>
      refine ⟨a0, Set.mem_univ a0, ?_⟩
      intro s _hsB hobs
      cases s with
      | w0 => exact True.intro
      | w1 => exact True.intro
      | w2 => cases hobs
      | w3 => cases hobs
  | true =>
      refine ⟨a3, Set.mem_univ a3, ?_⟩
      intro s _hsB hobs
      cases s with
      | w0 => cases hobs
      | w1 => cases hobs
      | w2 => exact True.intro
      | w3 => exact True.intro

/-- Explicit complementarity witness: neither repair alone permits the
one-bit forgetting step, while the pair of repairs does.

This shows that capability-information leverage can have increasing returns:
a greedy repair policy that only accepts individually positive one-step
information gains can miss a jointly valuable repair bundle. -/
theorem square_joint_capability_complementarity :
    Refines SquareFineObs SquareCoarseObs ∧
    SafeRep SquareGood Set.univ SquareBaseCaps SquareFineObs ∧
    ¬ SafeRep SquareGood Set.univ SquareBaseCaps SquareCoarseObs ∧
    ¬ SafeRep SquareGood Set.univ SquareCapsAdd0 SquareCoarseObs ∧
    ¬ SafeRep SquareGood Set.univ SquareCapsAdd3 SquareCoarseObs ∧
    SafeRep SquareGood Set.univ SquareCapsBoth SquareCoarseObs := by
  exact ⟨squareFine_refines_coarse,
    squareFine_safe_base,
    squareCoarse_unsafe_base,
    squareCoarse_unsafe_add0,
    squareCoarse_unsafe_add3,
    squareCoarse_safe_both⟩

end InsacermoActionabilityInformation
