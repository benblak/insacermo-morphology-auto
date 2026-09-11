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
      · simp [SquareBaseCaps]
      · intro t _htB hEq
        cases t <;> simp [SquareFineObs] at hEq ⊢
  | w1 =>
      refine ⟨a2, ?_, ?_⟩
      · simp [SquareBaseCaps]
      · intro t _htB hEq
        cases t <;> simp [SquareFineObs] at hEq ⊢
  | w2 =>
      refine ⟨a2, ?_, ?_⟩
      · simp [SquareBaseCaps]
      · intro t _htB hEq
        cases t <;> simp [SquareFineObs] at hEq ⊢
  | w3 =>
      refine ⟨a1, ?_, ?_⟩
      · simp [SquareBaseCaps]
      · intro t _htB hEq
        cases t <;> simp [SquareFineObs] at hEq ⊢

/-- The coarse one-bit observation is unsafe under the base capabilities. -/
theorem squareCoarse_unsafe_base :
    ¬ SafeRep SquareGood Set.univ SquareBaseCaps SquareCoarseObs := by
  intro hsafe
  rcases hsafe false ⟨w0, by simp, rfl⟩ with ⟨a, ha, hall⟩
  have h0 := hall w0 (by simp) rfl
  have h1 := hall w1 (by simp) rfl
  cases a <;> simp [SquareBaseCaps, SquareGood] at ha h0 h1

/-- Adding a0 alone does not buy the coarse observation: the upper fiber still
requires a3, which remains unavailable. -/
theorem squareCoarse_unsafe_add0 :
    ¬ SafeRep SquareGood Set.univ SquareCapsAdd0 SquareCoarseObs := by
  intro hsafe
  rcases hsafe true ⟨w2, by simp, rfl⟩ with ⟨a, ha, hall⟩
  have h2 := hall w2 (by simp) rfl
  have h3 := hall w3 (by simp) rfl
  cases a <;> simp [SquareCapsAdd0, SquareGood] at ha h2 h3

/-- Adding a3 alone does not buy the coarse observation: the lower fiber still
requires a0, which remains unavailable. -/
theorem squareCoarse_unsafe_add3 :
    ¬ SafeRep SquareGood Set.univ SquareCapsAdd3 SquareCoarseObs := by
  intro hsafe
  rcases hsafe false ⟨w0, by simp, rfl⟩ with ⟨a, ha, hall⟩
  have h0 := hall w0 (by simp) rfl
  have h1 := hall w1 (by simp) rfl
  cases a <;> simp [SquareCapsAdd3, SquareGood] at ha h0 h1

/-- Jointly adding a0 and a3 makes the one-bit observation safe: use a0 on the
lower fiber and a3 on the upper fiber. -/
theorem squareCoarse_safe_both :
    SafeRep SquareGood Set.univ SquareCapsBoth SquareCoarseObs := by
  intro y hy
  cases y with
  | false =>
      refine ⟨a0, by simp [SquareCapsBoth], ?_⟩
      intro s _hsB hobs
      cases s <;> simp [SquareCoarseObs, SquareGood] at hobs ⊢
  | true =>
      refine ⟨a3, by simp [SquareCapsBoth], ?_⟩
      intro s _hsB hobs
      cases s <;> simp [SquareCoarseObs, SquareGood] at hobs ⊢

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
