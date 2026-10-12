-- INSACERMO external proof audit, 2026-10-12. Original engine unchanged.
-- General future-preservation theorem in Lean 4; no sorry/admit/custom axioms.
import Init

namespace InsacermoFuturs

universe u
variable {α : Type u}

/-- A temporal history where all states are admissible and consecutive states
    satisfy the declared transition relation. -/
def Valid (S : α → Prop) (R : α → α → Prop)
    (h : Nat) (trajectory : Fin h → α) : Prop :=
  (∀ i, S (trajectory i)) ∧
  (∀ i j, j.val = i.val + 1 → R (trajectory i) (trajectory j))

/-- Enlarging the allowed states cannot invalidate a previously valid history. -/
theorem valid_mono
    {S T : α → Prop} {R : α → α → Prop} {h : Nat}
    (subset : ∀ x, S x → T x)
    {trajectory : Fin h → α}
    (hv : Valid S R h trajectory) : Valid T R h trajectory := by
  constructor
  · intro i
    exact subset (trajectory i) (hv.1 i)
  · exact hv.2

/-- The direct mapping from old histories to enlarged-state histories. -/
def liftHistory
    {S T : α → Prop} {R : α → α → Prop} {h : Nat}
    (subset : ∀ x, S x → T x)
    (p : {trajectory : Fin h → α // Valid S R h trajectory}) :
    {trajectory : Fin h → α // Valid T R h trajectory} :=
  ⟨p.1, valid_mono subset p.2⟩

/-- This mapping is injective: no old history is lost or merged. -/
theorem liftHistory_injective
    {S T : α → Prop} {R : α → α → Prop} {h : Nat}
    (subset : ∀ x, S x → T x) :
    Function.Injective (liftHistory (S := S) (T := T) (R := R) (h := h) subset) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg Subtype.val hpq

#print axioms InsacermoFuturs.valid_mono
#print axioms InsacermoFuturs.liftHistory_injective

end InsacermoFuturs
