-- External C3 coverage audit. Reuses frozen PortableC3 kernels; no changes to engine.
import C3.PortableExactSearchV1

namespace PortableC3

inductive C3Class where
  | ACT
  | EPISTEMIC_OPEN
  | REFUSE_ROBUST
  deriving DecidableEq, Repr

/-- Three-way finite classification relative to declared Must/May models. -/
def classifyFinite (must may : Model) (n budget : Nat)
    (lower upper : List Nat) : C3Class :=
  if canFinite must n budget upper = true then .ACT
  else if canFinite may n budget lower = true then .EPISTEMIC_OPEN
  else .REFUSE_ROBUST

/-- ACT iff the more restrictive Must/Upper model admits a safe tree. -/
theorem classify_act_iff (must may : Model) (n budget : Nat)
    (lower upper : List Nat) :
    classifyFinite must may n budget lower upper = .ACT ↔
    ∃ t : Tree, Safe must n budget upper t := by
  constructor
  · intro h
    by_cases hm : canFinite must n budget upper = true
    · exact (finite_search_complete must n budget upper).mp hm
    · simp [classifyFinite, hm] at h
  · rintro ⟨t, ht⟩
    have hm : canFinite must n budget upper = true :=
      (finite_search_complete must n budget upper).mpr ⟨t, ht⟩
    simp [classifyFinite, hm]

/-- Robust refusal excludes any safe tree even under May/Lower. -/
theorem classify_refuse_excludes_may (must may : Model)
    (n budget : Nat) (lower upper : List Nat)
    (h : classifyFinite must may n budget lower upper = .REFUSE_ROBUST)
    (t : Tree) : ¬ Safe may n budget lower t := by
  intro ht
  have hy : canFinite may n budget lower = true :=
    (finite_search_complete may n budget lower).mpr ⟨t, ht⟩
  by_cases hm : canFinite must n budget upper = true
  · simp [classifyFinite, hm] at h
  · simp [classifyFinite, hm, hy] at h

/-- Robust refusal also excludes a Must/Upper solution. -/
theorem classify_refuse_excludes_must (must may : Model)
    (n budget : Nat) (lower upper : List Nat)
    (h : classifyFinite must may n budget lower upper = .REFUSE_ROBUST)
    (t : Tree) : ¬ Safe must n budget upper t := by
  intro ht
  have hm : canFinite must n budget upper = true :=
    (finite_search_complete must n budget upper).mpr ⟨t, ht⟩
  simp [classifyFinite, hm] at h

/-- Open means May/Lower admits a safe tree but Must/Upper does not. -/
theorem classify_open_has_may_witness (must may : Model)
    (n budget : Nat) (lower upper : List Nat)
    (h : classifyFinite must may n budget lower upper = .EPISTEMIC_OPEN) :
    ∃ t : Tree, Safe may n budget lower t := by
  by_cases hm : canFinite must n budget upper = true
  · simp [classifyFinite, hm] at h
  · have hy : canFinite may n budget lower = true := by
      cases hc : canFinite may n budget lower with
      | true => rfl
      | false => simp [classifyFinite, hm, hc] at h
    exact (finite_search_complete may n budget lower).mp hy

theorem classify_open_excludes_must (must may : Model)
    (n budget : Nat) (lower upper : List Nat)
    (h : classifyFinite must may n budget lower upper = .EPISTEMIC_OPEN)
    (t : Tree) : ¬ Safe must n budget upper t := by
  intro ht
  have hm : canFinite must n budget upper = true :=
    (finite_search_complete must n budget upper).mpr ⟨t, ht⟩
  simp [classifyFinite, hm] at h

#print axioms PortableC3.classify_act_iff
#print axioms PortableC3.classify_refuse_excludes_may
#print axioms PortableC3.classify_refuse_excludes_must
#print axioms PortableC3.classify_open_has_may_witness
#print axioms PortableC3.classify_open_excludes_must

end PortableC3
