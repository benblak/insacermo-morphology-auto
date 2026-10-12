-- External refinement checker for the finite C3 Python receipt protocol.
-- The frozen Python engine is NOT modified and is NOT claimed verified here.
import C3.PortableExactSearchV1
import audit.python_lean_refinement_20261012.C3PolicyAttestation

namespace PortableC3

inductive ReceiptKind where
  | ACT | PROBE | REPAIR | EPISTEMIC_OPEN | REFUSE_ROBUST
  deriving DecidableEq, Repr

/-- This checker verifies the ACT/PROBE/REPAIR root, the allowed actions at ALL
    terminal leaves, actual Lean C3 safety, and the OPEN/REFUSE logical verdict.
    It also checks the concrete May witness carried in an OPEN Python candidate,
    which the historical generated C3Decision.lean did not expose as a tree. -/
def checkTypedReceipt
    (must may : Model) (mustAllow mayAllow : List Nat)
    (repairFlags : List Bool) (depth budget : Nat)
    (lower upper : List Nat) (kind : ReceiptKind)
    (candidate : Option Tree) : Bool :=
  match kind, candidate with
  | .ACT, some (.act a) =>
      attestPolicyTree must mustAllow depth budget upper (.act a)
  | .PROBE, some (.probe q no yes) =>
      attestPolicyTree must mustAllow depth budget upper (.probe q no yes) &&
        !(boolAt repairFlags q)
  | .REPAIR, some (.probe q no yes) =>
      attestPolicyTree must mustAllow depth budget upper (.probe q no yes) &&
        boolAt repairFlags q
  | .EPISTEMIC_OPEN, some t =>
      decide (canFinite must depth budget upper = false) &&
        attestPolicyTree may mayAllow depth budget lower t
  | .REFUSE_ROBUST, none =>
      decide (canFinite must depth budget upper = false) &&
        decide (canFinite may depth budget lower = false)
  | _, _ => false

theorem certified_ACT_is_safe_and_allowed
    (must may : Model) (mustAllow mayAllow : List Nat) (repairFlags : List Bool)
    (depth budget : Nat) (lower upper : List Nat) (a : Nat)
    (h : checkTypedReceipt must may mustAllow mayAllow repairFlags depth budget
         lower upper .ACT (some (.act a)) = true) :
    Safe must depth budget upper (.act a) ∧
    PolicyTree mustAllow (.act a) := by
  exact attested_tree_sound_and_authorized must mustAllow depth budget upper (.act a)
    (by simpa only [checkTypedReceipt] using h)

theorem certified_PROBE_is_safe_allowed_and_not_repair
    (must may : Model) (mustAllow mayAllow : List Nat) (repairFlags : List Bool)
    (depth budget : Nat) (lower upper : List Nat) (q : Nat) (no yes : Tree)
    (h : checkTypedReceipt must may mustAllow mayAllow repairFlags depth budget
         lower upper .PROBE (some (.probe q no yes)) = true) :
    (Safe must depth budget upper (.probe q no yes) ∧
     PolicyTree mustAllow (.probe q no yes)) ∧
     boolAt repairFlags q = false := by
  simp only [checkTypedReceipt, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨attested_tree_sound_and_authorized must mustAllow depth budget upper
    (.probe q no yes) h.1, h.2⟩

theorem certified_REPAIR_is_safe_allowed_and_repair
    (must may : Model) (mustAllow mayAllow : List Nat) (repairFlags : List Bool)
    (depth budget : Nat) (lower upper : List Nat) (q : Nat) (no yes : Tree)
    (h : checkTypedReceipt must may mustAllow mayAllow repairFlags depth budget
         lower upper .REPAIR (some (.probe q no yes)) = true) :
    (Safe must depth budget upper (.probe q no yes) ∧
     PolicyTree mustAllow (.probe q no yes)) ∧
     boolAt repairFlags q = true := by
  simp only [checkTypedReceipt, Bool.and_eq_true] at h
  exact ⟨attested_tree_sound_and_authorized must mustAllow depth budget upper
    (.probe q no yes) h.1, h.2⟩

theorem certified_OPEN_has_real_may_witness
    (must may : Model) (mustAllow mayAllow : List Nat) (repairFlags : List Bool)
    (depth budget : Nat) (lower upper : List Nat) (t : Tree)
    (h : checkTypedReceipt must may mustAllow mayAllow repairFlags depth budget
         lower upper .EPISTEMIC_OPEN (some t) = true) :
    canFinite must depth budget upper = false ∧
    Safe may depth budget lower t ∧ PolicyTree mayAllow t := by
  simp only [checkTypedReceipt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, (attested_tree_sound_and_authorized may mayAllow depth budget
    lower t h.2).1, (attested_tree_sound_and_authorized may mayAllow depth budget
    lower t h.2).2⟩

theorem certified_REFUSE_excludes_all_search_witnesses
    (must may : Model) (mustAllow mayAllow : List Nat) (repairFlags : List Bool)
    (depth budget : Nat) (lower upper : List Nat)
    (h : checkTypedReceipt must may mustAllow mayAllow repairFlags depth budget
         lower upper .REFUSE_ROBUST none = true) :
    (∀ t, ¬ Safe must depth budget upper t) ∧
    (∀ t, ¬ Safe may depth budget lower t) := by
  have hw : canFinite must depth budget upper = false ∧
      canFinite may depth budget lower = false := by
    simpa only [checkTypedReceipt, Bool.and_eq_true, decide_eq_true_eq] using h
  constructor
  · intro t ht
    have hx := (finite_search_complete must depth budget upper).mpr ⟨t, ht⟩
    simp [hw.1] at hx
  · intro t ht
    have hx := (finite_search_complete may depth budget lower).mpr ⟨t, ht⟩
    simp [hw.2] at hx

#print axioms PortableC3.certified_ACT_is_safe_and_allowed
#print axioms PortableC3.certified_PROBE_is_safe_allowed_and_not_repair
#print axioms PortableC3.certified_REPAIR_is_safe_allowed_and_repair
#print axioms PortableC3.certified_OPEN_has_real_may_witness
#print axioms PortableC3.certified_REFUSE_excludes_all_search_witnesses

end PortableC3
