import Std
import ReachableBeliefKernelV1

/-!
INSACERMO — Finite Reachable Belief Bound V1

Finite deterministic/passive specialization.

Assume probes are indexed by Nat values p < P and outcomes by Nat values o < M.
A realizable raw history is encoded canonically by a list of length P:
  0     = probe not observed,
  o + 1 = observed outcome o.

Thus every realizable history is represented by one code in the explicit
catalogue partialCodes (M+1) P, whose length is exactly (M+1)^P.

The decoded belief of that code is extensionally equal to the belief obtained
from the raw history. Therefore all reachable beliefs are covered by a finite
catalogue of (M+1)^P code slots.

Different codes may decode to the same belief, so this is an upper bound /
covering result, not an injectivity claim.
-/

namespace InsacermoFiniteReachableBelief

open InsacermoReachableBelief

abbrev NatConstraint := Constraint Nat Nat

def BoundedHistory
    (probeCount outcomeBound : Nat)
    (history : List NatConstraint) : Prop :=
  ∀ c ∈ history, c.probe < probeCount ∧ c.outcome < outcomeBound

noncomputable def canonicalDigit
    (history : List NatConstraint)
    (p : Nat) : Nat :=
  match canonicalCode history p with
  | none => 0
  | some o => o + 1

noncomputable def finiteCanonicalCode
    (probeCount : Nat)
    (history : List NatConstraint) : List Nat :=
  (List.range probeCount).map (canonicalDigit history)

theorem finiteCanonicalCode_length
    (probeCount : Nat)
    (history : List NatConstraint) :
    (finiteCanonicalCode probeCount history).length = probeCount := by
  simp [finiteCanonicalCode]

theorem assignment_outcome_lt
    (probeCount outcomeBound : Nat)
    (history : List NatConstraint)
    (hbound : BoundedHistory probeCount outcomeBound history)
    (p o : Nat)
    (ha : HistoryAssignment history p o) :
    o < outcomeBound := by
  rcases ha with ⟨c, hc, hp, ho⟩
  have hb := hbound c hc
  simpa [ho] using hb.2

theorem canonicalDigit_lt
    (probeCount outcomeBound : Nat)
    (history : List NatConstraint)
    (hbound : BoundedHistory probeCount outcomeBound history)
    (p : Nat)
    (hp : p < probeCount) :
    canonicalDigit history p < outcomeBound + 1 := by
  classical
  unfold canonicalDigit
  by_cases h : ∃ o, HistoryAssignment history p o
  · have hcode :
      canonicalCode history p = some (Classical.choose h) := by
      simp [canonicalCode, h]
    rw [hcode]
    simp only
    have ho : Classical.choose h < outcomeBound :=
      assignment_outcome_lt probeCount outcomeBound history hbound p
        (Classical.choose h) (Classical.choose_spec h)
    omega
  · have hcode : canonicalCode history p = none := by
      simp [canonicalCode, h]
    rw [hcode]
    simp

theorem all_code_digits_lt
    (probeCount outcomeBound : Nat)
    (history : List NatConstraint)
    (hbound : BoundedHistory probeCount outcomeBound history) :
    ∀ d ∈ finiteCanonicalCode probeCount history,
      d < outcomeBound + 1 := by
  intro d hd
  simp only [finiteCanonicalCode, List.mem_map] at hd
  rcases hd with ⟨p, hpRange, rfl⟩
  have hp : p < probeCount := by
    simpa using hpRange
  exact canonicalDigit_lt probeCount outcomeBound history hbound p hp

theorem mem_partialCodes_of_length_all_lt :
    ∀ (alphabet n : Nat) (xs : List Nat),
      xs.length = n →
      (∀ x ∈ xs, x < alphabet) →
      xs ∈ partialCodes alphabet n := by
  intro alphabet n
  induction n with
  | zero =>
      intro xs hlen hlt
      have hx : xs = [] := List.eq_nil_of_length_eq_zero hlen
      subst xs
      simp [partialCodes]
  | succ n ih =>
      intro xs hlen hlt
      cases xs with
      | nil =>
          simp at hlen
      | cons x tail =>
          have hx : x < alphabet := hlt x (by simp)
          have htailLen : tail.length = n := by
            simpa using Nat.succ.inj hlen
          have htailLt : ∀ y ∈ tail, y < alphabet := by
            intro y hy
            exact hlt y (by simp [hy])
          have htailMem : tail ∈ partialCodes alphabet n :=
            ih tail htailLen htailLt
          simp [partialCodes, hx, htailMem]

theorem finiteCanonicalCode_mem_catalogue
    (probeCount outcomeBound : Nat)
    (history : List NatConstraint)
    (hbound : BoundedHistory probeCount outcomeBound history) :
    finiteCanonicalCode probeCount history ∈
      partialCodes (outcomeBound + 1) probeCount := by
  apply mem_partialCodes_of_length_all_lt
  · exact finiteCanonicalCode_length probeCount history
  · exact all_code_digits_lt probeCount outcomeBound history hbound

/--
Decode one finite code against a deterministic observation function.
Digit 0 imposes no constraint; digit o+1 imposes observe p w = o.
Coordinates beyond the code are irrelevant.
-/
def decodeCode
    {W : Type}
    (observe : Nat → W → Nat)
    (B : Belief W)
    (code : List Nat) : Belief W :=
  fun w =>
    B w ∧
    ∀ p d, code[p]? = some d →
      d = 0 ∨ observe p w + 1 = d

theorem canonical_digit_zero_iff_no_assignment
    (history : List NatConstraint)
    (p : Nat) :
    canonicalDigit history p = 0 ↔
      ¬ ∃ o, HistoryAssignment history p o := by
  classical
  by_cases h : ∃ o, HistoryAssignment history p o
  · have hc : canonicalCode history p = some (Classical.choose h) := by
      simp [canonicalCode, h]
    simp [canonicalDigit, hc, h]
  · have hc : canonicalCode history p = none := by
      simp [canonicalCode, h]
    have hno : ¬ HistoryAssignment history p o := by
      intro ha
      exact h ⟨o, ha⟩
    simp [canonicalDigit, hc, hno]

theorem canonical_digit_succ_iff
    {W : Type}
    (observe : Nat → W → Nat)
    (B : Belief W)
    (history : List NatConstraint)
    (hreal : RealizableHistory observe B history)
    (p o : Nat) :
    canonicalDigit history p = o + 1 ↔
      HistoryAssignment history p o := by
  classical
  have hs := realizable_assignment_single_valued observe B history hreal
  unfold canonicalDigit
  by_cases h : ∃ x, HistoryAssignment history p x
  · have hc : canonicalCode history p = some (Classical.choose h) := by
      simp [canonicalCode, h]
    rw [hc]
    simp only
    constructor
    · intro heq
      have hchosen := Classical.choose_spec h
      have hov : Classical.choose h = o := by omega
      simpa [hov] using hchosen
    · intro ha
      have hchosen := Classical.choose_spec h
      have hov : Classical.choose h = o :=
        hs p (Classical.choose h) o hchosen ha
      omega
  · have hc : canonicalCode history p = none := by
      simp [canonicalCode, h]
    simp [canonicalDigit, hc, h]

theorem finiteCanonicalCode_get
    (probeCount : Nat)
    (history : List NatConstraint)
    (p : Nat)
    (hp : p < probeCount) :
    (finiteCanonicalCode probeCount history)[p]? =
      some (canonicalDigit history p) := by
  simp [finiteCanonicalCode, hp]

/--
Main finite decoding theorem:
for every realizable bounded history, its raw-history belief is exactly the
belief decoded from its canonical finite code.
-/
theorem raw_history_eq_decoded_canonical
    {W : Type}
    (observe : Nat → W → Nat)
    (B : Belief W)
    (probeCount outcomeBound : Nat)
    (history : List NatConstraint)
    (hreal : RealizableHistory observe B history)
    (hbound : BoundedHistory probeCount outcomeBound history)
    (hprobeCovered :
      ∀ c ∈ history, c.probe < probeCount) :
    runHistory observe B history =
      decodeCode observe B (finiteCanonicalCode probeCount history) := by
  funext w
  apply propext
  rw [runHistory_iff_assignment observe B history w]
  constructor
  · rintro ⟨hB, hassign⟩
    refine ⟨hB, ?_⟩
    intro p d hget
    have hp : p < probeCount := by
      by_cases hlt : p < probeCount
      · exact hlt
      · have hge : probeCount ≤ p := Nat.le_of_not_gt hlt
        have hnone :
            (finiteCanonicalCode probeCount history)[p]? = none := by
          apply List.getElem?_eq_none
          simpa [finiteCanonicalCode] using hge
        rw [hnone] at hget
        simp at hget
    have hcanon := finiteCanonicalCode_get probeCount history p hp
    rw [hcanon] at hget
    have hd : d = canonicalDigit history p := by
      exact Option.some.inj hget.symm
    subst d
    by_cases hz : canonicalDigit history p = 0
    · exact Or.inl hz
    · right
      have hex : ∃ o, HistoryAssignment history p o := by
        by_cases hyes : ∃ o, HistoryAssignment history p o
        · exact hyes
        · exact False.elim (hz ((canonical_digit_zero_iff_no_assignment history p).2 hyes))
      rcases hex with ⟨o, ha⟩
      have hdigit :
          canonicalDigit history p = o + 1 :=
        (canonical_digit_succ_iff observe B history hreal p o).2 ha
      have hobs : observe p w = o := hassign p o ha
      omega
  · rintro ⟨hB, hdecode⟩
    refine ⟨hB, ?_⟩
    intro p o ha
    have hp : p < probeCount := by
      rcases ha with ⟨c, hc, hpEq, hoEq⟩
      subst p
      exact hprobeCovered c hc
    have hget := finiteCanonicalCode_get probeCount history p hp
    have hdec := hdecode p (canonicalDigit history p) hget
    have hdigit :
        canonicalDigit history p = o + 1 :=
      (canonical_digit_succ_iff observe B history hreal p o).2 ha
    rcases hdec with hzero | hobs
    · rw [hdigit] at hzero
      omega
    · rw [hdigit] at hobs
      omega

/--
Every realizable bounded raw history is covered by one explicit code from the
finite catalogue of size (outcomeBound+1)^probeCount.
-/
theorem every_reachable_belief_has_catalogue_code
    {W : Type}
    (observe : Nat → W → Nat)
    (B : Belief W)
    (probeCount outcomeBound : Nat)
    (history : List NatConstraint)
    (hreal : RealizableHistory observe B history)
    (hbound : BoundedHistory probeCount outcomeBound history) :
    ∃ code ∈ partialCodes (outcomeBound + 1) probeCount,
      runHistory observe B history = decodeCode observe B code := by
  refine ⟨finiteCanonicalCode probeCount history,
    finiteCanonicalCode_mem_catalogue probeCount outcomeBound history hbound,
    ?_⟩
  apply raw_history_eq_decoded_canonical observe B probeCount outcomeBound
    history hreal hbound
  intro c hc
  exact (hbound c hc).1

theorem finite_catalogue_length
    (probeCount outcomeBound : Nat) :
    (partialCodes (outcomeBound + 1) probeCount).length =
      (outcomeBound + 1) ^ probeCount := by
  exact canonical_history_code_count probeCount outcomeBound

/--
Finite reachable-belief covering theorem:
there is an explicit catalogue with exactly (M+1)^P code slots, and every
realizable bounded history's belief is represented by at least one slot.
This yields the intended "at most" interpretation for distinct reachable
beliefs, while allowing multiple slots to decode to the same belief.
-/
theorem finite_reachable_belief_cover
    {W : Type}
    (observe : Nat → W → Nat)
    (B : Belief W)
    (probeCount outcomeBound : Nat) :
    (partialCodes (outcomeBound + 1) probeCount).length =
      (outcomeBound + 1) ^ probeCount ∧
    ∀ history : List NatConstraint,
      RealizableHistory observe B history →
      BoundedHistory probeCount outcomeBound history →
      ∃ code ∈ partialCodes (outcomeBound + 1) probeCount,
        runHistory observe B history = decodeCode observe B code := by
  constructor
  · exact finite_catalogue_length probeCount outcomeBound
  · intro history hreal hbound
    exact every_reachable_belief_has_catalogue_code
      observe B probeCount outcomeBound history hreal hbound

#print axioms finiteCanonicalCode_length
#print axioms canonicalDigit_lt
#print axioms mem_partialCodes_of_length_all_lt
#print axioms finiteCanonicalCode_mem_catalogue
#print axioms canonical_digit_succ_iff
#print axioms raw_history_eq_decoded_canonical
#print axioms every_reachable_belief_has_catalogue_code
#print axioms finite_catalogue_length
#print axioms finite_reachable_belief_cover

end InsacermoFiniteReachableBelief
