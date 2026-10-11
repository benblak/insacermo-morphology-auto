import C3.PortableVerifierSoundnessV1

/- For EVERY finite declared model, the Boolean exhaustive search is sound
   and complete relative to the portable policy-tree semantics.
   Therefore a false exhaustive result excludes ALL admissible policy trees,
   rather than merely disproving a single emitted witness. -/
namespace PortableC3

theorem direct_iff_witness (m : Model) (b : Nat) (X : List Nat) :
    direct m b X = true ↔
    ∃ a, a < m.actionCount ∧ priceAction m a ≤ b ∧
      ∀ w, w ∈ X → goodAt m w a = true := by
  simp [direct, List.any_eq_true, List.mem_range,
    List.all_eq_true, Bool.and_eq_true, and_assoc]

theorem finite_search_complete (m : Model) (n : Nat) :
    ∀ b X, canFinite m n b X = true ↔
      ∃ t : Tree, Safe m n b X t := by
  induction n with
  | zero =>
      intro b X
      constructor
      · intro h
        obtain ⟨a, ha, hc, hg⟩ := (direct_iff_witness m b X).mp h
        exact ⟨.act a, ⟨ha, hc, hg⟩⟩
      · rintro ⟨t, ht⟩
        cases t with
        | act a =>
            exact (direct_iff_witness m b X).mpr
              ⟨a, ht.1, ht.2.1, ht.2.2⟩
        | probe q l r =>
            exact False.elim (Nat.not_lt_zero _ ht.1)
  | succ n ih =>
      intro b X
      constructor
      · intro h
        have hcases := h
        simp only [canFinite, Bool.or_eq_true, List.any_eq_true] at hcases
        rcases hcases with hd | ⟨q, hmem, hq⟩
        · obtain ⟨a, ha, hc, hg⟩ := (direct_iff_witness m b X).mp hd
          exact ⟨.act a, ⟨ha, hc, hg⟩⟩
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
          rcases hq with ⟨⟨⟨hcost, htotal⟩, hn⟩, hy⟩
          obtain ⟨no, hno⟩ := (ih _ _).mp hn
          obtain ⟨yes, hyes⟩ := (ih _ _).mp hy
          have htotal' : ∀ w, w ∈ X → senseAt m q w != 0 := by
            simpa [sensorTotal, List.all_eq_true] using htotal
          exact ⟨.probe q no yes,
            ⟨Nat.zero_lt_succ n, List.mem_range.mp hmem,
             hcost, htotal', hno, hyes⟩⟩
      · rintro ⟨t, ht⟩
        cases t with
        | act a =>
            have hd : direct m b X = true :=
              (direct_iff_witness m b X).mpr
                ⟨a, ht.1, ht.2.1, ht.2.2⟩
            simp [canFinite, hd]
        | probe q no yes =>
            rcases ht with ⟨hdepth, hqbound, hcost, htotal, hno, hyes⟩
            have hn := (ih _ _).mpr ⟨no, hno⟩
            have hy := (ih _ _).mpr ⟨yes, hyes⟩
            have hs : sensorTotal m X q = true := by
              simpa [sensorTotal, List.all_eq_true] using htotal
            have hbranch :
                (List.range m.probeCount).any (fun q =>
                  decide (priceProbe m q ≤ b) && sensorTotal m X q &&
                  canFinite m n (b - priceProbe m q) (after m X q false) &&
                  canFinite m n (b - priceProbe m q) (after m X q true)) = true := by
              apply List.any_eq_true.mpr
              refine ⟨q, List.mem_range.mpr hqbound, ?_⟩
              simp [hcost, hs, hn, hy]
            simp [canFinite, hbranch]

theorem finite_search_iff_checked_tree
    (m : Model) (n b : Nat) (X : List Nat) :
    canFinite m n b X = true ↔
      ∃ t : Tree, checkTree m n b X t = true := by
  rw [finite_search_complete m n b X]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (checkTree_iff_safe m n b X t).mpr ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, (checkTree_iff_safe m n b X t).mp ht⟩

theorem impossible_budget_rejects_every_plan (m : Model)
    (n b : Nat) (X : List Nat)
    (h : canFinite m n b X = false) (t : Tree) :
    checkTree m n b X t = false := by
  cases hc : checkTree m n b X t with
  | false => exact hc
  | true =>
      have hyes : canFinite m n b X = true :=
        (finite_search_iff_checked_tree m n b X).mpr ⟨t, hc⟩
      simp [h] at hyes

end PortableC3
