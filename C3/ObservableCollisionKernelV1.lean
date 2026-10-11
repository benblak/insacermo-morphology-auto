import C3.PortableExactSearchV1

/- Generic observational collision obstruction. Two declared worlds require
   incompatible terminal actions. For each admitted probe there is at least
   one common outcome that leaves these worlds distinct and possible.
   Hence no FINITE tree can robustly guarantee classification for both,
   regardless of budget or depth. A constructive lower-bound certificate,
   not a claim about worlds outside the declared finite model. -/
namespace PortableC3

theorem pair_not_safely_separable
    (m : Model) (x y : Nat)
    (hbad : ∀ a, a < m.actionCount →
        ¬ (goodAt m x a = true ∧ goodAt m y a = true))
    (hcommon : ∀ q, q < m.probeCount →
        ∃ o : Bool,
          permits (senseAt m q x) o = true ∧
          permits (senseAt m q y) o = true ∧
          nextAt m q x o = x ∧ nextAt m q y o = y) :
    ∀ (t : Tree) (n b : Nat) (X : List Nat),
      x ∈ X → y ∈ X → ¬ Safe m n b X t := by
  intro t
  induction t with
  | act a =>
      intro n b X hx hy hs
      have hxGood := hs.2.2 x hx
      have hyGood := hs.2.2 y hy
      exact (hbad a hs.1) ⟨hxGood, hyGood⟩
  | probe q no yes ihNo ihYes =>
      intro n b X hx hy hs
      rcases hs with ⟨_hdepth, hq, _hcost, _htotal, hno, hyes⟩
      obtain ⟨o, hxObs, hyObs, hxNext, hyNext⟩ := hcommon q hq
      cases o with
      | false =>
          have hxAfter : x ∈ after m X q false := by
            apply List.mem_map.mpr
            exact ⟨x, List.mem_filter.mpr ⟨hx, hxObs⟩, hxNext⟩
          have hyAfter : y ∈ after m X q false := by
            apply List.mem_map.mpr
            exact ⟨y, List.mem_filter.mpr ⟨hy, hyObs⟩, hyNext⟩
          exact ihNo (n-1) (b-priceProbe m q) (after m X q false)
            hxAfter hyAfter hno
      | true =>
          have hxAfter : x ∈ after m X q true := by
            apply List.mem_map.mpr
            exact ⟨x, List.mem_filter.mpr ⟨hx, hxObs⟩, hxNext⟩
          have hyAfter : y ∈ after m X q true := by
            apply List.mem_map.mpr
            exact ⟨y, List.mem_filter.mpr ⟨hy, hyObs⟩, hyNext⟩
          exact ihYes (n-1) (b-priceProbe m q) (after m X q true)
            hxAfter hyAfter hyes

theorem pair_blocks_all_budgets
    (m : Model) (x y : Nat)
    (hbad : ∀ a, a < m.actionCount →
        ¬ (goodAt m x a = true ∧ goodAt m y a = true))
    (hcommon : ∀ q, q < m.probeCount →
        ∃ o : Bool,
          permits (senseAt m q x) o = true ∧
          permits (senseAt m q y) o = true ∧
          nextAt m q x o = x ∧ nextAt m q y o = y)
    (n budget : Nat) :
    canFinite m n budget [x,y] = false := by
  cases hc : canFinite m n budget [x,y] with
  | false => rfl
  | true =>
      obtain ⟨t, ht⟩ := (finite_search_complete m n budget [x,y]).mp hc
      have contradiction : False :=
        pair_not_safely_separable m x y hbad hcommon
          t n budget [x,y] (by simp) (by simp) ht
      exact False.elim contradiction

end PortableC3
