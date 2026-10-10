import Std

/-!
INSACERMO SYMBOLIC TRANSFORMATION SYNTHESIS V1
A family of contracts over an unbounded natural-number control u and
an additive capacity repair r.  No catalogue of candidate controls or
repairs is enumerated.  The proofs are model-relative: declared bounds
are not inferred physical laws.
-/
namespace InsacermoSymbolic

abbrev Bound := Nat × Nat

def demand : List Bound → Nat
  | [] => 0
  | c :: cs => max c.1 (demand cs)

def repairAt (u : Nat) : List Bound → Nat
  | [] => 0
  | c :: cs => max (u - c.2) (repairAt u cs)

def optimalRepair (xs : List Bound) : Nat :=
  repairAt (demand xs) xs

def Feasible (xs : List Bound) (u r : Nat) : Prop :=
  ∀ c, c ∈ xs → c.1 ≤ u ∧ u ≤ c.2 + r

theorem demand_le_iff (xs : List Bound) (u : Nat) :
    demand xs ≤ u ↔ ∀ c, c ∈ xs → c.1 ≤ u := by
  induction xs with
  | nil =>
      simp [demand]
  | cons c cs ih =>
      simp only [demand]
      constructor
      · intro h x hx
        have hc : c.1 ≤ u := by omega
        have hcs : demand cs ≤ u := by omega
        rcases List.mem_cons.mp hx with heq | htail
        · subst x
          exact hc
        · exact (ih.mp hcs) x htail
      · intro h
        have hc : c.1 ≤ u := h c (by simp)
        have hcs : demand cs ≤ u := ih.mpr (by
          intro x hx
          exact h x (by simp [hx]))
        omega

theorem repairAt_le_iff (xs : List Bound) (u r : Nat) :
    repairAt u xs ≤ r ↔ ∀ c, c ∈ xs → u ≤ c.2 + r := by
  induction xs with
  | nil =>
      simp [repairAt]
  | cons c cs ih =>
      simp only [repairAt]
      constructor
      · intro h x hx
        have hc : u - c.2 ≤ r := by omega
        have hcs : repairAt u cs ≤ r := by omega
        rcases List.mem_cons.mp hx with heq | htail
        · subst x
          omega
        · exact (ih.mp hcs) x htail
      · intro h
        have hc := h c (by simp)
        have hcs : repairAt u cs ≤ r := ih.mpr (by
          intro x hx
          exact h x (by simp [hx]))
        omega

/-- The synthesized control and repair meet every world constraint. -/
theorem synthesized_sound (xs : List Bound) :
    Feasible xs (demand xs) (optimalRepair xs) := by
  intro c hc
  constructor
  · exact (demand_le_iff xs (demand xs)).mp (by omega) c hc
  · exact (repairAt_le_iff xs (demand xs) (optimalRepair xs)).mp (by rfl) c hc

/-- No feasible control can use a repair smaller than the synthesized one. -/
theorem synthesized_minimal (xs : List Bound) (u r : Nat)
    (h : Feasible xs u r) :
    optimalRepair xs ≤ r := by
  have hDemand : demand xs ≤ u :=
    (demand_le_iff xs u).mpr (by
      intro c hc
      exact (h c hc).1)
  apply (repairAt_le_iff xs (demand xs) r).mpr
  intro c hc
  have hu := (h c hc).2
  omega

/-- The mathematical synthesis problem is solved without enumerating u. -/
theorem synthesis_iff_budget (xs : List Bound) (r : Nat) :
    (∃ u, Feasible xs u r) ↔ optimalRepair xs ≤ r := by
  constructor
  · rintro ⟨u, hu⟩
    exact synthesized_minimal xs u r hu
  · intro hr
    refine ⟨demand xs, ?_⟩
    intro c hc
    constructor
    · exact (synthesized_sound xs c hc).1
    · have hs := (synthesized_sound xs c hc).2
      omega

/-- For a fixed reserve, checking every pair of worlds is complete in 1D. -/
theorem feasible_iff_pairs (xs : List Bound) (r : Nat) :
    (∃ u, Feasible xs u r) ↔
      ∀ a, a ∈ xs → ∀ b, b ∈ xs → a.1 ≤ b.2 + r := by
  constructor
  · rintro ⟨u, hu⟩ a ha b hb
    have h1 := (hu a ha).1
    have h2 := (hu b hb).2
    omega
  · intro h
    refine ⟨demand xs, ?_⟩
    intro c hc
    constructor
    · exact (demand_le_iff xs (demand xs)).mp (by omega) c hc
    · exact (demand_le_iff xs (c.2 + r)).mpr (by
        intro a ha
        exact h a ha c hc)

/-- Any conflicting pair certifies a strict lower bound on repair. -/
theorem pair_impossibility (xs : List Bound) (a b : Bound)
    (ha : a ∈ xs) (hb : b ∈ xs) (r : Nat)
    (hgap : b.2 + r < a.1) :
    ¬ ∃ u, Feasible xs u r := by
  rintro ⟨u, hu⟩
  have h1 := (hu a ha).1
  have h2 := (hu b hb).2
  omega

/-- Required worst-case reserve for mutually exclusive observation branches. -/
def branchReserve : List (List Bound) → Nat
  | [] => 0
  | xs :: rest => max (optimalRepair xs) (branchReserve rest)

theorem branchReserve_le_iff (groups : List (List Bound)) (r : Nat) :
    branchReserve groups ≤ r ↔
      ∀ xs, xs ∈ groups → optimalRepair xs ≤ r := by
  induction groups with
  | nil =>
      simp [branchReserve]
  | cons xs rest ih =>
      simp only [branchReserve]
      constructor
      · intro h ys hy
        have hx : optimalRepair xs ≤ r := by omega
        have ht : branchReserve rest ≤ r := by omega
        rcases List.mem_cons.mp hy with heq | htail
        · subst ys
          exact hx
        · exact (ih.mp ht) ys htail
      · intro h
        have hx : optimalRepair xs ≤ r := h xs (by simp)
        have ht : branchReserve rest ≤ r := ih.mpr (by
          intro ys hy
          exact h ys (by simp [hy]))
        omega

/-- Exact robust budget for an observation with independent branch controls. -/
theorem adaptive_synthesis_iff
    (groups : List (List Bound)) (r : Nat) :
    (∀ xs, xs ∈ groups → ∃ u, Feasible xs u r) ↔
      branchReserve groups ≤ r := by
  constructor
  · intro h
    exact (branchReserve_le_iff groups r).mpr (by
      intro xs hxs
      exact (synthesis_iff_budget xs r).mp (h xs hxs))
  · intro h xs hxs
    exact (synthesis_iff_budget xs r).mpr
      ((branchReserve_le_iff groups r).mp h xs hxs)

end InsacermoSymbolic
