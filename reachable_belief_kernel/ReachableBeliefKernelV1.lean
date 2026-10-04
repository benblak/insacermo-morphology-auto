import Std

/-!
INSACERMO — Reachable Belief Kernel V1

Passive deterministic observation histories constrain a belief by conjunctions
of observation equalities.

Two local laws are fundamental:
1. compatible constraints commute;
2. repeating the exact same constraint is idempotent.

Therefore raw history length can overstate semantic history size.

We also define a syntactic partial-assignment code space for n probes with at
most m outcomes per probe. Each probe is either unobserved or assigned one of m
outcomes, hence the canonical code alphabet has size m+1.

This file proves the history invariances and the exact size of that canonical
code space. It does not yet prove that every runtime reachable belief has a
unique canonical code; that is a separate completeness/injectivity step.
-/

namespace InsacermoReachableBelief

abbrev Belief (W : Type) := W → Prop

structure Constraint (P O : Type) where
  probe : P
  outcome : O

def applyConstraint
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (c : Constraint P O) : Belief W :=
  fun w => B w ∧ observe c.probe w = c.outcome

def runHistory
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W) :
    List (Constraint P O) → Belief W
  | [] => B
  | c :: cs => runHistory observe (applyConstraint observe B c) cs

theorem applyConstraint_comm
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (c₁ c₂ : Constraint P O) :
    applyConstraint observe
      (applyConstraint observe B c₁) c₂ =
    applyConstraint observe
      (applyConstraint observe B c₂) c₁ := by
  funext w
  apply propext
  simp [applyConstraint, and_left_comm, and_assoc, and_comm]

theorem applyConstraint_idem
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (c : Constraint P O) :
    applyConstraint observe
      (applyConstraint observe B c) c =
    applyConstraint observe B c := by
  funext w
  apply propext
  simp [applyConstraint, and_assoc]

theorem history_adjacent_swap
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (pre suffix : List (Constraint P O))
    (c₁ c₂ : Constraint P O) :
    runHistory observe B
      (pre ++ c₁ :: c₂ :: suffix) =
    runHistory observe B
      (pre ++ c₂ :: c₁ :: suffix) := by
  induction pre generalizing B with
  | nil =>
      simp [runHistory, applyConstraint_comm]
  | cons h t ih =>
      simp only [List.cons_append, runHistory]
      exact ih (applyConstraint observe B h)

theorem history_duplicate_adjacent
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (pre suffix : List (Constraint P O))
    (c : Constraint P O) :
    runHistory observe B
      (pre ++ c :: c :: suffix) =
    runHistory observe B
      (pre ++ c :: suffix) := by
  induction pre generalizing B with
  | nil =>
      simp only [List.nil_append, runHistory]
      rw [applyConstraint_idem]
  | cons h t ih =>
      simp only [List.cons_append, runHistory]
      exact ih (applyConstraint observe B h)

/--
If one probe is constrained to two distinct outcomes, the resulting belief is
empty. This is why a nonempty deterministic history carries at most one outcome
per probe.
-/
theorem conflicting_same_probe_empty
    {W P O : Type} [DecidableEq O]
    (observe : P → W → O)
    (B : Belief W)
    (p : P)
    (o₁ o₂ : O)
    (hne : o₁ ≠ o₂) :
    applyConstraint observe
      (applyConstraint observe B ⟨p,o₁⟩)
      ⟨p,o₂⟩ =
    fun _ => False := by
  funext w
  apply propext
  constructor
  · intro h
    rcases h with ⟨⟨hB, h1⟩, h2⟩
    exact False.elim (hne (h1.symm.trans h2))
  · intro h
    exact False.elim h

/-- Extensional semantics of a history as the conjunction of all its constraints. -/
theorem runHistory_iff_all_constraints
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (history : List (Constraint P O))
    (w : W) :
    runHistory observe B history w ↔
      B w ∧
      ∀ c ∈ history, observe c.probe w = c.outcome := by
  induction history generalizing B with
  | nil =>
      simp [runHistory]
  | cons c cs ih =>
      simp [runHistory, ih, applyConstraint, and_assoc, and_left_comm, and_comm]

/-- The canonical partial assignment relation induced by a raw history. -/
def HistoryAssignment
    {P O : Type}
    (history : List (Constraint P O))
    (p : P)
    (o : O) : Prop :=
  ∃ c ∈ history, c.probe = p ∧ c.outcome = o

/--
A history's resulting belief depends only on its canonical partial assignment,
not on order or repeated syntax.
-/
theorem runHistory_iff_assignment
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (history : List (Constraint P O))
    (w : W) :
    runHistory observe B history w ↔
      B w ∧
      ∀ p o, HistoryAssignment history p o →
        observe p w = o := by
  rw [runHistory_iff_all_constraints]
  constructor
  · rintro ⟨hB, hall⟩
    refine ⟨hB, ?_⟩
    intro p o ha
    rcases ha with ⟨c, hc, hp, ho⟩
    subst p
    subst o
    exact hall c hc
  · rintro ⟨hB, hassignment⟩
    refine ⟨hB, ?_⟩
    intro c hc
    exact hassignment c.probe c.outcome ⟨c, hc, rfl, rfl⟩

/-- A realizable history is one satisfied by at least one possible world. -/
def RealizableHistory
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (history : List (Constraint P O)) : Prop :=
  ∃ w : W, runHistory observe B history w

/--
For a realizable deterministic history, the canonical assignment is a partial
function: one probe cannot carry two distinct outcomes.
-/
theorem realizable_assignment_single_valued
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (history : List (Constraint P O))
    (hreal : RealizableHistory observe B history) :
    ∀ p o₁ o₂,
      HistoryAssignment history p o₁ →
      HistoryAssignment history p o₂ →
      o₁ = o₂ := by
  rcases hreal with ⟨w, hw⟩
  have hsem := (runHistory_iff_assignment observe B history w).mp hw
  intro p o₁ o₂ h1 h2
  have ho1 := hsem.2 p o₁ h1
  have ho2 := hsem.2 p o₂ h2
  exact ho1.symm.trans ho2

/--
If two raw histories induce exactly the same partial assignment relation, they
produce exactly the same belief. This is the canonical reachability
factorization theorem.
-/
theorem same_assignment_same_belief
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (h₁ h₂ : List (Constraint P O))
    (hsame : ∀ p o,
      HistoryAssignment h₁ p o ↔ HistoryAssignment h₂ p o) :
    runHistory observe B h₁ =
      runHistory observe B h₂ := by
  funext w
  apply propext
  constructor
  · intro hw
    have hsem := (runHistory_iff_assignment observe B h₁ w).mp hw
    apply (runHistory_iff_assignment observe B h₂ w).mpr
    refine ⟨hsem.1, ?_⟩
    intro p o ha
    exact hsem.2 p o ((hsame p o).mpr ha)
  · intro hw
    have hsem := (runHistory_iff_assignment observe B h₂ w).mp hw
    apply (runHistory_iff_assignment observe B h₁ w).mpr
    refine ⟨hsem.1, ?_⟩
    intro p o ha
    exact hsem.2 p o ((hsame p o).mp ha)

/--
Reachability factorization summary:
every realizable raw history induces a single-valued partial assignment, and
the resulting belief is determined extensionally by that assignment alone.
-/
theorem canonical_reachability_factorization
    {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (history : List (Constraint P O))
    (hreal : RealizableHistory observe B history) :
    (∀ p o₁ o₂,
      HistoryAssignment history p o₁ →
      HistoryAssignment history p o₂ →
      o₁ = o₂) ∧
    (∀ w : W,
      runHistory observe B history w ↔
        B w ∧
        ∀ p o, HistoryAssignment history p o →
          observe p w = o) := by
  constructor
  · exact realizable_assignment_single_valued observe B history hreal
  · intro w
    exact runHistory_iff_assignment observe B history w

/--
Canonical syntactic code space.
For each of n probes, a digit 0 means "not observed" and digits 1..m encode one
of at most m outcomes. Thus each coordinate has alphabet size m+1.
-/
def partialCodes (alphabet : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
      (List.range alphabet).flatMap
        (fun a => (partialCodes alphabet n).map (fun xs => a :: xs))

theorem flatMap_const_length
    {α β : Type}
    (xs : List α)
    (f : α → List β)
    (k : Nat)
    (h : ∀ x ∈ xs, (f x).length = k) :
    (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : (f x).length = k := h x (by simp)
      have ht : ∀ y ∈ xs, (f y).length = k := by
        intro y hy
        exact h y (by simp [hy])
      calc
        ((x :: xs).flatMap f).length
            = (f x).length + (xs.flatMap f).length := by simp
        _ = k + xs.length * k := by rw [hx, ih ht]
        _ = (xs.length + 1) * k := by
              simp [Nat.add_mul, Nat.add_comm]

theorem partialCodes_length
    (alphabet : Nat) :
    ∀ n : Nat,
      (partialCodes alphabet n).length = alphabet ^ n := by
  intro n
  induction n with
  | zero =>
      simp [partialCodes]
  | succ n ih =>
      let f : Nat → List (List Nat) :=
        fun a => (partialCodes alphabet n).map (fun xs => a :: xs)
      have hf :
          ∀ a ∈ List.range alphabet,
            (f a).length = alphabet ^ n := by
        intro a ha
        simp [f, ih]
      calc
        (partialCodes alphabet (n + 1)).length
            = (List.range alphabet).length * (alphabet ^ n) := by
                simpa [partialCodes, f] using
                  flatMap_const_length (List.range alphabet) f
                    (alphabet ^ n) hf
        _ = alphabet * (alphabet ^ n) := by simp
        _ = alphabet ^ (n + 1) := by
              rw [Nat.pow_succ]
              exact Nat.mul_comm _ _

theorem canonical_history_code_count
    (probeCount outcomeBound : Nat) :
    (partialCodes (outcomeBound + 1) probeCount).length =
      (outcomeBound + 1) ^ probeCount := by
  exact partialCodes_length (outcomeBound + 1) probeCount

#print axioms applyConstraint_comm
#print axioms applyConstraint_idem
#print axioms history_adjacent_swap
#print axioms history_duplicate_adjacent
#print axioms conflicting_same_probe_empty
#print axioms runHistory_iff_all_constraints
#print axioms runHistory_iff_assignment
#print axioms realizable_assignment_single_valued
#print axioms same_assignment_same_belief
#print axioms canonical_reachability_factorization
#print axioms partialCodes_length
#print axioms canonical_history_code_count

end InsacermoReachableBelief
