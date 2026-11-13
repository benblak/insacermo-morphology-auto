/-
INSACERMO five-world exact minimum probe audit, 2026-11-13.
Independent toy model, not an empirical OpenFlights statement.
Lean 4.20, core Init only. Total Boolean enumeration is kernel-reduced.
-/
import Init

namespace InsacermoFiveWorld

abbrev Selection := Bool × Bool × Bool × Bool

def selected (s : Selection) (i : Fin 4) : Bool :=
  if i.val == 0 then s.1
  else if i.val == 1 then s.2.1
  else if i.val == 2 then s.2.2.1
  else s.2.2.2

/-- Explicitly enumerated worlds 0..4 and four failure-probes. -/
def worlds : List (Fin 5) := [0, 1, 2, 3, 4]
def probes : List (Fin 4) := [0, 1, 2, 3]

def answer (i : Fin 4) (w : Fin 5) : Bool :=
  decide (w.val = i.val + 1)

/-- Each selected probe must return an identical answer in two worlds. -/
def sameSignature (s : Selection) (w u : Fin 5) : Bool :=
  probes.all (fun i => !selected s i || (answer i w == answer i u))

/-- Fixing a broken link is safe if the network is intact or exactly
that link has failed (the only possibilities in this toy model). -/
def repairWorks (i : Fin 4) (w : Fin 5) : Bool :=
  (w.val == 0) || (w.val == i.val + 1)

/-- For each actual world, at least one repair succeeds in every world
consistent with its probe signature. -/
def guaranteedAction (s : Selection) : Bool :=
  worlds.all (fun w =>
    probes.any (fun i =>
      worlds.all (fun u =>
        !sameSignature s w u || repairWorks i u)))

def count (s : Selection) : Nat :=
  (if s.1 then 1 else 0) +
  (if s.2.1 then 1 else 0) +
  (if s.2.2.1 then 1 else 0) +
  (if s.2.2.2 then 1 else 0)

/-- Full 16-case verification of the exact optimum. The proof uses structural case splits and Lean's ordinary kernel evaluation. -/
theorem exact_minimum_three :
    ∀ s : Selection, guaranteedAction s = true ↔ 3 ≤ count s := by
  intro ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def threeProbes : Selection := (true, true, true, false)

theorem three_suffice : guaranteedAction threeProbes = true := by decide
theorem three_are_used : count threeProbes = 3 := by decide

theorem two_never_suffice :
    ∀ s : Selection, count s ≤ 2 → guaranteedAction s = false := by
  intro s h
  have heq := (exact_minimum_three s)
  cases hs : guaranteedAction s with
  | false => rfl
  | true =>
      have hthree : 3 ≤ count s := heq.mp hs
      have hlt : count s < 3 := Nat.lt_of_le_of_lt h (by decide : 2 < 3)
      exact False.elim (Nat.not_le_of_gt hlt hthree)

#print axioms exact_minimum_three
#print axioms three_suffice
#print axioms three_are_used
#print axioms two_never_suffice
end InsacermoFiveWorld
