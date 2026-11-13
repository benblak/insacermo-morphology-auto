/-
INSACERMO -- Exact minimum of reliable probes in the five-world toy model.
Lean 4.20 / Init only / independent kernel checked computation.
No Mathlib, no sorry, no native_decide.
The five worlds and four indicator probes are explicitly fixed.
This is NOT a universal optimal-probing theorem, nor a proof for noisy probes.
-/
import Init

namespace InsacermoFiveWorld

/-- Four optional binary probes, one per critical failure. -/
abbrev Selection := Bool × Bool × Bool × Bool

/-- Probe i is enabled when its corresponding flag is true. -/
def selected (s : Selection) (i : Fin 4) : Bool :=
  if i.val == 0 then s.1
  else if i.val == 1 then s.2.1
  else if i.val == 2 then s.2.2.1
  else s.2.2.2

/-- World 0 is intact; worlds 1--4 are the four single-failure cases. -/
def answer (i : Fin 4) (w : Fin 5) : Bool :=
  decide (w.val = i.val + 1)

/-- Two worlds are indistinguishable using the selected probes. -/
def sameSignature (s : Selection) (w u : Fin 5) : Prop :=
  ∀ i : Fin 4, selected s i = true → answer i w = answer i u

/-- A targeted repair i succeeds in world 0 or in world i+1. -/
def repairWorks (i : Fin 4) (w : Fin 5) : Prop :=
  w.val = 0 ∨ w.val = i.val + 1

/-- Each observation class must admit one targeted repair that works
for all remaining possible worlds. -/
def guaranteedAction (s : Selection) : Prop :=
  ∀ w : Fin 5, ∃ i : Fin 4,
    ∀ u : Fin 5, sameSignature s w u → repairWorks i u

/-- The number of distinct probes selected (each used once). -/
def count (s : Selection) : Nat :=
  (if s.1 then 1 else 0) +
  (if s.2.1 then 1 else 0) +
  (if s.2.2.1 then 1 else 0) +
  (if s.2.2.2 then 1 else 0)

/-- Exact exhaustive theorem over all 16 choices of four probes:
a guaranteed action is possible iff at least three distinct probes
were selected. This is checked by kernel-reduced `decide`, not an axiom. -/
theorem exact_minimum_three :
    ∀ s : Selection, guaranteedAction s ↔ 3 ≤ count s := by
  decide

/-- A concrete three-probe witness. -/
def threeProbes : Selection := (true, true, true, false)

theorem three_suffice : guaranteedAction threeProbes := by decide
theorem three_are_used : count threeProbes = 3 := by decide

/-- Another explicit finite statement: two fixed probes never suffice. -/
theorem two_never_suffice :
    ∀ s : Selection, count s ≤ 2 → ¬ guaranteedAction s := by
  decide

#print axioms exact_minimum_three
#print axioms three_suffice
#print axioms three_are_used
#print axioms two_never_suffice

end InsacermoFiveWorld
