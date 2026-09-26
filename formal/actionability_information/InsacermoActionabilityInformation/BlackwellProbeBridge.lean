import InsacermoActionabilityInformation.BiMonotone
import Mathlib

namespace InsacermoActionabilityInformation

namespace BlackwellProbeBridge

universe u v w z

/-- For a fixed action type, the fine representation dominates the coarse one
for INSACERMO safety when every decision problem that is safe under the coarse
representation remains safe under the fine representation. -/
def SafeDominatesFor
    {S : Type u} {A : Type v} {YFine : Type w} {YCoarse : Type z}
    (fine : S → YFine) (coarse : S → YCoarse) : Prop :=
  ∀ (Good : S → A → Prop) (B : Set S) (C : Set A),
    SafeRep Good B C coarse → SafeRep Good B C fine

/-- Deterministic garbling/refinement implies universal safety dominance.
This is the INSACERMO analogue of the easy direction of Blackwell monotonicity:
a coarse signal reproducible from a fine signal cannot support a safe decision
problem that the fine signal cannot also support. -/
theorem refines_implies_safeDominatesFor
    {S : Type u} {A : Type v} {YFine : Type w} {YCoarse : Type z}
    {fine : S → YFine} {coarse : S → YCoarse}
    (href : Refines fine coarse) :
    SafeDominatesFor (A := A) fine coarse := by
  intro Good B C hsafe
  exact safeRep_information_mono hsafe href

/-- Fiber refinement: indistinguishable worlds under the fine signal must also
be indistinguishable under the coarse signal. -/
def FiberRefines
    {S : Type u} {YFine : Type w} {YCoarse : Type z}
    (fine : S → YFine) (coarse : S → YCoarse) : Prop :=
  ∀ s t, fine s = fine t → coarse s = coarse t

/-- Deterministic factorization implies fiber refinement. -/
theorem refines_implies_fiberRefines
    {S : Type u} {YFine : Type w} {YCoarse : Type z}
    {fine : S → YFine} {coarse : S → YCoarse}
    (href : Refines fine coarse) :
    FiberRefines fine coarse := by
  rcases href with ⟨f, hf⟩
  intro s t hst
  rw [hf s, hf t, hst]

/-- If the coarse signal space is inhabited, fiber refinement is sufficient to
construct the deterministic garbling map. -/
theorem fiberRefines_implies_refines
    {S : Type u} {YFine : Type w} {YCoarse : Type z}
    [Nonempty YCoarse]
    {fine : S → YFine} {coarse : S → YCoarse}
    (hker : FiberRefines fine coarse) :
    Refines fine coarse := by
  classical
  let default : YCoarse := Classical.choice (inferInstance : Nonempty YCoarse)
  let f : YFine → YCoarse := fun y =>
    if h : ∃ s, fine s = y then coarse (Classical.choose h) else default
  refine ⟨f, ?_⟩
  intro s
  have hex : ∃ t, fine t = fine s := ⟨s, rfl⟩
  rw [show f (fine s) = coarse (Classical.choose hex) by
    simp [f, hex]]
  exact hker s (Classical.choose hex) (Classical.choose_spec hex).symm

/-- Exact-code decision problem associated with a representation: the action
must reproduce the coarse code of the true world. -/
def GoodCoarseCode
    {S : Type u} {Y : Type v}
    (coarse : S → Y) (s : S) (a : Y) : Prop :=
  coarse s = a

/-- Every representation is safe for its own exact-code decision problem. -/
theorem coarse_safe_for_own_code
    {S : Type u} {Y : Type v}
    (coarse : S → Y) :
    SafeRep (GoodCoarseCode coarse) Set.univ Set.univ coarse := by
  intro y hy
  refine ⟨y, by simp, ?_⟩
  intro s hs hsy
  exact hsy

/-- Universal INSACERMO safety dominance for the coarse-code action type forces
fiber refinement.  A failure of fiber refinement is exposed by the exact-code
decision problem. -/
theorem safeDominatesFor_implies_fiberRefines
    {S : Type u} {YFine : Type w} {YCoarse : Type z}
    {fine : S → YFine} {coarse : S → YCoarse}
    (hdom : SafeDominatesFor (A := YCoarse) fine coarse) :
    FiberRefines fine coarse := by
  have hsafeFine :
      SafeRep (GoodCoarseCode coarse) Set.univ Set.univ fine :=
    hdom (GoodCoarseCode coarse) Set.univ Set.univ
      (coarse_safe_for_own_code coarse)
  intro s t hst
  rcases hsafeFine (fine s) ⟨s, by simp, rfl⟩ with ⟨a, ha, hall⟩
  have hs : coarse s = a := hall s (by simp) rfl
  have ht : coarse t = a := hall t (by simp) hst.symm
  exact hs.trans ht.symm

/-- Deterministic Blackwell-style characterization inside the INSACERMO
SafeRep semantics.

When the coarse signal space is inhabited, deterministic garbling/factorization
is equivalent to preserving safety for every Good/B/C decision problem with
the coarse signal space available as the action space. -/
theorem deterministic_refines_iff_safeDominates
    {S : Type u} {YFine : Type w} {YCoarse : Type z}
    [Nonempty YCoarse]
    {fine : S → YFine} {coarse : S → YCoarse} :
    Refines fine coarse ↔
      SafeDominatesFor (A := YCoarse) fine coarse := by
  constructor
  · exact refines_implies_safeDominatesFor
  · intro hdom
    exact fiberRefines_implies_refines
      (safeDominatesFor_implies_fiberRefines hdom)

/-- Contract-relative usefulness of one information move. -/
def UsefulProbeFor
    {S : Type u} {A : Type v} {YFrom : Type w} {YTo : Type z}
    (Good : S → A → Prop) (B : Set S) (C : Set A)
    (fromObs : S → YFrom) (toObs : S → YTo) : Prop :=
  ¬ SafeRep Good B C fromObs ∧ SafeRep Good B C toObs

/-! ### Incomparable information structures with contract-relative value -/

inductive FourWorld
  | w00 | w01 | w10 | w11
  deriving DecidableEq, Fintype

inductive Bit
  | zero | one
  deriving DecidableEq, Fintype

open FourWorld Bit

def firstObs : FourWorld → Bit
  | w00 | w01 => zero
  | w10 | w11 => one

def secondObs : FourWorld → Bit
  | w00 | w10 => zero
  | w01 | w11 => one

/-- The first-bit experiment does not refine the second-bit experiment. -/
theorem first_not_refines_second :
    ¬ Refines firstObs secondObs := by
  intro href
  have hker := refines_implies_fiberRefines href
  have h := hker w00 w01 rfl
  simp [secondObs] at h

/-- The second-bit experiment does not refine the first-bit experiment. -/
theorem second_not_refines_first :
    ¬ Refines secondObs firstObs := by
  intro href
  have hker := refines_implies_fiberRefines href
  have h := hker w00 w10 rfl
  simp [firstObs] at h

def GoodFirst (s : FourWorld) (a : Bit) : Prop :=
  firstObs s = a

def GoodSecond (s : FourWorld) (a : Bit) : Prop :=
  secondObs s = a

theorem first_safe_for_first_contract :
    SafeRep GoodFirst Set.univ Set.univ firstObs := by
  change SafeRep (GoodCoarseCode firstObs) Set.univ Set.univ firstObs
  exact coarse_safe_for_own_code firstObs

theorem second_not_safe_for_first_contract :
    ¬ SafeRep GoodFirst Set.univ Set.univ secondObs := by
  intro hsafe
  rcases hsafe zero ⟨w00, by simp, rfl⟩ with ⟨a, ha, hall⟩
  have h00 : GoodFirst w00 a := hall w00 (by simp) rfl
  have h10 : GoodFirst w10 a := hall w10 (by simp) rfl
  cases a <;> simp [GoodFirst, firstObs] at h00 h10

theorem second_safe_for_second_contract :
    SafeRep GoodSecond Set.univ Set.univ secondObs := by
  change SafeRep (GoodCoarseCode secondObs) Set.univ Set.univ secondObs
  exact coarse_safe_for_own_code secondObs

theorem first_not_safe_for_second_contract :
    ¬ SafeRep GoodSecond Set.univ Set.univ firstObs := by
  intro hsafe
  rcases hsafe zero ⟨w00, by simp, rfl⟩ with ⟨a, ha, hall⟩
  have h00 : GoodSecond w00 a := hall w00 (by simp) rfl
  have h01 : GoodSecond w01 a := hall w01 (by simp) rfl
  cases a <;> simp [GoodSecond, secondObs] at h00 h01

/-- Two Blackwell-incomparable deterministic observations can each be the
useful PROBE for a different declared contract.

This is the formal separation between universal information dominance and
INSACERMO's contract-relative value of information. -/
theorem incomparable_probes_have_contract_relative_value :
    (¬ Refines firstObs secondObs) ∧
    (¬ Refines secondObs firstObs) ∧
    UsefulProbeFor GoodFirst Set.univ Set.univ secondObs firstObs ∧
    UsefulProbeFor GoodSecond Set.univ Set.univ firstObs secondObs := by
  exact ⟨first_not_refines_second,
    second_not_refines_first,
    ⟨second_not_safe_for_first_contract, first_safe_for_first_contract⟩,
    ⟨first_not_safe_for_second_contract, second_safe_for_second_contract⟩⟩

end BlackwellProbeBridge

end InsacermoActionabilityInformation
