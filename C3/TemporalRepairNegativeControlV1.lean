import C3.TotalHistoricalMultiProbeIntegrationV1

/-!
Regression: two actions both meet the SAME current LP contract; one destroys
the actual historical temporal future. This is a negative control proving
that a bad future candidate cannot accidentally be "certified" as an ACT.
-/
namespace INSACERMO.Regression
open INSACERMO.TotalHistoricalMulti
open INSACERMO.TotalRepairFuture
open INSACERMO.LegacyC3Repair
open INSACERMO.RecursiveC3
open INSACERMO.C3PP
open InsacermoExactRepair
open InsacermoMultiProbeBudget

def A : Nat → Nat → Nat := fun i j =>
  if i == 0 && j < 2 then 10 else 0
def b : Nat → Nat := fun i => if i == 0 then 1 else 0
def allowed : Nat → Bool := fun _ => true

def goodRecipe : Recipe :=
  ⟨fun j => if j == 1 then 1 else 0, 10⟩
def badRecipe : Recipe :=
  ⟨fun j => if j == 0 then 1 else 0, 10⟩

def bad0 : Bool → Prop := fun s => s = true
def badt : Bool → Prop := bad0
def dist (x y : Bool) : Nat := if x == y then 0 else 2
def state (_ : Unit) (p : Recipe) : Bool := p.amount 0 == 1

def m : DynamicProblem Unit Recipe Unit Bool :=
  repairModel 1 2 A b allowed (HistoricalFuture bad0 dist 0 state)
    (fun _ => True) (fun _ => 1)
    (fun _ _ _ => True) (fun _ _ w => w)

theorem both_repairs_satisfy_current_contract :
    checkPrimal 1 2 A b allowed goodRecipe.amount goodRecipe.denominator = true ∧
    checkPrimal 1 2 A b allowed badRecipe.amount badRecipe.denominator = true := by
  decide +kernel

theorem good_can_be_certified :
    PlanValid m 0 0 (fun _ => True) (.act goodRecipe) := by
  apply certified_repair_constructive
    1 2 A b allowed (HistoricalFuture bad0 dist 0 state)
    (fun _ => True) (fun _ => 1)
    (fun _ _ _ => True) (fun _ _ w => w)
    goodRecipe (fun _ => True) 0 0
  · decide
  · decide +kernel
  · decide +kernel
  · intro s hs
    intro b0 hb0
    cases s
    cases b0 with
    | false =>
        exact False.elim (Bool.noConfusion hb0)
    | true =>
        decide

theorem bad_fails_future_contract :
    ¬ PlanValid m 0 0 (fun _ => True) (.act badRecipe) := by
  intro h
  have hg := h.2.2 () trivial
  have hf := hg.2.2
  have hz : INSACERMO.TemporalValidityV1.Safe bad0 dist 0 (state () badRecipe) := hf
  have hb : bad0 true := rfl
  have inequality := hz true hb
  exact (by decide : ¬ (0 < dist (state () badRecipe) true)) inequality

theorem equal_to_reserve_must_refuse :
    ¬ PlanAffordable 1 0 [1] := by
  simp [PlanAffordable, debtAfterPlan]

end INSACERMO.Regression
