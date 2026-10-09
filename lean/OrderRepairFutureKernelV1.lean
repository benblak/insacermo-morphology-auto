import Std
namespace INSACERMO.OrderRepairFuture
structure Option where
  cost : Nat
  nowMask : Nat
  futureMask : Nat
def acts (ops : List Option) (reserve debt : Nat) (future : Bool) (belief : Nat) : Bool :=
  ops.any (fun o => decide (debt + o.cost < reserve) &&
    (Nat.land belief (if future then Nat.land o.nowMask o.futureMask else o.nowMask) == belief))
def minimalCore (ops : List Option) (reserve debt : Nat) (future : Bool) (belief : Nat) : Bool :=
  !acts ops reserve debt future belief &&
  (List.range 3).all (fun w =>
    if belief.testBit w then acts ops reserve debt future (Nat.land belief (7 - 2^w)) else true)
def cores (ops : List Option) (reserve debt : Nat) (future : Bool) : List Nat :=
  ((List.range 7).map (fun i => i+1)).filter (minimalCore ops reserve debt future)
def base : List Option := [⟨0,1,1⟩,⟨0,2,2⟩,⟨0,4,4⟩]
def pairs : List Option := base ++ [⟨1,3,3⟩,⟨1,5,5⟩,⟨1,6,6⟩]
def destructive : List Option := pairs ++ [⟨3,7,3⟩]
def safe : List Option := destructive ++ [⟨3,7,7⟩]
theorem baseline_order_two : cores base 1 0 true = [3,5,6] := by decide +kernel
theorem repairs_raise_order_to_three : cores pairs 2 0 true = [7] := by decide +kernel
theorem debt_restores_order_two : cores pairs 2 1 true = [3,5,6] := by decide +kernel
theorem immediate_act_future_refuse :
  acts destructive 4 0 false 7 = true ∧
  acts destructive 4 0 true 7 = false := by decide +kernel
theorem safe_global_repair_allows_act : acts safe 4 0 true 7 = true := by decide +kernel
theorem strict_reserve_equality_refuses : acts safe 3 0 true 7 = false := by decide +kernel
theorem optional_capability_preserves_act {α : Type} (ops : List α) (newOp : α)
 (ok : α → Prop) (h : ∃ x ∈ ops, ok x) : ∃ x ∈ newOp :: ops, ok x := by
  obtain ⟨x,hmem,hOk⟩ := h
  exact ⟨x,List.mem_cons_of_mem _ hmem,hOk⟩
end INSACERMO.OrderRepairFuture
