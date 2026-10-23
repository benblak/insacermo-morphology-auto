import C3.PortableExactSearchV1

/- INSACERMO finite self-audit: a recoverable capability is not always
   a robustly actionable one. Historical C3 files unchanged. -/
namespace INSACERMO.Recoverability
open PortableC3

def start : List Nat := [0,1]

def outOfPhase : Model := {
  worldCount := 2
  actionCount := 1
  probeCount := 1
  good := [[true],[false]]
  sense := [[3,3]]
  nextFalse := [[1,0]]
  nextTrue := [[1,0]]
  actionCost := [0]
  probeCost := [0]
}

def resetBoth : Model := {
  worldCount := 2
  actionCount := 1
  probeCount := 1
  good := [[true],[false]]
  sense := [[3,3]]
  nextFalse := [[0,0]]
  nextTrue := [[0,0]]
  actionCost := [0]
  probeCost := [0]
}

def distinguishingProbe : Model := {
  worldCount := 2
  actionCount := 2
  probeCount := 1
  good := [[true,false],[false,true]]
  sense := [[1,2]]
  nextFalse := [[0,1]]
  nextTrue := [[0,1]]
  actionCost := [0,0]
  probeCost := [0]
}

def tick (m : Model) (X : List Nat) : List Nat := after m X 0 false
def orbit (m : Model) (X : List Nat) : Nat → List Nat
  | 0 => X
  | n+1 => tick m (orbit m X n)

set_option maxRecDepth 8192
set_option maxHeartbeats 100000000

theorem all_models_well_formed :
    wellFormed outOfPhase start = true ∧
    wellFormed resetBoth start = true ∧
    wellFormed distinguishingProbe start = true := by
  decide +kernel

def phaseTrap (X : List Nat) : Prop :=
    X = [0,1] ∨ X = [1,0]

theorem phase_trap_closed (X : List Nat)
    (hX : phaseTrap X) : phaseTrap (tick outOfPhase X) := by
  rcases hX with h | h
  · right
    rw [h]
    decide +kernel
  · left
    rw [h]
    decide +kernel

theorem phase_trap_blocks_action (X : List Nat)
    (hX : phaseTrap X) : direct outOfPhase 0 X = false := by
  rcases hX with h | h
  · rw [h]
    decide +kernel
  · rw [h]
    decide +kernel

theorem closed_trap_prevents_recovery
    (m : Model) (initial : List Nat) (P : List Nat → Prop)
    (hinitial : P initial)
    (hclosed : ∀ X, P X → P (tick m X))
    (hblocked : ∀ X, P X → direct m 0 X = false)
    (n : Nat) :
    direct m 0 (orbit m initial n) = false := by
  have hP : ∀ t, P (orbit m initial t) := by
    intro t
    induction t with
    | zero => exact hinitial
    | succ t ih => exact hclosed _ ih
  exact hblocked _ (hP n)

theorem robust_action_blocked_at_all_horizons (n : Nat) :
    direct outOfPhase 0 (orbit outOfPhase start n) = false :=
  closed_trap_prevents_recovery outOfPhase start phaseTrap
    (Or.inl rfl) phase_trap_closed phase_trap_blocks_action n

theorem different_worlds_have_different_good_times :
    direct outOfPhase 0 [0] = true ∧
    direct outOfPhase 0 (tick outOfPhase [1]) = true ∧
    direct outOfPhase 0 start = false := by
  decide +kernel

theorem noninformative_transition_restores_common_action :
    direct resetBoth 0 start = false ∧
    direct resetBoth 0 (tick resetBoth start) = true := by
  decide +kernel

theorem perfect_sensing_can_enable_contingent_action :
    direct distinguishingProbe 0 start = false ∧
    checkTree distinguishingProbe 1 0 start
      (.probe 0 (.act 0) (.act 1)) = true := by
  decide +kernel

theorem sensed_action_safe :
    Safe distinguishingProbe 1 0 start
      (.probe 0 (.act 0) (.act 1)) :=
  accepted_certificate_sound distinguishingProbe 1 0 start
    (.probe 0 (.act 0) (.act 1))
    (by decide +kernel)

end INSACERMO.Recoverability
