import labs.refus_espoir_20261119.RefusEspoirBridge

namespace INSACERMO.AntimatterToy
open INSACERMO.RefusEspoir

/-- All seven worlds below are SYNTHETIC mechanism signatures.
    They are NOT numerical predictions of real baryogenesis theories. -/
def family (w : Fin 7) : Fin 5 :=
  match w.val with
  | 0 | 1 => 0
  | 2 | 3 => 1
  | 4 => 2
  | 5 => 3
  | _ => 4

def correct (w : Fin 7) (a : Fin 5) : Prop := a = family w

/-- Four entirely invented future-observation outcomes. -/
def observedFour (w : Fin 7) : Bool × Bool × Bool × Bool :=
  match w.val with
  | 0 => (true,  false, true,  false)
  | 1 => (true,  true,  true,  false)
  | 2 => (false, true,  false, false)
  | 3 => (true,  true,  false, true)
  | 4 => (false, false, false, true)
  | 5 => (false, false, false, false)
  | _ => (true,  false, true,  false)

/-- An idealized fifth probe separates world 6 from its observational twin.
    This is an abstract observation, not a real instrument. -/
def hypotheticalExtra (w : Fin 7) : Bool := w.val == 6

def observedFive (w : Fin 7) :=
  (observedFour w, hypotheticalExtra w)

/-- A world imitating the first four probes blocks mechanism identification. -/
theorem four_probes_cannot_identify :
    ¬ Safe correct observedFour := by
  apply collision_forces_refusal correct observedFour (0 : Fin 7) (6 : Fin 7)
  · decide
  · intro a h
    have h0 : a = (0 : Fin 5) := by simpa [correct, family] using h.1
    have h6 : a = (4 : Fin 5) := by simpa [correct, family] using h.2
    have hc : (0 : Fin 5) = (4 : Fin 5) := h0.symm.trans h6
    exact (by decide : (0 : Fin 5) ≠ (4 : Fin 5)) hc

/-- Every future probe family still tying worlds 0 and 6 is insufficient.
    This generalizes the obstruction to an arbitrary observational language. -/
theorem tied_worlds_forbid_any_observation {O : Type}
    (obs : Fin 7 → O) (h : obs 0 = obs 6) :
    ¬ Safe correct obs := by
  apply collision_forces_refusal correct obs (0 : Fin 7) (6 : Fin 7) h
  intro a hs
  have h0 : a = (0 : Fin 5) := by simpa [correct, family] using hs.1
  have h6 : a = (4 : Fin 5) := by simpa [correct, family] using hs.2
  have hc : (0 : Fin 5) = (4 : Fin 5) := h0.symm.trans h6
  exact (by decide : (0 : Fin 5) ≠ (4 : Fin 5)) hc

/-- In this invented benchmark, an extra perfect distinguishing probe
    suffices to identify the FAMILY (not the exact parameter benchmark). -/
def policyFive (z : (Bool × Bool × Bool × Bool) × Bool) : Fin 5 :=
  if z.2 then 4
  else if z.1 == (true, false, true, false) then 0
  else if z.1 == (true, true, true, false) then 0
  else if z.1 == (false, true, false, false) then 1
  else if z.1 == (true, true, false, true) then 1
  else if z.1 == (false, false, false, true) then 2
  else 3

theorem idealized_fifth_probe_allows_identification :
    Safe correct observedFive := by
  refine ⟨policyFive, ?_⟩
  decide

/-- No observation is needed to execute an action equally safe in every
    declared world: mechanism identification is a strictly stronger contract. -/
def commonSafe (_w : Fin 7) (_a : Unit) : Prop := True
theorem contract_without_identification : Safe commonSafe observedFour := by
  exact ⟨fun _ => (), fun _ => trivial⟩

end INSACERMO.AntimatterToy
