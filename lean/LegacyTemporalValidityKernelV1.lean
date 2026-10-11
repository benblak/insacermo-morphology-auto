namespace INSACERMO.TemporalValidityV1

/--
A point x is safe at debt budget D when every reference-bad point b0
is strictly farther than D under the declared distance-like map d.
No metric axioms are required for this minimal kernel statement.
-/
def Safe {X : Type u}
    (bad0 : X → Prop) (d : X → X → Nat) (D : Nat) (x : X) : Prop :=
  ∀ b0, bad0 b0 → D < d x b0

/--
TEMPORAL RESERVE / DEBT THEOREM.

If every current-bad point lies within directed debt D of some
reference-bad point, and x has reserve strictly greater than D
against every reference-bad point, then x is not current-bad.
-/
theorem safe_of_directed_debt
    {X : Type u}
    (bad0 badt : X → Prop)
    (d : X → X → Nat)
    (D : Nat) (x : X)
    (hdebt :
      ∀ b, badt b → ∃ b0, bad0 b0 ∧ d b b0 ≤ D)
    (hreserve : Safe bad0 d D x) :
    ¬ badt x := by
  intro hx
  obtain ⟨b0, hb0, hclose⟩ := hdebt x hx
  have hfar : D < d x b0 := hreserve b0 hb0
  exact (Nat.not_lt_of_ge hclose) hfar

/--
FILTRATION / ANTITONICITY THEOREM.

A larger temporal debt budget can only shrink the safe region:
if x is safe against D2 and D1 ≤ D2, then x is safe against D1.
-/
theorem safe_antitone_debt
    {X : Type u}
    (bad0 : X → Prop)
    (d : X → X → Nat)
    {D1 D2 : Nat}
    (hD : D1 ≤ D2)
    {x : X}
    (hsafe : Safe bad0 d D2 x) :
    Safe bad0 d D1 x := by
  intro b0 hb0
  have h2 : D2 < d x b0 := hsafe b0 hb0
  exact Nat.lt_of_le_of_lt hD h2

/--
OBSERVER FRACTURE THEOREM.

If two worlds have the same observation but require different actions,
no deterministic observation-only policy can be correct on both.
-/
theorem observer_fracture_no_policy
    {World : Type u} {Obs : Type v} {Action : Type w}
    (phi : World → Obs)
    (req : World → Action)
    (x y : World)
    (hphi : phi x = phi y)
    (hreq : req x ≠ req y) :
    ¬ ∃ policy : Obs → Action,
      policy (phi x) = req x ∧
      policy (phi y) = req y := by
  intro h
  obtain ⟨policy, hx, hy⟩ := h
  apply hreq
  calc
    req x = policy (phi x) := hx.symm
    _ = policy (phi y) := congrArg policy hphi
    _ = req y := hy

/--
Observation-only monitors produce the same output on identical
observation traces.
-/
theorem observation_only_monitor_same_output
    {Time : Type u} {Obs : Type v} {Verdict : Type w}
    (obs₁ obs₂ : Time → Obs)
    (monitor : (Time → Obs) → Time → Verdict)
    (t : Time)
    (hobs : obs₁ = obs₂) :
    monitor obs₁ t = monitor obs₂ t := by
  cases hobs
  rfl

/--
TEMPORAL INDISTINGUISHABILITY THEOREM.

If two temporal worlds expose exactly the same observation trace but
require different actions at time t, no observation-only monitor can
be correct on both at t.
-/
theorem temporal_observation_only_no_common_correctness
    {Time : Type u} {Obs : Type v} {Action : Type w}
    (obs₁ obs₂ : Time → Obs)
    (req₁ req₂ : Time → Action)
    (monitor : (Time → Obs) → Time → Action)
    (t : Time)
    (hobs : obs₁ = obs₂)
    (hreq : req₁ t ≠ req₂ t) :
    ¬ (monitor obs₁ t = req₁ t ∧
       monitor obs₂ t = req₂ t) := by
  intro h
  apply hreq
  calc
    req₁ t = monitor obs₁ t := h.1.symm
    _ = monitor obs₂ t :=
      observation_only_monitor_same_output obs₁ obs₂ monitor t hobs
    _ = req₂ t := h.2

/-
Concrete finite witness in the same logical form as the Occupancy
observer-fracture certificate: same complete observation, incompatible
required actions.
-/
inductive WitnessWorld where
  | w0
  | w1
deriving DecidableEq

def witnessObs : WitnessWorld → Nat
  | .w0 => 0
  | .w1 => 0

def witnessReq : WitnessWorld → Bool
  | .w0 => false
  | .w1 => true

theorem occupancy_style_observer_fracture :
    ¬ ∃ policy : Nat → Bool,
      policy (witnessObs .w0) = witnessReq .w0 ∧
      policy (witnessObs .w1) = witnessReq .w1 := by
  exact observer_fracture_no_policy
    witnessObs witnessReq .w0 .w1 rfl (by decide)

#print axioms safe_of_directed_debt
#print axioms safe_antitone_debt
#print axioms observer_fracture_no_policy
#print axioms observation_only_monitor_same_output
#print axioms temporal_observation_only_no_common_correctness
#print axioms occupancy_style_observer_fracture

end INSACERMO.TemporalValidityV1
