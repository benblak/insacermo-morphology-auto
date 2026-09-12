import InsacermoActionabilityInformation.DynamicPolicyActionability

namespace InsacermoActionabilityInformation

/-- A deterministic finite-horizon adaptive policy maps the accumulated
observation history to the next control. -/
abbrev AdaptivePolicy (O U : Type*) := List O → U

/-- Lift a policy written for a coarse observation alphabet to a finer one
using a decoder from fine observations to coarse observations. -/
def liftAdaptivePolicy {OFine OCoarse U : Type*}
    (decode : OFine → OCoarse)
    (pi : AdaptivePolicy OCoarse U) : AdaptivePolicy OFine U :=
  fun hist => pi (hist.map decode)

/-- One closed-loop rollout step with accumulated observation history. -/
def adaptiveStep {S O U : Type*}
    (step : S → U → S)
    (observe : S → O)
    (pi : AdaptivePolicy O U)
    (x : S × List O) : S × List O :=
  let s := x.1
  let hist := x.2
  let o := observe s
  let hist' := hist ++ [o]
  let u := pi hist'
  (step s u, hist')

/-- Closed-loop adaptive state after `n` control updates, starting with an
empty observation history. -/
def adaptiveRun {S O U : Type*}
    (step : S → U → S)
    (observe : S → O)
    (pi : AdaptivePolicy O U)
    (n : Nat) (s0 : S) : S × List O :=
  Nat.iterate (adaptiveStep step observe pi) n (s0, [])

/-- A fine internal sensor refines a coarse internal sensor when the coarse
observation is a deterministic decoding of the fine observation. -/
def SensorRefines {S OFine OCoarse : Type*}
    (fineObs : S → OFine) (coarseObs : S → OCoarse) : Prop :=
  ∃ decode : OFine → OCoarse, ∀ s, coarseObs s = decode (fineObs s)

/-- Contract compiled from an adaptive closed-loop policy.  `GoodFinal` can
encode any fixed finite-horizon safety/goal property that depends on the
initial and final closed-loop state. -/
def adaptiveGood {S O U : Type*}
    (step : S → U → S)
    (observe : S → O)
    (horizon : Nat)
    (GoodFinal : S → S → Prop)
    (s0 : S) (pi : AdaptivePolicy O U) : Prop :=
  GoodFinal s0 (adaptiveRun step observe pi horizon s0).1

/-- Adaptive actionability is the frozen `SafeRep` kernel instantiated with a
closed-loop adaptive-policy contract. -/
def AdaptiveSafeRep {S O U Y : Type*}
    (step : S → U → S)
    (observe : S → O)
    (horizon : Nat)
    (GoodFinal : S → S → Prop)
    (B : Set S) (C : Set (AdaptivePolicy O U)) (h : S → Y) : Prop :=
  SafeRep (adaptiveGood step observe horizon GoodFinal) B C h

/-- The adaptive contract remains within the finite hypergraph theorem once
compiled to a fixed initial-world/policy predicate. -/
theorem adaptiveSafeRep_iff_hypergraphSafe
    {S O U Y : Type*} [Fintype S] [DecidableEq S]
    {step : S → U → S} {observe : S → O} {horizon : Nat}
    {GoodFinal : S → S → Prop}
    {B : Set S} {C : Set (AdaptivePolicy O U)} {h : S → Y} :
    AdaptiveSafeRep step observe horizon GoodFinal B C h ↔
      HypergraphSafe (adaptiveGood step observe horizon GoodFinal) B C h := by
  exact safeRep_iff_hypergraphSafe

/-- Likewise, adaptive unsafety has a minimal finite common-policy obstruction
on finite world spaces. -/
theorem adaptiveSafeRep_iff_no_minimal_fiber_obstruction
    {S O U Y : Type*} [Fintype S] [DecidableEq S]
    {step : S → U → S} {observe : S → O} {horizon : Nat}
    {GoodFinal : S → S → Prop}
    {B : Set S} {C : Set (AdaptivePolicy O U)} {h : S → Y} :
    AdaptiveSafeRep step observe horizon GoodFinal B C h ↔
      ¬ FiberContainsMinimalObstruction
        (adaptiveGood step observe horizon GoodFinal) B C h := by
  exact safeRep_iff_no_minimal_fiber_obstruction

/-- External representation refinement remains monotone even when the
capabilities are adaptive observation-history policies. -/
theorem adaptiveSafeRep_information_mono
    {S O U YFine YCoarse : Type*}
    {step : S → U → S} {observe : S → O} {horizon : Nat}
    {GoodFinal : S → S → Prop} {B : Set S}
    {C : Set (AdaptivePolicy O U)}
    {fine : S → YFine} {coarse : S → YCoarse}
    (hsafe : AdaptiveSafeRep step observe horizon GoodFinal B C coarse)
    (href : Refines fine coarse) :
    AdaptiveSafeRep step observe horizon GoodFinal B C fine := by
  exact safeRep_information_mono hsafe href

/-- Expanding the executable adaptive-policy set cannot destroy actionability
under a fixed sensor and contract. -/
theorem adaptiveSafeRep_capability_mono
    {S O U Y : Type*}
    {step : S → U → S} {observe : S → O} {horizon : Nat}
    {GoodFinal : S → S → Prop} {B : Set S}
    {C C' : Set (AdaptivePolicy O U)} {h : S → Y}
    (hsafe : AdaptiveSafeRep step observe horizon GoodFinal B C h)
    (hcap : C ⊆ C') :
    AdaptiveSafeRep step observe horizon GoodFinal B C' h := by
  exact safeRep_capability_mono hsafe hcap

end InsacermoActionabilityInformation
