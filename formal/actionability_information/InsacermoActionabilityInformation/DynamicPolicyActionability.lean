import InsacermoActionabilityInformation.HypergraphActionability

namespace InsacermoActionabilityInformation

/-- A finite-horizon dynamic controller can be compiled to an ordinary
capability object once the contract assigns each initial world / policy pair
an acceptability proposition.  The internal rollout semantics remain external
to the actionability kernel. -/
structure FiniteHorizonPolicyContract (S Policy : Type*) where
  GoodPolicy : S → Policy → Prop

/-- Dynamic-policy actionability is exactly the frozen `SafeRep` semantics with
whole policies/plans playing the role of capabilities. -/
def PolicySafeRep {S Policy Y : Type*}
    (K : FiniteHorizonPolicyContract S Policy)
    (B : Set S) (C : Set Policy) (h : S → Y) : Prop :=
  SafeRep K.GoodPolicy B C h

/-- Enlarging the set of executable policies cannot destroy a representation
that was already dynamically actionable. -/
theorem policySafeRep_capability_mono
    {S Policy Y : Type*}
    {K : FiniteHorizonPolicyContract S Policy}
    {B : Set S} {C C' : Set Policy} {h : S → Y}
    (hsafe : PolicySafeRep K B C h)
    (hcap : C ⊆ C') :
    PolicySafeRep K B C' h := by
  exact safeRep_capability_mono hsafe hcap

/-- Refining information cannot destroy dynamic-policy actionability under a
fixed policy contract and capability set. -/
theorem policySafeRep_information_mono
    {S Policy YFine YCoarse : Type*}
    {K : FiniteHorizonPolicyContract S Policy}
    {B : Set S} {C : Set Policy}
    {fine : S → YFine} {coarse : S → YCoarse}
    (hsafe : PolicySafeRep K B C coarse)
    (href : Refines fine coarse) :
    PolicySafeRep K B C fine := by
  exact safeRep_information_mono hsafe href

/-- Product-order monotonicity survives when capabilities are whole policies. -/
theorem policySafeRep_bimonotone
    {S Policy YFine YCoarse : Type*}
    {K : FiniteHorizonPolicyContract S Policy}
    {B : Set S} {C C' : Set Policy}
    {fine : S → YFine} {coarse : S → YCoarse}
    (hsafe : PolicySafeRep K B C coarse)
    (href : Refines fine coarse)
    (hcap : C ⊆ C') :
    PolicySafeRep K B C' fine := by
  exact safeRep_of_refines_of_capabilitySubset hsafe href hcap

/-- Finite hypergraph characterization survives verbatim for compiled dynamic
policies.  No claim is made here that arbitrary POMDP/history-dependent models
support a lossless compilation to `GoodPolicy`; this theorem states the exact
boundary once such a contract is available. -/
theorem policySafeRep_iff_hypergraphSafe
    {S Policy Y : Type*} [Fintype S] [DecidableEq S]
    {K : FiniteHorizonPolicyContract S Policy}
    {B : Set S} {C : Set Policy} {h : S → Y} :
    PolicySafeRep K B C h ↔ HypergraphSafe K.GoodPolicy B C h := by
  exact safeRep_iff_hypergraphSafe

/-- Likewise, dynamic-policy unsafety has a minimal finite common-policy
obstruction on finite world spaces. -/
theorem policySafeRep_iff_no_minimal_fiber_obstruction
    {S Policy Y : Type*} [Fintype S] [DecidableEq S]
    {K : FiniteHorizonPolicyContract S Policy}
    {B : Set S} {C : Set Policy} {h : S → Y} :
    PolicySafeRep K B C h ↔
      ¬ FiberContainsMinimalObstruction K.GoodPolicy B C h := by
  exact safeRep_iff_no_minimal_fiber_obstruction

end InsacermoActionabilityInformation
