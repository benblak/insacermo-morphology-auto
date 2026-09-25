import InsacermoActionabilityInformation.EventualObstructionRank
import Mathlib

namespace InsacermoActionabilityInformation

namespace StructuralAuditKernel

open FutureRobustness


/-!
## Generic finite feasibility families

ContractComplex is intentionally downward closed. Some physical feasibility
models need not be. The certificate-router logic itself does not need downward
closure: it only needs a predicate on finite bundles plus a bounded-bad-witness
property.
-/

/-- An arbitrary feasibility predicate on finite bundles. No monotonicity or
downward-closure assumption is imposed. -/
abbrev FeasibilityFamily (Q : Type*) [DecidableEq Q] :=
  Finset Q → Prop

/-- Inclusion-minimal failure for an arbitrary feasibility family. -/
def MinimalFailure
    {Q : Type*} [DecidableEq Q]
    (P : FeasibilityFamily Q) (F : Finset Q) : Prop :=
  ¬ P F ∧ ∀ G : Finset Q, G ⊂ F → P G

/-- Generic bounded-witness certificate, requiring no downward closure:
every failed finite bundle contains a failed sub-bundle of size at most r. -/
def FamilyBadWitnessAtMost
    {Q : Type*} [DecidableEq Q]
    (P : FeasibilityFamily Q) (r : ℕ) : Prop :=
  ∀ F : Finset Q, ¬ P F →
    ∃ G : Finset Q, G ⊆ F ∧ G.card ≤ r ∧ ¬ P G

/-- Generic certificate-router theorem. Downward closure is not needed:
bounded failed sub-witnesses alone bound every inclusion-minimal failure. -/
theorem minimalFailure_card_le_of_boundedWitness
    {Q : Type*} [DecidableEq Q]
    {P : FeasibilityFamily Q}
    {r : ℕ}
    (hcert : FamilyBadWitnessAtMost P r)
    {F : Finset Q}
    (hmin : MinimalFailure P F) :
    F.card ≤ r := by
  by_contra hnot
  have hgt : r < F.card := Nat.lt_of_not_ge hnot
  rcases hcert F hmin.1 with ⟨G, hGF, hGcard, hGbad⟩
  have hproper : G ⊂ F := by
    constructor
    · exact hGF
    · intro hFG
      have hcardFG : F.card ≤ G.card := Finset.card_le_card hFG
      omega
  exact hGbad (hmin.2 G hproper)

/-- Generic stopping theorem. If every failure contains a failed witness of
size at most r, then checking every bundle through size r is complete even for
a non-hereditary feasibility family. -/
theorem familyAudit_complete_of_boundedWitness
    {Q : Type*} [DecidableEq Q]
    {P : FeasibilityFamily Q}
    {r : ℕ}
    (hcert : FamilyBadWitnessAtMost P r)
    (hsmall : ∀ G : Finset Q, G.card ≤ r → P G) :
    ∀ F : Finset Q, P F := by
  intro F
  by_contra hF
  rcases hcert F hF with ⟨G, _hGF, hGcard, hGbad⟩
  exact hGbad (hsmall G hGcard)


/-- General bounded-witness structural certificate.

Every infeasible finite contract contains an infeasible sub-contract whose
cardinality is at most r.  Each system class may discharge this hypothesis with
its own structural certificate (SCC/comparability, resource capacity, cuts,
duality, Hall-type witnesses, etc.). -/
def BadWitnessAtMost
    {Q : Type*} [DecidableEq Q]
    (K : ContractComplex Q) (r : ℕ) : Prop :=
  ∀ F : Finset Q, ¬ K.feasible F →
    ∃ G : Finset Q, G ⊆ F ∧ G.card ≤ r ∧ ¬ K.feasible G


/-- Every downward-closed ContractComplex induces the generic family
certificate with exactly the same radius. -/
theorem familyBadWitnessAtMost_of_contractComplex
    {Q : Type*} [DecidableEq Q]
    {K : ContractComplex Q} {r : ℕ}
    (hcert : BadWitnessAtMost K r) :
    FamilyBadWitnessAtMost K.feasible r := by
  exact hcert

/-- Certificate-router theorem: if every failure contains a bad witness of
cardinality at most r, then every minimal obstruction has cardinality at most r. -/
theorem minimalNonface_card_le_of_boundedWitness
    {Q : Type*} [DecidableEq Q]
    {K : ContractComplex Q}
    {r : ℕ}
    (hcert : BadWitnessAtMost K r)
    {F : Finset Q}
    (hmin : MinimalNonface K F) :
    F.card ≤ r := by
  by_contra hnot
  have hgt : r < F.card := Nat.lt_of_not_ge hnot
  rcases hcert F hmin.1 with ⟨G, hGF, hGcard, hGbad⟩
  have hproper : G ⊂ F := by
    constructor
    · exact hGF
    · intro hFG
      have hcardFG : F.card ≤ G.card := Finset.card_le_card hFG
      omega
  exact hGbad (hmin.2 G hproper)

/-- Operational stopping theorem.  Under a bounded-witness certificate of
radius r, auditing every bundle of cardinality at most r is complete: if all
such bundles are feasible, then every finite bundle is feasible. -/
theorem audit_complete_of_boundedWitness
    {Q : Type*} [DecidableEq Q]
    {K : ContractComplex Q}
    {r : ℕ}
    (hcert : BadWitnessAtMost K r)
    (hsmall : ∀ G : Finset Q, G.card ≤ r → K.feasible G) :
    ∀ F : Finset Q, K.feasible F := by
  intro F
  by_contra hF
  rcases hcert F hF with ⟨G, _hGF, hGcard, hGbad⟩
  exact hGbad (hsmall G hGcard)

/-- Structural certificate saying that every infeasible finite contract contains
an infeasible sub-contract of cardinality at most two.  In graph instances with
state-valued goals at unbounded horizon, the SCC condensation theorem is meant
to discharge exactly this hypothesis. -/
def BadWitnessAtMostTwo
    {Q : Type*} [DecidableEq Q]
    (K : ContractComplex Q) : Prop :=
  BadWitnessAtMost K 2

/-- If every failure has a singleton-or-pair witness, then no minimal
obstruction can have cardinality larger than two. -/
theorem minimalNonface_card_le_two
    {Q : Type*} [DecidableEq Q]
    {K : ContractComplex Q}
    (hcert : BadWitnessAtMostTwo K)
    {F : Finset Q}
    (hmin : MinimalNonface K F) :
    F.card ≤ 2 := by
  exact minimalNonface_card_le_of_boundedWitness hcert hmin

/-- Arithmetic core of the finite-horizon audit-rank certificate.
If every proper (m-1)-goal witness needs at least d + (m-2)δ resource,
and such a witness fits under H, then m is bounded accordingly.

The graph-theoretic layer only has to prove the premise
d + (m-2)δ ≤ H. -/
theorem finiteHorizon_card_bound
    {m d δ H : ℕ}
    (hm : 2 ≤ m)
    (hδ : 0 < δ)
    (hbudget : d + (m - 2) * δ ≤ H) :
    m ≤ 2 + (H - d) / δ := by
  have hdH : d ≤ H := by omega
  have hmul : (m - 2) * δ ≤ H - d := by omega
  have hdiv : m - 2 ≤ (H - d) / δ := by
    exact (Nat.le_div_iff_mul_le hδ).2 hmul
  omega

/-- Abstract directional-completion bound.
If one proper sub-contract G can be completed to F with extra resource at most R,
then the boundary delay of F over the worst proper sub-contract is at most R. -/
theorem directionalCompletionDebtBound
    {Dfull DproperMax DG R : ℕ}
    (hGle : DG ≤ DproperMax)
    (hcomplete : Dfull ≤ DG + R) :
    Dfull - DproperMax ≤ R := by
  omega

/-- Deadline form of the same certificate: if all proper sub-contracts are
resolved by H and F can be completed from one of them using at most R extra
resource, then F resolves by H+R. -/
theorem hiddenDeadlineCompletionBound
    {Dfull DG H R : ℕ}
    (hGdeadline : DG ≤ H)
    (hcomplete : Dfull ≤ DG + R) :
    Dfull ≤ H + R := by
  omega

/-- Consequently any finite hidden delay beyond deadline H is at most R. -/
theorem hiddenDeadlineDebt_le
    {Dfull H R : ℕ}
    (hbad : H < Dfull)
    (hresolved : Dfull ≤ H + R) :
    Dfull - H ≤ R := by
  omega


/-- Arithmetic core of a resource-capacity audit certificate.

Suppose a minimal lost bundle has cardinality m ≥ 1. If every proper
(m-1)-goal subbundle consumes at least δ units per goal of the same limiting
resource and still fits inside post-transformation capacity C, then

  m ≤ 1 + C / δ.

The domain-specific Petri/stoichiometric layer must discharge the premise
`(m - 1) * δ ≤ C`. -/
theorem resourceCapacity_card_bound
    {m C δ : ℕ}
    (hm : 1 ≤ m)
    (hδ : 0 < δ)
    (hproper : (m - 1) * δ ≤ C) :
    m ≤ 1 + C / δ := by
  have hdiv : m - 1 ≤ C / δ := by
    exact (Nat.le_div_iff_mul_le hδ).2 hproper
  omega

/-- Unit-demand specialization of `resourceCapacity_card_bound`.
If every proper subbundle of an m-goal minimal resource obstruction fits in
capacity C and every goal needs one unit of the limiting resource, then
m ≤ C + 1. -/
theorem unitResource_card_bound
    {m C : ℕ}
    (hm : 1 ≤ m)
    (hproper : m - 1 ≤ C) :
    m ≤ C + 1 := by
  omega

/-- Exact unit-resource minimal-obstruction law.

If the full unit-demand bundle of size m exceeds capacity C, while every
(m-1)-goal proper subbundle fits, then the obstruction size is exactly C+1.
This explains saturation in clean shared-resource witnesses. -/
theorem unitResource_minimalObstruction_exact
    {m C : ℕ}
    (hfull : C < m)
    (hproper : m - 1 ≤ C) :
    m = C + 1 := by
  omega

/-- Weighted arithmetic window for a minimal shared-resource obstruction.
If total demand is above capacity C, and removing the lightest required goal
(weight wmin) makes the bundle fit, then total demand lies in the narrow window
C < total ≤ C + wmin. -/
theorem weightedResource_minimalObstruction_window
    {total C wmin : ℕ}
    (hfull : C < total)
    (hwmin : wmin ≤ total)
    (hproper : total - wmin ≤ C) :
    C < total ∧ total ≤ C + wmin := by
  constructor
  · exact hfull
  · omega

/-- Arithmetic core for an additive dual/cut certificate.

A domain-specific dual certificate can often be oriented as a nonnegative
"burden" per goal against a total certificate capacity C.  If every goal in a
minimal obstruction contributes at least delta > 0 and every (m-1)-goal proper
subbundle remains below C, then the same cardinality bound as for a physical
resource follows.  The theorem is intentionally domain-agnostic: cuts,
Farkas rays, Hall deficits, and other additive certificates may discharge the
premise. -/
theorem additiveCertificate_card_bound
    {m C delta : ℕ}
    (hm : 1 ≤ m)
    (hdelta : 0 < delta)
    (hproper : (m - 1) * delta ≤ C) :
    m ≤ 1 + C / delta := by
  exact resourceCapacity_card_bound hm hdelta hproper

/-- Exact unit-burden form for an additive certificate. -/
theorem unitAdditiveCertificate_exact
    {m C : ℕ}
    (hfull : C < m)
    (hproper : m - 1 ≤ C) :
    m = C + 1 := by
  exact unitResource_minimalObstruction_exact hfull hproper

end StructuralAuditKernel

end InsacermoActionabilityInformation
