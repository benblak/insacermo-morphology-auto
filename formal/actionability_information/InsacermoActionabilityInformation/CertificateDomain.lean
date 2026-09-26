import InsacermoActionabilityInformation.CertificatePreAuditDepth

namespace InsacermoActionabilityInformation

namespace CertificateDomain

open StructuralAuditKernel
open CertificatePreAudit

universe u

/-- A certificate domain is the abstract plug-in interface for INSACERMO
pre-audit.

The domain supplies:
* a feasibility predicate on finite future-goal bundles;
* a type of structural certificates;
* a certificate family;
* a proof that feasibility is characterized exactly by absence of certificates.

No assumption is made about the internal mathematics of the certificates:
they may be Farkas rays, resource-capacity witnesses, unbalanced cycles, cuts,
Hall obstructions, SAT cores, etc. -/
structure Domain (Q : Type u) [DecidableEq Q] where
  R : Type u
  feasible : FeasibilityFamily Q
  cert : CertificateFamily Q R
  characterizes : Characterizes feasible cert

variable {Q : Type u} [DecidableEq Q]

/-- A certified pre-audit result exported by one domain-specific engine.

The engine may compute its depth in any way it wants. INSACERMO only requires
the proof that every certificate-local deletion-minimal obstruction has
cardinality at most that depth. -/
structure PreAuditResult (D : Domain Q) where
  depth : ℕ
  sound : PreAuditDepthAtMost D.cert depth

/-- A pre-audit result immediately gives an actual obstruction-depth upper
bound, independently of the domain-specific certificate mathematics. -/
theorem PreAuditResult.actualDepthAtMost
    {D : Domain Q} (A : PreAuditResult D) :
    ActualDepthAtMost D.feasible A.depth := by
  exact preAuditDepthAtMost_implies_actualDepthAtMost
    D.characterizes A.sound

/-- A closed pre-audit result additionally carries one cross-certified witness
attaining the pre-audit bound.

This is the generic exact-depth output object of the INSACERMO certificate
layer. -/
structure ClosedPreAuditResult (D : Domain Q) extends PreAuditResult D where
  rho : D.R
  witness : Finset Q
  crossCertified : CrossCertifiedMinimal D.cert rho witness
  witness_card : witness.card = depth

/-- Any closed pre-audit result certifies the exact actual obstruction depth. -/
theorem ClosedPreAuditResult.actualDepthExact
    {D : Domain Q} (A : ClosedPreAuditResult D) :
    ActualDepthExact D.feasible A.depth := by
  exact exactDepth_of_preAudit_and_crossWitness
    D.characterizes A.sound A.crossCertified A.witness_card

/-- The exact-depth conclusion split into the two operational facts most useful
to downstream planners: no minimal obstruction is deeper than the certified
depth, and at least one genuine minimal obstruction attains it. -/
theorem ClosedPreAuditResult.upper_and_attained
    {D : Domain Q} (A : ClosedPreAuditResult D) :
    ActualDepthAtMost D.feasible A.depth ∧
      ∃ F : Finset Q, MinimalFailure D.feasible F ∧ F.card = A.depth := by
  exact A.actualDepthExact

/-- A closed result is automatically a sound pre-audit result. -/
def ClosedPreAuditResult.toPreAudit
    {D : Domain Q} (A : ClosedPreAuditResult D) : PreAuditResult D where
  depth := A.depth
  sound := A.sound

/-- Certificate domains compose at the theorem interface: once a domain-specific
engine exports only a PreAuditResult, all downstream code can forget how its
certificates were produced and use the same generic upper-bound theorem. -/
theorem domain_independent_upper_bound
    {D : Domain Q} {r : ℕ}
    (hpre : PreAuditDepthAtMost D.cert r) :
    ActualDepthAtMost D.feasible r := by
  exact preAuditDepthAtMost_implies_actualDepthAtMost
    D.characterizes hpre

/-- Likewise, exact closure is domain-independent once the plug-in supplies a
cross-certified witness attaining the bound. -/
theorem domain_independent_exact_closure
    {D : Domain Q} {r : ℕ} {rho : D.R} {F : Finset Q}
    (hpre : PreAuditDepthAtMost D.cert r)
    (hw : CrossCertifiedMinimal D.cert rho F)
    (hcard : F.card = r) :
    ActualDepthExact D.feasible r := by
  exact exactDepth_of_preAudit_and_crossWitness
    D.characterizes hpre hw hcard

end CertificateDomain

end InsacermoActionabilityInformation
