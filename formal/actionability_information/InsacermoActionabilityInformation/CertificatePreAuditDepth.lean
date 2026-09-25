import InsacermoActionabilityInformation.StructuralAuditKernel
import Mathlib

namespace InsacermoActionabilityInformation

namespace CertificatePreAudit

open StructuralAuditKernel

variable {Q R : Type*} [DecidableEq Q]

/-- A family of structural infeasibility certificates indexed by R. -/
abbrev CertificateFamily (Q R : Type*) [DecidableEq Q] :=
  R → Finset Q → Prop

/-- Exact certificate characterization of feasibility:
a bundle is feasible iff no certificate rejects it. -/
def Characterizes
    (P : FeasibilityFamily Q)
    (Cert : CertificateFamily Q R) : Prop :=
  ∀ F : Finset Q, P F ↔ ∀ ρ : R, ¬ Cert ρ F

/-- A bundle is deletion-minimal for one certificate when that certificate
rejects the full bundle but no one-goal deletion.  This is the abstract form
of the one-deletion Farkas-ray criterion used by the DC pre-audit. -/
def RayDeletionMinimal
    (Cert : CertificateFamily Q R) (ρ : R) (F : Finset Q) : Prop :=
  Cert ρ F ∧ ∀ q, q ∈ F → ¬ Cert ρ (F.erase q)

/-- Structural pre-audit depth at most r: every bundle that is deletion-minimal
for any single certificate has cardinality at most r. -/
def PreAuditDepthAtMost
    (Cert : CertificateFamily Q R) (r : ℕ) : Prop :=
  ∀ ρ : R, ∀ F : Finset Q, RayDeletionMinimal Cert ρ F → F.card ≤ r

/-- Actual minimal-obstruction depth at most r. -/
def ActualDepthAtMost
    (P : FeasibilityFamily Q) (r : ℕ) : Prop :=
  ∀ F : Finset Q, MinimalFailure P F → F.card ≤ r

/-- Exact actual obstruction depth r: r is an upper bound and is attained by
at least one genuine minimal failure. -/
def ActualDepthExact
    (P : FeasibilityFamily Q) (r : ℕ) : Prop :=
  ActualDepthAtMost P r ∧
    ∃ F : Finset Q, MinimalFailure P F ∧ F.card = r

/-- A cross-certified minimal obstruction is rejected by one certificate while
every proper subbundle is accepted by every certificate.  Unlike
RayDeletionMinimal, this condition already controls interference from all other
certificates and is therefore sufficient for genuine primal minimality. -/
def CrossCertifiedMinimal
    (Cert : CertificateFamily Q R) (ρ : R) (F : Finset Q) : Prop :=
  Cert ρ F ∧
    ∀ G : Finset Q, G ⊂ F → ∀ σ : R, ¬ Cert σ G

/-- Every genuine minimal failure has a certificate that is deletion-minimal
on that same bundle.  This is the key bridge from primal minimality to
certificate pre-audit depth. -/
theorem minimalFailure_has_rayDeletionMinimal
    {P : FeasibilityFamily Q}
    {Cert : CertificateFamily Q R}
    (hchar : Characterizes P Cert)
    {F : Finset Q}
    (hmin : MinimalFailure P F) :
    ∃ ρ : R, RayDeletionMinimal Cert ρ F := by
  classical
  have hneg : ¬ (∀ ρ : R, ¬ Cert ρ F) := by
    intro hall
    exact hmin.1 ((hchar F).2 hall)
  push_neg at hneg
  rcases hneg with ⟨ρ, hcert⟩
  refine ⟨ρ, hcert, ?_⟩
  intro q hq hdelcert
  have hproper : F.erase q ⊂ F := by
    exact Finset.erase_ssubset hq
  have hdelFeasible : P (F.erase q) := hmin.2 (F.erase q) hproper
  have hnoCert := (hchar (F.erase q)).1 hdelFeasible
  exact (hnoCert ρ) hdelcert

/-- Generic pre-audit upper-bound theorem.

If certificates characterize feasibility exactly and every certificate-local
deletion-minimal bundle has size at most r, then every genuine minimal failure
has size at most r.

This is the abstract theorem behind the inequality kappa <= r_pre. -/
theorem preAuditDepthAtMost_implies_actualDepthAtMost
    {P : FeasibilityFamily Q}
    {Cert : CertificateFamily Q R}
    {r : ℕ}
    (hchar : Characterizes P Cert)
    (hpre : PreAuditDepthAtMost Cert r) :
    ActualDepthAtMost P r := by
  intro F hmin
  rcases minimalFailure_has_rayDeletionMinimal hchar hmin with ⟨ρ, hray⟩
  exact hpre ρ F hray

/-- Cross-certificate closure turns a dual witness into a genuine minimal
failure.  This identifies exactly what the single-ray criterion alone lacks:
all proper subbundles must survive every other certificate too. -/
theorem crossCertifiedMinimal_implies_minimalFailure
    {P : FeasibilityFamily Q}
    {Cert : CertificateFamily Q R}
    (hchar : Characterizes P Cert)
    {ρ : R} {F : Finset Q}
    (hw : CrossCertifiedMinimal Cert ρ F) :
    MinimalFailure P F := by
  constructor
  · intro hPF
    have hnone := (hchar F).1 hPF
    exact (hnone ρ) hw.1
  · intro G hGF
    exact (hchar G).2 (hw.2 G hGF)

/-- Exact-depth closure theorem.

A certificate-derived upper bound r becomes the exact obstruction depth as soon
as one cross-certified minimal witness of cardinality r is found.  No primal
feasibility oracle is logically required once Characterizes is available. -/
theorem exactDepth_of_preAudit_and_crossWitness
    {P : FeasibilityFamily Q}
    {Cert : CertificateFamily Q R}
    {r : ℕ} {ρ : R} {F : Finset Q}
    (hchar : Characterizes P Cert)
    (hpre : PreAuditDepthAtMost Cert r)
    (hw : CrossCertifiedMinimal Cert ρ F)
    (hcard : F.card = r) :
    ActualDepthExact P r := by
  constructor
  · exact preAuditDepthAtMost_implies_actualDepthAtMost hchar hpre
  · exact ⟨F, crossCertifiedMinimal_implies_minimalFailure hchar hw, hcard⟩

/-- The conceptual split made explicit:
single-certificate deletion minimality suffices for an upper bound, whereas an
attained exact depth requires cross-certificate closure of the proper
subbundles. -/
theorem preAudit_upper_and_crossWitness_exact
    {P : FeasibilityFamily Q}
    {Cert : CertificateFamily Q R}
    {r : ℕ}
    (hchar : Characterizes P Cert)
    (hpre : PreAuditDepthAtMost Cert r)
    (hwit : ∃ ρ : R, ∃ F : Finset Q,
      CrossCertifiedMinimal Cert ρ F ∧ F.card = r) :
    ActualDepthExact P r := by
  rcases hwit with ⟨ρ, F, hw, hcard⟩
  exact exactDepth_of_preAudit_and_crossWitness hchar hpre hw hcard

end CertificatePreAudit

end InsacermoActionabilityInformation
