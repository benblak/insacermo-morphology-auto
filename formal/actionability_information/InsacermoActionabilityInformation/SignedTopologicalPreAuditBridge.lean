import InsacermoActionabilityInformation.CertificatePreAuditDepth
import InsacermoActionabilityInformation.SignedTopologicalMinimal

namespace InsacermoActionabilityInformation

open SimpleGraph

namespace SignedTopologicalPreAuditBridge

open SignedGraph

variable {V : Type*} (SG : SignedGraph V)

/-- For signed-XOR contracts, the structural pre-audit invariant is the
unbalanced girth: the least length of an unbalanced cycle.  It is computed
from graph structure/certificates, not by enumerating selected edge bundles. -/
noncomputable def topologicalPreAuditDepth
    (hC : ∃ n, SG.HasUnbalancedCycleAtMost n) : ℕ :=
  SG.unbalancedGirth hC

/-- Exact bridge: signed topological pre-audit depth is not merely an upper
bound.  It is exactly the actual least UNSAT subcontract cardinality.

This is the graph/topology instantiation of the INSACERMO certificate
pre-audit pattern. -/
theorem actualTopologicalDepth_eq_preAuditDepth
    (hU : ∃ n, SG.HasUnsatSubcontractAtMost n) :
    SG.topologicalDepth hU =
      SG.topologicalPreAuditDepth
        ((SG.exists_hasUnsatSubcontractAtMost_iff_exists_hasUnbalancedCycleAtMost).mp hU) := by
  exact SG.topologicalDepth_eq_unbalancedGirth hU

/-- Conversely, the pre-audit invariant can be read directly as the actual
topological depth. -/
theorem preAuditDepth_eq_actualTopologicalDepth
    (hU : ∃ n, SG.HasUnsatSubcontractAtMost n) :
    SG.topologicalPreAuditDepth
        ((SG.exists_hasUnsatSubcontractAtMost_iff_exists_hasUnbalancedCycleAtMost).mp hU) =
      SG.topologicalDepth hU := by
  symm
  exact SG.actualTopologicalDepth_eq_preAuditDepth hU

/-- Atomic certificate classification: every inclusion-minimal finite UNSAT
signed subcontract is exactly the edge set of an unbalanced simple cycle.

Thus, in this domain, the cross-certified witnesses required by the generic
certificate-pre-audit theory are intrinsic graph objects rather than objects
found by bundle enumeration. -/
theorem minimalUnsat_is_topologicalCertificate
    {F : Finset (Sym2 V)}
    (hmin : SG.IsMinimalUnsat F) :
    ∃ u : V, ∃ p : SG.graph.Walk u u,
      SG.IsUnbalancedCycle p ∧ SG.cycleEdgeFinset p = F := by
  exact SG.minimalUnsat_eq_unbalancedCycleEdges hmin

/-- Every unbalanced simple cycle is already a genuine inclusion-minimal UNSAT
subcontract, so a shortest unbalanced cycle supplies an exact obstruction
witness directly from topology. -/
theorem topologicalCertificate_is_minimalUnsat
    {u : V} {p : SG.graph.Walk u u}
    (hp : SG.IsUnbalancedCycle p) :
    SG.IsMinimalUnsat (SG.cycleEdgeFinset p) := by
  exact SG.unbalancedCycleEdges_isMinimalUnsat hp

/-- Compact two-way classification used by the INSACERMO pre-audit layer. -/
theorem minimalUnsat_iff_topologicalCertificate
    {F : Finset (Sym2 V)} :
    SG.IsMinimalUnsat F ↔
      ∃ u : V, ∃ p : SG.graph.Walk u u,
        SG.IsUnbalancedCycle p ∧ SG.cycleEdgeFinset p = F := by
  exact SG.minimalUnsat_iff_exists_unbalancedCycleEdges

end SignedTopologicalPreAuditBridge

end InsacermoActionabilityInformation
