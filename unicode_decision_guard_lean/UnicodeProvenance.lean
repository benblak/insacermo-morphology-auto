/-
INSACERMO Unicode Provenance -- Lean 4.20 laboratory proof.
No modifications to frozen MAX TOTAL or C3.
HMAC-SHA256, Python, JSON, SQLite and Unicode implementation correctness
are not formalized: authenticated is an explicit external hypothesis.
-/
import UnicodeDecisionGuard

namespace InsacermoUnicodeProvenance
open InsacermoUnicodeDecisionGuard

structure Packet where
  expr : Expression
  token : Nat
  audience : Nat
  pipeline : Nat
  nonce : Nat

def authorizedDecision (p : Packet) (authenticated : Bool)
    (targetAudience targetPipeline : Nat) (consumed : List Nat) : Option Bool :=
  if authenticated then
    if p.audience = targetAudience then
      if p.pipeline = targetPipeline then
        if p.nonce ∈ consumed then none
        else if decodeOp p.token = some (p.expr.family, p.expr.negated) then
          some (truth p.expr)
        else none
      else none
    else none
  else none

theorem unauthenticated_refuses (p : Packet) (a t : Nat)
    (consumed : List Nat) :
    authorizedDecision p false a t consumed = none := by
  rfl

theorem replay_refuses (p : Packet) (trusted : Bool) (a t : Nat)
    (consumed : List Nat) (hSeen : p.nonce ∈ consumed) :
    authorizedDecision p trusted a t consumed = none := by
  simp [authorizedDecision, hSeen]

theorem wrong_audience_refuses (p : Packet) (trusted : Bool) (a t : Nat)
    (consumed : List Nat) (hOther : p.audience ≠ a) :
    authorizedDecision p trusted a t consumed = none := by
  simp [authorizedDecision, hOther]

theorem wrong_pipeline_refuses (p : Packet) (trusted : Bool) (a t : Nat)
    (consumed : List Nat) (hOther : p.pipeline ≠ t) :
    authorizedDecision p trusted a t consumed = none := by
  simp [authorizedDecision, hOther]

theorem authorized_roundtrip (p : Packet) (a t : Nat)
    (consumed : List Nat)
    (ha : p.audience = a) (ht : p.pipeline = t)
    (hFresh : p.nonce ∉ consumed)
    (hToken : decodeOp p.token = some (p.expr.family, p.expr.negated)) :
    authorizedDecision p true a t consumed = some (truth p.expr) := by
  simp [authorizedDecision, ha, ht, hFresh, hToken]

theorem authorized_decision_sound (p : Packet) (trusted : Bool) (a t : Nat)
    (consumed : List Nat) (v : Bool)
    (h : authorizedDecision p trusted a t consumed = some v) :
    v = truth p.expr := by
  unfold authorizedDecision at h
  split at h <;> try simp_all
  split at h <;> try simp_all
  split at h <;> try simp_all
  split at h <;> try simp_all
  split at h <;> try simp_all
  simp_all

theorem lossy_view_forces_refusal
    {W O : Type} (observe : W → O) (actual : W → Bool)
    (act : O → Option Bool)
    (safe : AlwaysSafe observe actual act)
    (x y : W) (same : observe x = observe y)
    (different : actual x ≠ actual y) :
    act (observe x) = none :=
  collision_forces_refusal observe actual act safe x y same different

#print axioms unauthenticated_refuses
#print axioms replay_refuses
#print axioms wrong_audience_refuses
#print axioms wrong_pipeline_refuses
#print axioms authorized_roundtrip
#print axioms authorized_decision_sound
#print axioms lossy_view_forces_refusal

end InsacermoUnicodeProvenance
