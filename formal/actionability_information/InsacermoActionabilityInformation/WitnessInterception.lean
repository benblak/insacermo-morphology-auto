import Mathlib

namespace InsacermoActionabilityInformation
namespace WitnessInterception

/-- A finite path witness in a directed transition system. -/
def IsPath {X : Type*} (Step : X → X → Prop) : List X → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => Step x y ∧ IsPath Step (y :: xs)

/-- A path avoids the support modified by a transformation when every
adjacent edge lies outside the support. -/
def AvoidsSupport {X : Type*}
    (support : X → X → Prop) : List X → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => ¬ support x y ∧ AvoidsSupport support (y :: xs)

/-- Every before-edge outside the modified support survives after the decision. -/
def EdgeLocalTransformation {X : Type*}
    (StepBefore StepAfter support : X → X → Prop) : Prop :=
  ∀ x y, StepBefore x y → ¬ support x y → StepAfter x y

/-- Concrete locality lemma: every valid before-path that avoids the modified
support remains a valid after-path. -/
theorem path_survives_if_avoids_support
    {X : Type*}
    {StepBefore StepAfter support : X → X → Prop}
    (hlocal : EdgeLocalTransformation StepBefore StepAfter support) :
    ∀ p : List X,
      IsPath StepBefore p →
      AvoidsSupport support p →
      IsPath StepAfter p := by
  intro p
  induction p with
  | nil =>
      intro _ _
      simp [IsPath]
  | cons x xs ih =>
      cases xs with
      | nil =>
          intro _ _
          simp [IsPath]
      | cons y ys =>
          intro hpath hav
          simp [IsPath] at hpath ⊢
          simp [AvoidsSupport] at hav
          constructor
          · exact hlocal x y hpath.1 hav.1
          · exact ih hpath.2 hav.2

/-- A path witnesses a future bundle when it is valid and satisfies an
arbitrary bundle-specific acceptance predicate.  The acceptance predicate is
deliberately independent of the transformation: only the transition support
changes. -/
def Witnesses {Q X : Type*}
    (Step : X → X → Prop)
    (Accepts : Finset Q → List X → Prop)
    (F : Finset Q) (p : List X) : Prop :=
  IsPath Step p ∧ Accepts F p

/-- WITNESS INTERCEPTION THEOREM.
If a bundle has a witness before a local edge transformation and has no witness
after it, then every before-witness must cross the modified support. Otherwise
that witness would survive unchanged. -/
theorem destroyed_bundle_intercepts_every_witness
    {Q X : Type*}
    {StepBefore StepAfter support : X → X → Prop}
    {Accepts : Finset Q → List X → Prop}
    (hlocal : EdgeLocalTransformation StepBefore StepAfter support)
    {F : Finset Q}
    (hbefore : ∃ p, Witnesses StepBefore Accepts F p)
    (hafter : ¬ ∃ p, Witnesses StepAfter Accepts F p) :
    ∀ p,
      Witnesses StepBefore Accepts F p →
      ¬ AvoidsSupport support p := by
  intro p hp hav
  apply hafter
  refine ⟨p, ?_⟩
  exact ⟨path_survives_if_avoids_support hlocal p hp.1 hav, hp.2⟩

/-- Equivalent existential form: each before-witness to a destroyed bundle
contains at least one adjacent edge in the modified support. -/
def CrossesSupport {X : Type*}
    (support : X → X → Prop) : List X → Prop
  | [] => False
  | [_] => False
  | x :: y :: xs => support x y ∨ CrossesSupport support (y :: xs)

theorem not_avoidsSupport_iff_crossesSupport
    {X : Type*}
    {support : X → X → Prop} :
    ∀ p : List X, ¬ AvoidsSupport support p ↔ CrossesSupport support p := by
  intro p
  induction p with
  | nil =>
      simp [AvoidsSupport, CrossesSupport]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [AvoidsSupport, CrossesSupport]
      | cons y ys =>
          simp [AvoidsSupport, CrossesSupport, ih]

theorem destroyed_bundle_every_witness_crosses_support
    {Q X : Type*}
    {StepBefore StepAfter support : X → X → Prop}
    {Accepts : Finset Q → List X → Prop}
    (hlocal : EdgeLocalTransformation StepBefore StepAfter support)
    {F : Finset Q}
    (hbefore : ∃ p, Witnesses StepBefore Accepts F p)
    (hafter : ¬ ∃ p, Witnesses StepAfter Accepts F p) :
    ∀ p,
      Witnesses StepBefore Accepts F p →
      CrossesSupport support p := by
  intro p hp
  exact (not_avoidsSupport_iff_crossesSupport p).mp
    (destroyed_bundle_intercepts_every_witness hlocal hbefore hafter p hp)

end WitnessInterception
end InsacermoActionabilityInformation
