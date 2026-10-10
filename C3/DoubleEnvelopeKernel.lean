import Lean

/- INSACERMO C3: double epistemic envelope.
   This is an independent *candidate* kernel. Full verification requires a green Lean CI.
   Validity is relative to the declared success predicate and admissible policy universe. -/
namespace INSACERMO.C3

universe u v
variable {World : Type u} {Policy : Type v}

def Incl (A B : World → Prop) : Prop := ∀ w, A w → B w
def PolicyIncl (A B : Policy → Prop) : Prop := ∀ p, A p → B p

structure Envelope (World : Type u) (Policy : Type v) where
  lowerWorld : World → Prop
  upperWorld : World → Prop
  lowerPolicy : Policy → Prop
  upperPolicy : Policy → Prop
  worldBounds : Incl lowerWorld upperWorld
  policyBounds : PolicyIncl lowerPolicy upperPolicy

def Succeeds (good : Policy → World → Prop)
    (worlds : World → Prop) (policies : Policy → Prop) : Prop :=
  ∃ p, policies p ∧ ∀ w, worlds w → good p w

def ACT (e : Envelope World Policy) (good : Policy → World → Prop) : Prop :=
  Succeeds good e.upperWorld e.lowerPolicy

def REFUSE (e : Envelope World Policy) (good : Policy → World → Prop) : Prop :=
  ¬ Succeeds good e.lowerWorld e.upperPolicy

def OPEN (e : Envelope World Policy) (good : Policy → World → Prop) : Prop :=
  ¬ ACT e good ∧ ¬ REFUSE e good

theorem success_antitone_world (good : Policy → World → Prop)
    {A B : World → Prop} {Q : Policy → Prop} (h : Incl A B)
    (s : Succeeds good B Q) : Succeeds good A Q := by
  rcases s with ⟨p, hp, hg⟩
  exact ⟨p, hp, fun w hw => hg w (h w hw)⟩

theorem success_monotone_policies (good : Policy → World → Prop)
    {A B : Policy → Prop} {X : World → Prop} (h : PolicyIncl A B)
    (s : Succeeds good X A) : Succeeds good X B := by
  rcases s with ⟨p, hp, hg⟩
  exact ⟨p, h p hp, hg⟩

theorem act_sound (e : Envelope World Policy)
    (good : Policy → World → Prop) {realWorld : World → Prop}
    {realPolicy : Policy → Prop} (hw : Incl realWorld e.upperWorld)
    (hp : PolicyIncl e.lowerPolicy realPolicy)
    (h : ACT e good) : Succeeds good realWorld realPolicy :=
  success_monotone_policies good hp (success_antitone_world good hw h)

theorem refuse_sound (e : Envelope World Policy)
    (good : Policy → World → Prop) {realWorld : World → Prop}
    {realPolicy : Policy → Prop} (hw : Incl e.lowerWorld realWorld)
    (hp : PolicyIncl realPolicy e.upperPolicy)
    (h : REFUSE e good) : ¬ Succeeds good realWorld realPolicy := by
  intro hreal
  apply h
  exact success_monotone_policies good hp
    (success_antitone_world good hw hreal)

theorem act_implies_not_refuse (e : Envelope World Policy)
    (good : Policy → World → Prop) (h : ACT e good) : ¬ REFUSE e good := by
  intro hr
  apply hr
  exact success_monotone_policies good e.policyBounds
    (success_antitone_world good e.worldBounds h)

theorem verdict_trichotomy (e : Envelope World Policy)
    (good : Policy → World → Prop) :
    ACT e good ∨ REFUSE e good ∨ OPEN e good := by
  classical
  by_cases ha : ACT e good
  · exact Or.inl ha
  · by_cases hr : REFUSE e good
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr ⟨ha, hr⟩)

theorem open_has_possible_success (e : Envelope World Policy)
    (good : Policy → World → Prop) (h : OPEN e good) :
    Succeeds good e.lowerWorld e.upperPolicy := by
  classical
  exact not_not.mp h.2

theorem open_has_possible_failure (e : Envelope World Policy)
    (good : Policy → World → Prop) (h : OPEN e good) :
    ¬ Succeeds good e.upperWorld e.lowerPolicy := h.1

theorem refinement_preserves_act
    (e e' : Envelope World Policy) (good : Policy → World → Prop)
    (hWorld : Incl e'.upperWorld e.upperWorld)
    (hPolicy : PolicyIncl e.lowerPolicy e'.lowerPolicy)
    (ha : ACT e good) : ACT e' good :=
  success_monotone_policies good hPolicy
    (success_antitone_world good hWorld ha)

theorem refinement_preserves_refuse
    (e e' : Envelope World Policy) (good : Policy → World → Prop)
    (hWorld : Incl e.lowerWorld e'.lowerWorld)
    (hPolicy : PolicyIncl e'.upperPolicy e.upperPolicy)
    (hr : REFUSE e good) : REFUSE e' good := by
  intro hs
  apply hr
  exact success_monotone_policies good hPolicy
    (success_antitone_world good hWorld hs)

end INSACERMO.C3
