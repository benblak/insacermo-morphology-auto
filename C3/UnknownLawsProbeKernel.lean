import C3.DoubleEnvelopeKernel

/- INSACERMO C3+: epistemic law uncertainty + noisy/nondeterministic observations.
   A scenario explicitly includes a candidate environmental law.
   All guarantees remain relative to the declared envelopes, success predicate,
   and observation-support relation; no assumption that all real laws are known. -/

namespace INSACERMO.C3Plus

open INSACERMO.C3
universe u v w z

abbrev Scenario (World : Type u) (Law : Type v) := World × Law

variable {World : Type u} {Law : Type v} {Policy : Type w} {Outcome : Type z}

def posterior (e : Envelope (Scenario World Law) Policy)
    (observes : Scenario World Law → Outcome → Prop) (outcome : Outcome) :
    Envelope (Scenario World Law) Policy where
  lowerWorld := fun s => e.lowerWorld s ∧ observes s outcome
  upperWorld := fun s => e.upperWorld s ∧ observes s outcome
  lowerPolicy := e.lowerPolicy
  upperPolicy := e.upperPolicy
  worldBounds := by
    intro s hs
    exact ⟨e.worldBounds s hs.1, hs.2⟩
  policyBounds := e.policyBounds

def sensorTotal (upper : Scenario World Law → Prop)
    (observes : Scenario World Law → Outcome → Prop) : Prop :=
  ∀ s, upper s → ∃ o, observes s o

/- A safe PROBE must yield at least one declared possible observation for every
   admissible scenario and must have a known policy for *every* possible outcome.
   The observation relation may overlap between different laws or states. -/
def SafeProbe (e : Envelope (Scenario World Law) Policy)
    (observes : Scenario World Law → Outcome → Prop)
    (good : Policy → Scenario World Law → Prop) : Prop :=
  sensorTotal e.upperWorld observes ∧
    ∃ plan : Outcome → Policy,
      (∀ o, e.lowerPolicy (plan o)) ∧
      ∀ o s, e.upperWorld s → observes s o → good (plan o) s

theorem possible_scenario_not_discarded
    (e : Envelope (Scenario World Law) Policy)
    (observes : Scenario World Law → Outcome → Prop)
    (s : Scenario World Law) (o : Outcome)
    (hs : e.upperWorld s) (ho : observes s o) :
    (posterior e observes o).upperWorld s := ⟨hs, ho⟩

theorem true_support_after_observation
    (e : Envelope (Scenario World Law) Policy)
    (observes : Scenario World Law → Outcome → Prop)
    {actual : Scenario World Law → Prop}
    (hactual : Incl actual e.upperWorld)
    (o : Outcome) :
    Incl (fun s => actual s ∧ observes s o)
      (posterior e observes o).upperWorld := by
  intro s hs
  exact ⟨hactual s hs.1, hs.2⟩

theorem after_observation_act_sound
    (e : Envelope (Scenario World Law) Policy)
    (observes : Scenario World Law → Outcome → Prop)
    (good : Policy → Scenario World Law → Prop)
    {actual : Scenario World Law → Prop}
    {available : Policy → Prop}
    (hactual : Incl actual e.upperWorld)
    (havailable : PolicyIncl e.lowerPolicy available)
    (o : Outcome)
    (hact : ACT (posterior e observes o) good) :
    Succeeds good (fun s => actual s ∧ observes s o) available := by
  exact act_sound (posterior e observes o) good
    (true_support_after_observation e observes hactual o) havailable hact

theorem safe_probe_actual_sound
    (e : Envelope (Scenario World Law) Policy)
    (observes : Scenario World Law → Outcome → Prop)
    (good : Policy → Scenario World Law → Prop)
    {actual : Scenario World Law → Prop}
    {available : Policy → Prop}
    (hactual : Incl actual e.upperWorld)
    (havailable : PolicyIncl e.lowerPolicy available)
    (h : SafeProbe e observes good) :
    (∀ s, actual s → ∃ o, observes s o) ∧
      ∃ plan : Outcome → Policy,
        (∀ o, available (plan o)) ∧
        ∀ o s, actual s → observes s o → good (plan o) s := by
  rcases h with ⟨htotal, ⟨plan, hknown, hcorrect⟩⟩
  refine ⟨?_, ⟨plan, ?_, ?_⟩⟩
  · intro s hs
    exact htotal s (hactual s hs)
  · intro o
    exact havailable (plan o) (hknown o)
  · intro o s hs ho
    exact hcorrect o s (hactual s hs) ho

theorem safe_probe_iff_all_branches_act
    (e : Envelope (Scenario World Law) Policy)
    (observes : Scenario World Law → Outcome → Prop)
    (good : Policy → Scenario World Law → Prop) :
    SafeProbe e observes good ↔
      sensorTotal e.upperWorld observes ∧
        ∀ o, ACT (posterior e observes o) good := by
  constructor
  · intro h
    rcases h with ⟨htotal, ⟨plan, hknown, hcorrect⟩⟩
    refine ⟨htotal, ?_⟩
    intro o
    exact ⟨plan o, hknown o, fun s hpost => hcorrect o s hpost.1 hpost.2⟩
  · rintro ⟨htotal, hbranches⟩
    classical
    let plan : Outcome → Policy := fun o => Classical.choose (hbranches o)
    refine ⟨htotal, ⟨plan, ?_, ?_⟩⟩
    · intro o
      exact (Classical.choose_spec (hbranches o)).1
    · intro o s hs ho
      exact (Classical.choose_spec (hbranches o)).2 s ⟨hs, ho⟩

theorem uninformative_probe_cannot_replace_act
    (e : Envelope (Scenario World Law) Policy)
    (observes : Scenario World Law → Outcome → Prop)
    (good : Policy → Scenario World Law → Prop)
    (o : Outcome)
    (hconstant : ∀ s, e.upperWorld s → observes s o)
    (hprobe : SafeProbe e observes good) :
    ACT e good := by
  rcases hprobe.2 with ⟨plan, hknown, hcorrect⟩
  exact ⟨plan o, hknown o, fun s hs => hcorrect o s hs (hconstant s hs)⟩

/- Explicit witness: the correct action depends on which law is real.
   A perfect observation reveals it, while a nondiscriminating/noisy one does not.
   This is a tiny finite *counterexample*, not a universal law-discovery engine. -/
def twoLaws : Envelope (Scenario Unit Bool) Bool where
  lowerWorld := fun _ => True
  upperWorld := fun _ => True
  lowerPolicy := fun _ => True
  upperPolicy := fun _ => True
  worldBounds := by intro s hs; trivial
  policyBounds := by intro p hp; trivial

def lawGood (p : Bool) (s : Scenario Unit Bool) : Prop := p = s.2
def revealingObs (s : Scenario Unit Bool) (o : Bool) : Prop := o = s.2
def ambiguousObs (_s : Scenario Unit Bool) (_o : Bool) : Prop := True

theorem no_fixed_policy : ¬ ACT twoLaws lawGood := by
  intro hact
  rcases hact with ⟨p, hp, hgood⟩
  have hfalse : p = false := hgood ((), false) (by trivial)
  have htrue : p = true := hgood ((), true) (by trivial)
  cases p with
  | false => simp at htrue
  | true => simp at hfalse

theorem immediate_refuse : REFUSE twoLaws lawGood :=
  no_fixed_policy

theorem revealing_probe_succeeds : SafeProbe twoLaws revealingObs lawGood := by
  refine ⟨?_, ?_⟩
  · intro s hs
    exact ⟨s.2, rfl⟩
  · refine ⟨(fun o => o), ?_, ?_⟩
    · intro o
      trivial
    · intro o s hs ho
      exact ho

theorem ambiguous_probe_cannot_succeed :
    ¬ SafeProbe twoLaws ambiguousObs lawGood := by
  intro hprobe
  apply no_fixed_policy
  exact uninformative_probe_cannot_replace_act
    twoLaws ambiguousObs lawGood false
    (by intro s hs; trivial) hprobe

end INSACERMO.C3Plus
