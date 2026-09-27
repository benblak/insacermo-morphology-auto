import InsacermoV13Kernel.TotalClosure

namespace InsacermoV13Kernel

universe uC uW uCA uAA uO uM

/-- Pull an abstract observation back to the concrete world through a declared
    state abstraction. -/
def PullbackObs
    {ConcreteWorld : Type uC} {World : Type uW} {Obs : Type uO}
    (abstractState : ConcreteWorld → World)
    (obs : World → Obs) : ConcreteWorld → Obs :=
  fun x => obs (abstractState x)

/-- A sound concrete-to-INSACERMO adapter.

    abstractState is the state abstraction and realizeAction interprets an
    abstract action as a concrete action.

    Soundness is deliberately one-sided:
      * every abstract action declared available is concretely available;
      * every abstract admissibility certificate at the abstraction of a
        concrete state implies the corresponding concrete contract fact.

    This is exactly the direction needed to ensure that an abstract ACT
    certificate cannot become a false concrete ACT merely because of the
    adapter. -/
def ConcreteAdapterSound
    {ConcreteWorld : Type uC} {World : Type uW}
    {ConcreteAction : Type uCA} {Action : Type uAA}
    (abstractState : ConcreteWorld → World)
    (realizeAction : Action → ConcreteAction)
    (abstractAvailable : Action → Prop)
    (concreteAvailable : ConcreteAction → Prop)
    (abstractAdmissible : World → Action → Prop)
    (concreteGood : ConcreteWorld → ConcreteAction → Prop) : Prop :=
  (∀ ⦃a : Action⦄,
      abstractAvailable a → concreteAvailable (realizeAction a)) ∧
  (∀ ⦃x : ConcreteWorld⦄ ⦃a : Action⦄,
      abstractAdmissible (abstractState x) a →
        concreteGood x (realizeAction a))

/-- Completeness conditions for the reverse direction.

    These assumptions are stronger than soundness and are intentionally
    explicit. They say:
      * every abstract state is represented by some concrete state;
      * every concretely available action has an abstract representative;
      * concrete goodness of a represented abstract action is reflected by
        abstract admissibility.

    Under these hypotheses, abstract REFUSE can be interpreted as concrete
    impossibility for the induced observation. Without them, REFUSE means only
    "not certified by this abstraction". -/
def ConcreteAdapterComplete
    {ConcreteWorld : Type uC} {World : Type uW}
    {ConcreteAction : Type uCA} {Action : Type uAA}
    (abstractState : ConcreteWorld → World)
    (realizeAction : Action → ConcreteAction)
    (abstractAvailable : Action → Prop)
    (concreteAvailable : ConcreteAction → Prop)
    (abstractAdmissible : World → Action → Prop)
    (concreteGood : ConcreteWorld → ConcreteAction → Prop) : Prop :=
  Function.Surjective abstractState ∧
  (∀ ⦃u : ConcreteAction⦄,
      concreteAvailable u →
        ∃ a : Action, abstractAvailable a ∧ realizeAction a = u) ∧
  (∀ ⦃x : ConcreteWorld⦄ ⦃a : Action⦄,
      concreteGood x (realizeAction a) →
        abstractAdmissible (abstractState x) a)

/-- Core bridge theorem: a safe abstract fiber pulls back to a safe concrete
    fiber under a sound adapter. -/
theorem fiberSafe_pullback_of_sound
    {ConcreteWorld : Type uC} {World : Type uW}
    {ConcreteAction : Type uCA} {Action : Type uAA}
    {Obs : Type uO}
    {abstractState : ConcreteWorld → World}
    {realizeAction : Action → ConcreteAction}
    {abstractAvailable : Action → Prop}
    {concreteAvailable : ConcreteAction → Prop}
    {abstractAdmissible : World → Action → Prop}
    {concreteGood : ConcreteWorld → ConcreteAction → Prop}
    {obs : World → Obs}
    {x : ConcreteWorld}
    (hsound :
      ConcreteAdapterSound
        abstractState realizeAction
        abstractAvailable concreteAvailable
        abstractAdmissible concreteGood)
    (hsafe :
      FiberSafe obs abstractAvailable abstractAdmissible (abstractState x)) :
    FiberSafe
      (PullbackObs abstractState obs)
      concreteAvailable concreteGood x := by
  rcases hsafe with ⟨a, haAvail, hall⟩
  refine ⟨realizeAction a, hsound.1 haAvail, ?_⟩
  intro y hy
  apply hsound.2
  apply hall
  simpa [PullbackObs] using hy

/-- Global ACT-soundness of the adapter: every abstract globally safe
    observation induces a globally safe concrete observation. -/
theorem globalSafe_pullback_of_sound
    {ConcreteWorld : Type uC} {World : Type uW}
    {ConcreteAction : Type uCA} {Action : Type uAA}
    {Obs : Type uO}
    {abstractState : ConcreteWorld → World}
    {realizeAction : Action → ConcreteAction}
    {abstractAvailable : Action → Prop}
    {concreteAvailable : ConcreteAction → Prop}
    {abstractAdmissible : World → Action → Prop}
    {concreteGood : ConcreteWorld → ConcreteAction → Prop}
    {obs : World → Obs}
    (hsound :
      ConcreteAdapterSound
        abstractState realizeAction
        abstractAvailable concreteAvailable
        abstractAdmissible concreteGood)
    (hsafe :
      GlobalSafe obs abstractAvailable abstractAdmissible) :
    GlobalSafe
      (PullbackObs abstractState obs)
      concreteAvailable concreteGood := by
  intro x
  exact fiberSafe_pullback_of_sound hsound (hsafe (abstractState x))

/-- A certified abstract message protocol can be executed concretely through a
    sound adapter without changing its message alphabet. -/
theorem certifiedProtocol_pullback_of_sound
    {ConcreteWorld : Type uC} {World : Type uW}
    {ConcreteAction : Type uCA} {Action : Type uAA}
    {Message : Type uM}
    {abstractState : ConcreteWorld → World}
    {realizeAction : Action → ConcreteAction}
    {abstractAvailable : Action → Prop}
    {concreteAvailable : ConcreteAction → Prop}
    {abstractAdmissible : World → Action → Prop}
    {concreteGood : ConcreteWorld → ConcreteAction → Prop}
    (hsound :
      ConcreteAdapterSound
        abstractState realizeAction
        abstractAvailable concreteAvailable
        abstractAdmissible concreteGood)
    (hprotocol :
      CertifiedProtocol
        abstractAvailable abstractAdmissible Message) :
    CertifiedProtocol
      concreteAvailable concreteGood Message := by
  rcases hprotocol with ⟨encode, decode, havail, hcert⟩
  refine
    ⟨(fun x => encode (abstractState x)),
     (fun m => realizeAction (decode m)),
     ?_, ?_⟩
  · intro m
    exact hsound.1 (havail m)
  · intro x
    exact hsound.2 (hcert (abstractState x))

/-- Therefore every finite safe-symbol budget established in the abstract
    INSACERMO model is also a sufficient concrete symbol budget after pullback.
    This is a sufficiency statement, not a claim that the budget is concretely
    minimal. -/
theorem safeEncoding_pullback_of_sound
    {ConcreteWorld : Type uC} {World : Type uW}
    {ConcreteAction : Type uCA} {Action : Type uAA}
    {abstractState : ConcreteWorld → World}
    {realizeAction : Action → ConcreteAction}
    {abstractAvailable : Action → Prop}
    {concreteAvailable : ConcreteAction → Prop}
    {abstractAdmissible : World → Action → Prop}
    {concreteGood : ConcreteWorld → ConcreteAction → Prop}
    {n : Nat}
    (hsound :
      ConcreteAdapterSound
        abstractState realizeAction
        abstractAvailable concreteAvailable
        abstractAdmissible concreteGood)
    (henc :
      SafeEncoding abstractAvailable abstractAdmissible n) :
    SafeEncoding concreteAvailable concreteGood n := by
  rcases henc with ⟨obs, hsafe⟩
  exact ⟨PullbackObs abstractState obs,
    globalSafe_pullback_of_sound hsound hsafe⟩

/-- Under adapter completeness, concrete safety of the pulled-back observation
    reflects back to abstract safety at the represented abstract state. -/
theorem fiberSafe_reflects_of_complete
    {ConcreteWorld : Type uC} {World : Type uW}
    {ConcreteAction : Type uCA} {Action : Type uAA}
    {Obs : Type uO}
    {abstractState : ConcreteWorld → World}
    {realizeAction : Action → ConcreteAction}
    {abstractAvailable : Action → Prop}
    {concreteAvailable : ConcreteAction → Prop}
    {abstractAdmissible : World → Action → Prop}
    {concreteGood : ConcreteWorld → ConcreteAction → Prop}
    {obs : World → Obs}
    {x : ConcreteWorld}
    (hcomplete :
      ConcreteAdapterComplete
        abstractState realizeAction
        abstractAvailable concreteAvailable
        abstractAdmissible concreteGood)
    (hsafe :
      FiberSafe
        (PullbackObs abstractState obs)
        concreteAvailable concreteGood x) :
    FiberSafe obs abstractAvailable abstractAdmissible (abstractState x) := by
  rcases hsafe with ⟨u, huAvail, hall⟩
  rcases hcomplete.2.1 huAvail with ⟨a, haAvail, hrealize⟩
  refine ⟨a, haAvail, ?_⟩
  intro y hy
  rcases hcomplete.1 y with ⟨yc, hyc⟩
  have hfib :
      PullbackObs abstractState obs yc =
        PullbackObs abstractState obs x := by
    simpa [PullbackObs, hyc] using hy
  have hgoodU : concreteGood yc u := hall hfib
  have hgoodA : concreteGood yc (realizeAction a) := by
    simpa [hrealize] using hgoodU
  have habs :
      abstractAdmissible (abstractState yc) a :=
    hcomplete.2.2 hgoodA
  simpa [hyc] using habs

/-- Global reflection under completeness. This is the extra condition required
    before an abstract failure may be promoted from "not certified" to a
    concrete impossibility claim for the induced observation. -/
theorem globalSafe_reflects_of_complete
    {ConcreteWorld : Type uC} {World : Type uW}
    {ConcreteAction : Type uCA} {Action : Type uAA}
    {Obs : Type uO}
    {abstractState : ConcreteWorld → World}
    {realizeAction : Action → ConcreteAction}
    {abstractAvailable : Action → Prop}
    {concreteAvailable : ConcreteAction → Prop}
    {abstractAdmissible : World → Action → Prop}
    {concreteGood : ConcreteWorld → ConcreteAction → Prop}
    {obs : World → Obs}
    (hcomplete :
      ConcreteAdapterComplete
        abstractState realizeAction
        abstractAvailable concreteAvailable
        abstractAdmissible concreteGood)
    (hsafe :
      GlobalSafe
        (PullbackObs abstractState obs)
        concreteAvailable concreteGood) :
    GlobalSafe obs abstractAvailable abstractAdmissible := by
  intro s
  rcases hcomplete.1 s with ⟨x, hx⟩
  have hlocal :
      FiberSafe obs abstractAvailable abstractAdmissible
        (abstractState x) :=
    fiberSafe_reflects_of_complete hcomplete (hsafe x)
  simpa [hx] using hlocal

/-- Exact abstraction theorem.

    With both soundness and completeness, abstract and concrete global safety
    coincide exactly for the pulled-back observation. -/
theorem globalSafe_iff_concrete_of_exact_adapter
    {ConcreteWorld : Type uC} {World : Type uW}
    {ConcreteAction : Type uCA} {Action : Type uAA}
    {Obs : Type uO}
    {abstractState : ConcreteWorld → World}
    {realizeAction : Action → ConcreteAction}
    {abstractAvailable : Action → Prop}
    {concreteAvailable : ConcreteAction → Prop}
    {abstractAdmissible : World → Action → Prop}
    {concreteGood : ConcreteWorld → ConcreteAction → Prop}
    {obs : World → Obs}
    (hsound :
      ConcreteAdapterSound
        abstractState realizeAction
        abstractAvailable concreteAvailable
        abstractAdmissible concreteGood)
    (hcomplete :
      ConcreteAdapterComplete
        abstractState realizeAction
        abstractAvailable concreteAvailable
        abstractAdmissible concreteGood) :
    GlobalSafe obs abstractAvailable abstractAdmissible ↔
      GlobalSafe
        (PullbackObs abstractState obs)
        concreteAvailable concreteGood := by
  constructor
  · exact globalSafe_pullback_of_sound hsound
  · exact globalSafe_reflects_of_complete hcomplete

/-- REFUSE discipline: under completeness, an abstract global failure implies
    concrete global failure for the induced observation. -/
theorem concrete_not_globalSafe_of_abstract_refuse
    {ConcreteWorld : Type uC} {World : Type uW}
    {ConcreteAction : Type uCA} {Action : Type uAA}
    {Obs : Type uO}
    {abstractState : ConcreteWorld → World}
    {realizeAction : Action → ConcreteAction}
    {abstractAvailable : Action → Prop}
    {concreteAvailable : ConcreteAction → Prop}
    {abstractAdmissible : World → Action → Prop}
    {concreteGood : ConcreteWorld → ConcreteAction → Prop}
    {obs : World → Obs}
    (hcomplete :
      ConcreteAdapterComplete
        abstractState realizeAction
        abstractAvailable concreteAvailable
        abstractAdmissible concreteGood)
    (hrefuse :
      ¬ GlobalSafe obs abstractAvailable abstractAdmissible) :
    ¬ GlobalSafe
      (PullbackObs abstractState obs)
      concreteAvailable concreteGood := by
  intro hconcrete
  exact hrefuse (globalSafe_reflects_of_complete hcomplete hconcrete)

namespace AdapterGapWitness

inductive ConcreteAction
  | blocked
  | rescue

inductive AbstractAction
  | blocked

open ConcreteAction AbstractAction

def abstractState : Unit → Unit := fun _ => ()

def realizeAction : AbstractAction → ConcreteAction
  | AbstractAction.blocked => ConcreteAction.blocked

def abstractAvailable : AbstractAction → Prop :=
  fun _ => True

def concreteAvailable : ConcreteAction → Prop :=
  fun _ => True

def abstractAdmissible : Unit → AbstractAction → Prop :=
  fun _ _ => False

def concreteGood : Unit → ConcreteAction → Prop
  | _, ConcreteAction.blocked => False
  | _, ConcreteAction.rescue => True

def obs : Unit → Unit := fun _ => ()

/-- The adapter is sound: it never certifies a false concrete fact. -/
theorem adapter_sound :
    ConcreteAdapterSound
      abstractState realizeAction
      abstractAvailable concreteAvailable
      abstractAdmissible concreteGood := by
  constructor
  · intro a ha
    trivial
  · intro x a h
    exact False.elim h

/-- Yet the abstract model cannot certify ACT because it omitted the concrete
    rescue action. -/
theorem abstract_refuse :
    ¬ GlobalSafe obs abstractAvailable abstractAdmissible := by
  intro h
  rcases h () with ⟨a, ha, hall⟩
  have hbad : abstractAdmissible () a := hall rfl
  exact hbad

/-- The concrete world is in fact globally safe via the omitted rescue action. -/
theorem concrete_act :
    GlobalSafe
      (PullbackObs abstractState obs)
      concreteAvailable concreteGood := by
  intro x
  refine ⟨ConcreteAction.rescue, trivial, ?_⟩
  intro y hy
  trivial

/-- Formal counterexample to the invalid inference
      abstract REFUSE -> concrete impossibility
    when only adapter soundness is known. -/
theorem soundness_alone_does_not_make_refuse_real :
    ConcreteAdapterSound
      abstractState realizeAction
      abstractAvailable concreteAvailable
      abstractAdmissible concreteGood ∧
    (¬ GlobalSafe obs abstractAvailable abstractAdmissible) ∧
    GlobalSafe
      (PullbackObs abstractState obs)
      concreteAvailable concreteGood := by
  exact ⟨adapter_sound, abstract_refuse, concrete_act⟩

end AdapterGapWitness

end InsacermoV13Kernel
