import Std

namespace Insacermo

universe u v w

abbrev WSet (World : Type u) := World → Prop
abbrev CapSet (Action : Type v) := Action → Prop

def Subset {World : Type u} (A B : WSet World) : Prop :=
  ∀ x, A x → B x

def StrictSubset {World : Type u} (A B : WSet World) : Prop :=
  Subset A B ∧ ¬ Subset B A

def Actionable
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World) : Prop :=
  ∃ a, C a ∧ ∀ x, B x → good x a

def GoodRegion
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (b : Action) : WSet World :=
  fun x => good x b

def AddCapability
    {Action : Type v}
    (C : CapSet Action)
    (b : Action) : CapSet Action :=
  fun a => C a ∨ a = b

def Obstruction
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World) : Prop :=
  ¬ Actionable good C B

def MinimalObstruction
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World) : Prop :=
  Obstruction good C B ∧
  ∀ G, StrictSubset G B → Actionable good C G

def SurvivingObstruction
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (b : Action)
    (B : WSet World) : Prop :=
  Obstruction good C B ∧
  ¬ Subset B (GoodRegion good b)

/-- Actionability is downward closed in the ambiguity set. -/
theorem actionable_downward
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    {A B : WSet World}
    (hAB : Subset A B)
    (hB : Actionable good C B) :
    Actionable good C A := by
  obtain ⟨a, haC, haB⟩ := hB
  exact ⟨a, haC, fun x hx => haB x (hAB x hx)⟩

/-- Adding optional capabilities cannot destroy an actionable ambiguity set. -/
theorem actionable_capability_mono
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    {C D : CapSet Action}
    {B : WSet World}
    (hCD : ∀ a, C a → D a)
    (hB : Actionable good C B) :
    Actionable good D B := by
  obtain ⟨a, haC, haB⟩ := hB
  exact ⟨a, hCD a haC, haB⟩

/--
FILL LAW.
After adding one capability b, an ambiguity set B is actionable exactly when
it was already actionable or B lies entirely inside the region served by b.
-/
theorem actionable_addCapability_iff
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (b : Action)
    (B : WSet World) :
    Actionable good (AddCapability C b) B ↔
      Actionable good C B ∨ Subset B (GoodRegion good b) := by
  constructor
  · intro h
    obtain ⟨a, ha, hgood⟩ := h
    cases ha with
    | inl haC =>
        exact Or.inl ⟨a, haC, hgood⟩
    | inr hab =>
        subst a
        exact Or.inr (fun x hx => hgood x hx)
  · intro h
    cases h with
    | inl hold =>
        obtain ⟨a, haC, hgood⟩ := hold
        exact ⟨a, Or.inl haC, hgood⟩
    | inr hsub =>
        exact ⟨b, Or.inr rfl, fun x hx => hsub x hx⟩

/--
Exact obstruction survival law.
An ambiguity remains impossible after adding b iff it was impossible before
and is not fully covered by b.
-/
theorem obstruction_addCapability_iff
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (b : Action)
    (B : WSet World) :
    Obstruction good (AddCapability C b) B ↔
      SurvivingObstruction good C b B := by
  unfold Obstruction SurvivingObstruction
  rw [actionable_addCapability_iff]
  constructor
  · intro h
    constructor
    · intro ha
      exact h (Or.inl ha)
    · intro hs
      exact h (Or.inr hs)
  · rintro ⟨hna, hns⟩ h
    cases h with
    | inl ha => exact hna ha
    | inr hs => exact hns hs

/--
HIGHER-ORDER CAPABILITY COLLAPSE.
The new minimal obstructions are exactly the inclusion-minimal surviving old
obstructions. This holds at every obstruction order, not only for pairs.
-/
theorem minimalObstruction_addCapability_iff
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (b : Action)
    (B : WSet World) :
    MinimalObstruction good (AddCapability C b) B ↔
      SurvivingObstruction good C b B ∧
      ∀ G, StrictSubset G B → ¬ SurvivingObstruction good C b G := by
  constructor
  · rintro ⟨hobs, hmins⟩
    constructor
    · exact (obstruction_addCapability_iff good C b B).mp hobs
    · intro G hGB hsurv
      have hobsG : Obstruction good (AddCapability C b) G :=
        (obstruction_addCapability_iff good C b G).mpr hsurv
      exact hobsG (hmins G hGB)
  · rintro ⟨hsurv, hminsurv⟩
    constructor
    · exact (obstruction_addCapability_iff good C b B).mpr hsurv
    · intro G hGB
      apply Classical.byContradiction
      intro hnot
      have hobsG : Obstruction good (AddCapability C b) G := by
        exact hnot
      have hsurvG : SurvivingObstruction good C b G :=
        (obstruction_addCapability_iff good C b G).mp hobsG
      exact hminsurv G hGB hsurvG

/-- Observation fiber inside the current ambiguity set. -/
def Fiber
    {World : Type u} {Obs : Type w}
    (observe : World → Obs)
    (B : WSet World)
    (o : Obs) : WSet World :=
  fun x => B x ∧ observe x = o

/--
CUT LAW.
A passive probe resolves B for the current capability set exactly when every
observation fiber is actionable. This is the static common-action criterion.
-/
def SafeProbe
    {World : Type u} {Action : Type v} {Obs : Type w}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World)
    (observe : World → Obs) : Prop :=
  ∀ o, Actionable good C (Fiber observe B o)

theorem safeProbe_iff_allFibersActionable
    {World : Type u} {Action : Type v} {Obs : Type w}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World)
    (observe : World → Obs) :
    SafeProbe good C B observe ↔
      ∀ o, Actionable good C (Fiber observe B o) := by
  rfl

/-- Obstructions are upward closed in the ambiguity set. -/
theorem obstruction_upward
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    {A B : WSet World}
    (hAB : Subset A B)
    (hA : Obstruction good C A) :
    Obstruction good C B := by
  intro hB
  exact hA (actionable_downward good C hAB hB)

def PointUnion
    {World : Type u}
    (H : WSet World)
    (z : World) : WSet World :=
  fun x => H x ∨ x = z

/--
ONE-STEP EXPOSURE LAW.
If B becomes a genuinely new minimal obstruction after adding one capability b
(i.e. B was not already minimal before), then some old proper obstruction H
inside B is completely repaired by b, and B is exactly H plus one world z
outside b's good region.

This is the order-theoretic core behind the finite k -> k+1 phenomenon.
No finiteness assumption is needed for this structural statement.
-/
theorem newlyMinimal_exposes_one_outsider
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (b : Action)
    (B : WSet World)
    (hnew : MinimalObstruction good (AddCapability C b) B)
    (hnotold : ¬ MinimalObstruction good C B) :
    ∃ H z,
      StrictSubset H B ∧
      Obstruction good C H ∧
      Subset H (GoodRegion good b) ∧
      B z ∧ ¬ GoodRegion good b z ∧
      ∀ x, B x ↔ PointUnion H z x := by
  have hchar := (minimalObstruction_addCapability_iff good C b B).mp hnew
  rcases hchar with ⟨hsurvB, hminsurv⟩

  have hexH : ∃ H, StrictSubset H B ∧ Obstruction good C H := by
    apply Classical.byContradiction
    intro hnone
    apply hnotold
    constructor
    · exact hsurvB.1
    · intro G hGB
      apply Classical.byContradiction
      intro hnotAct
      exact hnone ⟨G, hGB, hnotAct⟩

  obtain ⟨H, hHB, hHobs⟩ := hexH

  have hHcovered : Subset H (GoodRegion good b) := by
    apply Classical.byContradiction
    intro hnotCovered
    exact hminsurv H hHB ⟨hHobs, hnotCovered⟩

  have hexz : ∃ z, B z ∧ ¬ GoodRegion good b z := by
    apply Classical.byContradiction
    intro hnone
    apply hsurvB.2
    intro x hx
    apply Classical.byContradiction
    intro hnotGood
    exact hnone ⟨x, hx, hnotGood⟩

  obtain ⟨z, hzB, hzout⟩ := hexz

  let G : WSet World := PointUnion H z

  have hHG : Subset H G := by
    intro x hx
    exact Or.inl hx

  have hGB : Subset G B := by
    intro x hx
    cases hx with
    | inl hHx => exact hHB.1 x hHx
    | inr hxz =>
        subst x
        exact hzB

  have hGobs : Obstruction good C G :=
    obstruction_upward good C hHG hHobs

  have hGnotCovered : ¬ Subset G (GoodRegion good b) := by
    intro hsub
    exact hzout (hsub z (Or.inr rfl))

  have hGsurv : SurvivingObstruction good C b G :=
    ⟨hGobs, hGnotCovered⟩

  have hBG : Subset B G := by
    apply Classical.byContradiction
    intro hnotBG
    have hstrict : StrictSubset G B := ⟨hGB, hnotBG⟩
    exact hminsurv G hstrict hGsurv

  refine ⟨H, z, hHB, hHobs, hHcovered, hzB, hzout, ?_⟩
  intro x
  constructor
  · intro hx
    exact hBG x hx
  · intro hx
    exact hGB x hx


end Insacermo
