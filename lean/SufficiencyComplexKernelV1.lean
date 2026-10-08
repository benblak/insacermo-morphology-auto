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



/--
STRONG ONE-STEP EXPOSURE.
The old obstruction H exposed inside a genuinely new minimal obstruction can
itself be chosen minimal. Hence one added capability lifts minimal obstruction
order by exactly one along each newly exposed branch (with the empty
obstruction allowed in the zero-capability degenerate case).
-/
theorem newlyMinimal_exposes_oldMinimal_plus_one
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (b : Action)
    (B : WSet World)
    (hnew : MinimalObstruction good (AddCapability C b) B)
    (hnotold : ¬ MinimalObstruction good C B) :
    ∃ H z,
      MinimalObstruction good C H ∧
      Subset H (GoodRegion good b) ∧
      B z ∧ ¬ GoodRegion good b z ∧
      ∀ x, B x ↔ PointUnion H z x := by
  obtain ⟨H, z, hHB, hHobs, hHcovered, hzB, hzout, hBeq⟩ :=
    newlyMinimal_exposes_one_outsider good C b B hnew hnotold

  have hHmin : MinimalObstruction good C H := by
    constructor
    · exact hHobs
    · intro G hGH
      apply Classical.byContradiction
      intro hnotAct
      have hGobs : Obstruction good C G := hnotAct

      let J : WSet World := PointUnion G z

      have hGJ : Subset G J := by
        intro x hx
        exact Or.inl hx

      have hJobs : Obstruction good C J :=
        obstruction_upward good C hGJ hGobs

      have hJnotCovered : ¬ Subset J (GoodRegion good b) := by
        intro hsub
        exact hzout (hsub z (Or.inr rfl))

      have hJsurv : SurvivingObstruction good C b J :=
        ⟨hJobs, hJnotCovered⟩

      have hJB : Subset J B := by
        intro x hx
        cases hx with
        | inl hGx =>
            exact hHB.1 x (hGH.1 x hGx)
        | inr hxz =>
            subst x
            exact hzB

      have hex : ∃ x, H x ∧ ¬ G x := by
        apply Classical.byContradiction
        intro hnone
        apply hGH.2
        intro x hxH
        apply Classical.byContradiction
        intro hxnotG
        exact hnone ⟨x, hxH, hxnotG⟩

      obtain ⟨x, hxH, hxnotG⟩ := hex

      have hxnez : x ≠ z := by
        intro hxz
        subst x
        exact hzout (hHcovered z hxH)

      have hxB : B x := hHB.1 x hxH

      have hxnotJ : ¬ J x := by
        intro hxJ
        cases hxJ with
        | inl hxG => exact hxnotG hxG
        | inr hxeq => exact hxnez hxeq

      have hnotBJ : ¬ Subset B J := by
        intro hsub
        exact hxnotJ (hsub x hxB)

      have hstrictJB : StrictSubset J B := ⟨hJB, hnotBJ⟩

      have hchar := (minimalObstruction_addCapability_iff good C b B).mp hnew
      exact hchar.2 J hstrictJB hJsurv

  exact ⟨H, z, hHmin, hHcovered, hzB, hzout, hBeq⟩

/-! ## Unified future/action sufficiency geometry -/

def FutureCoherent
    {World : Type u}
    (futureEq : World → World → Prop)
    (B : WSet World) : Prop :=
  ∀ x y, B x → B y → futureEq x y

def Sufficient
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    (B : WSet World) : Prop :=
  Actionable good C B ∧ FutureCoherent futureEq B

theorem futureCoherent_downward
    {World : Type u}
    (futureEq : World → World → Prop)
    {A B : WSet World}
    (hAB : Subset A B)
    (hB : FutureCoherent futureEq B) :
    FutureCoherent futureEq A := by
  intro x y hx hy
  exact hB x y (hAB x hx) (hAB y hy)

theorem sufficient_downward
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    {A B : WSet World}
    (hAB : Subset A B)
    (hB : Sufficient good C futureEq B) :
    Sufficient good C futureEq A := by
  exact ⟨
    actionable_downward good C hAB hB.1,
    futureCoherent_downward futureEq hAB hB.2
  ⟩

/--
UNIFIED FILL LAW.
Adding one capability changes only the actionability side of sufficiency:
future coherence is untouched, while the ambiguity becomes actionable either
because it already was or because the new capability covers it completely.
-/
theorem sufficient_addCapability_iff
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    (b : Action)
    (B : WSet World) :
    Sufficient good (AddCapability C b) futureEq B ↔
      FutureCoherent futureEq B ∧
      (Actionable good C B ∨ Subset B (GoodRegion good b)) := by
  unfold Sufficient
  rw [actionable_addCapability_iff]
  constructor
  · rintro ⟨hact, hfuture⟩
    exact ⟨hfuture, hact⟩
  · rintro ⟨hfuture, hact⟩
    exact ⟨hact, hfuture⟩

def RepFiber
    {World : Type u} {Code : Type w}
    (encode : World → Code)
    (z : Code) : WSet World :=
  fun x => encode x = z

def RepresentationSafe
    {World : Type u} {Action : Type v} {Code : Type w}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    (encode : World → Code) : Prop :=
  ∀ z, Sufficient good C futureEq (RepFiber encode z)

/--
A representation is safe exactly when every information fiber is a sufficient
ambiguity set. This is the common fiber form behind future-preserving
compression and capability-relative actionability.
-/
theorem representationSafe_iff_allFibersSufficient
    {World : Type u} {Action : Type v} {Code : Type w}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    (encode : World → Code) :
    RepresentationSafe good C futureEq encode ↔
      ∀ z, Sufficient good C futureEq (RepFiber encode z) := by
  rfl

def FullySafeProbe
    {World : Type u} {Action : Type v} {Obs : Type w}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    (B : WSet World)
    (observe : World → Obs) : Prop :=
  ∀ o, Sufficient good C futureEq (Fiber observe B o)

theorem fullySafeProbe_implies_actionSafe
    {World : Type u} {Action : Type v} {Obs : Type w}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    (B : WSet World)
    (observe : World → Obs)
    (h : FullySafeProbe good C futureEq B observe) :
    SafeProbe good C B observe := by
  intro o
  exact (h o).1

/-! ## Abstract resource frontier -/

def MinimalSufficientResource
    {Resource : Type u}
    (leR : Resource → Resource → Prop)
    (Suff : Resource → Prop)
    (r : Resource) : Prop :=
  Suff r ∧
  ∀ q, leR q r → ¬ leR r q → ¬ Suff q

/--
Minimal sufficient resources form an antichain up to resource equivalence:
if two minimal resources are comparable, the comparison must also hold in the
reverse direction.
-/
theorem minimalSufficient_comparable_implies_equiv
    {Resource : Type u}
    (leR : Resource → Resource → Prop)
    (Suff : Resource → Prop)
    {r s : Resource}
    (hr : MinimalSufficientResource leR Suff r)
    (hs : MinimalSufficientResource leR Suff s)
    (hrs : leR r s) :
    leR s r := by
  apply Classical.byContradiction
  intro hnot
  have hnotSuffR : ¬ Suff r := hs.2 r hrs hnot
  exact hnotSuffR hr.1

/--
COMPENSATION PRINCIPLE.
For an upward-monotone sufficiency predicate, if the current resource r is
insufficient while s is sufficient, then s cannot be no richer than r.
-/
theorem insufficiency_requires_resource_upgrade
    {Resource : Type u}
    (leR : Resource → Resource → Prop)
    (Suff : Resource → Prop)
    (mono : ∀ a b, leR a b → Suff a → Suff b)
    {r s : Resource}
    (hr : ¬ Suff r)
    (hs : Suff s) :
    ¬ leR s r := by
  intro hsr
  exact hr (mono s r hsr hs)


/-! ## Abstract rank-growth consequence -/

def RankBounded
    {Obj : Type u}
    (rank : Obj → Nat)
    (K : Obj → Prop)
    (k : Nat) : Prop :=
  ∀ x, K x → rank x ≤ k

/--
If one transformation can increase the rank of every newly admissible witness
by at most one relative to some predecessor witness, then a chain of m such
transformations increases the global bound by at most m.

This abstract induction isolates the quantitative content of the one-step
exposure law from any particular finite encoding.
-/
theorem iterated_one_step_rank_bound
    {Obj : Type u}
    (rank : Obj → Nat)
    (K : Nat → Obj → Prop)
    (k0 : Nat)
    (h0 : RankBounded rank (K 0) k0)
    (step :
      ∀ n x, K (n+1) x →
        K n x ∨
        ∃ y, K n y ∧ rank x ≤ rank y + 1) :
    ∀ m, RankBounded rank (K m) (k0 + m) := by
  intro m
  induction m with
  | zero =>
      simpa using h0
  | succ n ih =>
      intro x hx
      rcases step n x hx with hold | hnew
      · have hle : rank x ≤ k0 + n := ih x hold
        exact Nat.le_trans hle (Nat.le_add_right (k0 + n) 1)
      · obtain ⟨y, hy, hxy⟩ := hnew
        have hyb : rank y ≤ k0 + n := ih y hy
        have h1 : rank x ≤ (k0 + n) + 1 := by
          exact Nat.le_trans hxy (Nat.add_le_add_right hyb 1)
        simpa [Nat.add_assoc] using h1


/-! ## Batch repair geometry and endpoint/path separation -/

def AddCapabilities
    {Action : Type v}
    (C : CapSet Action)
    (bs : List Action) : CapSet Action :=
  fun a => C a ∨ a ∈ bs

/--
BATCH FILL LAW.
After adding a finite list of capabilities, B is actionable exactly when it
was already actionable or one newly added capability covers all of B.
-/
theorem actionable_addCapabilities_iff
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (bs : List Action)
    (B : WSet World) :
    Actionable good (AddCapabilities C bs) B ↔
      Actionable good C B ∨
      ∃ b, b ∈ bs ∧ Subset B (GoodRegion good b) := by
  constructor
  · intro h
    obtain ⟨a, ha, hgood⟩ := h
    cases ha with
    | inl haC =>
        exact Or.inl ⟨a, haC, hgood⟩
    | inr hab =>
        exact Or.inr ⟨a, hab, fun x hx => hgood x hx⟩
  · intro h
    cases h with
    | inl hold =>
        obtain ⟨a, haC, hgood⟩ := hold
        exact ⟨a, Or.inl haC, hgood⟩
    | inr hnew =>
        obtain ⟨b, hbmem, hsub⟩ := hnew
        exact ⟨b, Or.inr hbmem, fun x hx => hsub x hx⟩

/--
Exact batch obstruction law.
After a finite family of capability additions, B remains impossible exactly
when it was impossible before and no added capability covers B completely.
-/
theorem obstruction_addCapabilities_iff
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (bs : List Action)
    (B : WSet World) :
    Obstruction good (AddCapabilities C bs) B ↔
      Obstruction good C B ∧
      ∀ b, b ∈ bs → ¬ Subset B (GoodRegion good b) := by
  unfold Obstruction
  rw [actionable_addCapabilities_iff]
  constructor
  · intro h
    constructor
    · intro ha
      exact h (Or.inl ha)
    · intro b hb hsub
      exact h (Or.inr ⟨b, hb, hsub⟩)
  · rintro ⟨hold, hcover⟩ h
    cases h with
    | inl ha => exact hold ha
    | inr hnew =>
        obtain ⟨b, hb, hsub⟩ := hnew
        exact hcover b hb hsub

/--
Exact minimal-obstruction characterization after a batch of repairs:
the final minimal obstructions are the inclusion-minimal old obstructions that
escape every newly added capability region.
-/
theorem minimalObstruction_addCapabilities_iff
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (bs : List Action)
    (B : WSet World) :
    MinimalObstruction good (AddCapabilities C bs) B ↔
      (Obstruction good C B ∧
       ∀ b, b ∈ bs → ¬ Subset B (GoodRegion good b)) ∧
      ∀ G, StrictSubset G B →
        ¬ (Obstruction good C G ∧
           ∀ b, b ∈ bs → ¬ Subset G (GoodRegion good b)) := by
  constructor
  · rintro ⟨hobs, hmins⟩
    constructor
    · exact (obstruction_addCapabilities_iff good C bs B).mp hobs
    · intro G hGB hsurv
      have hobsG : Obstruction good (AddCapabilities C bs) G :=
        (obstruction_addCapabilities_iff good C bs G).mpr hsurv
      exact hobsG (hmins G hGB)
  · rintro ⟨hsurv, hminsurv⟩
    constructor
    · exact (obstruction_addCapabilities_iff good C bs B).mpr hsurv
    · intro G hGB
      apply Classical.byContradiction
      intro hnot
      have hobsG : Obstruction good (AddCapabilities C bs) G := hnot
      have hsurvG :=
        (obstruction_addCapabilities_iff good C bs G).mp hobsG
      exact hminsurv G hGB hsurvG

/--
ENDPOINT ORDER INDEPENDENCE.
For the static model, the final actionability geometry depends only on which
capabilities were added, not on their list order or multiplicity.
-/
theorem actionable_batch_endpoint_extensional
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (xs ys : List Action)
    (B : WSet World)
    (hmem : ∀ a, a ∈ xs ↔ a ∈ ys) :
    Actionable good (AddCapabilities C xs) B ↔
      Actionable good (AddCapabilities C ys) B := by
  constructor
  · intro h
    obtain ⟨a, ha, hgood⟩ := h
    cases ha with
    | inl haC =>
        exact ⟨a, Or.inl haC, hgood⟩
    | inr hax =>
        exact ⟨a, Or.inr ((hmem a).mp hax), hgood⟩
  · intro h
    obtain ⟨a, ha, hgood⟩ := h
    cases ha with
    | inl haC =>
        exact ⟨a, Or.inl haC, hgood⟩
    | inr hay =>
        exact ⟨a, Or.inr ((hmem a).mpr hay), hgood⟩

theorem sufficient_addCapabilities_iff
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    (bs : List Action)
    (B : WSet World) :
    Sufficient good (AddCapabilities C bs) futureEq B ↔
      FutureCoherent futureEq B ∧
      (Actionable good C B ∨
       ∃ b, b ∈ bs ∧ Subset B (GoodRegion good b)) := by
  unfold Sufficient
  rw [actionable_addCapabilities_iff]
  constructor
  · rintro ⟨hact, hfuture⟩
    exact ⟨hfuture, hact⟩
  · rintro ⟨hfuture, hact⟩
    exact ⟨hact, hfuture⟩

theorem sufficient_batch_endpoint_extensional
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    (xs ys : List Action)
    (B : WSet World)
    (hmem : ∀ a, a ∈ xs ↔ a ∈ ys) :
    Sufficient good (AddCapabilities C xs) futureEq B ↔
      Sufficient good (AddCapabilities C ys) futureEq B := by
  unfold Sufficient
  constructor
  · rintro ⟨hact, hfuture⟩
    exact ⟨
      (actionable_batch_endpoint_extensional good C xs ys B hmem).mp hact,
      hfuture
    ⟩
  · rintro ⟨hact, hfuture⟩
    exact ⟨
      (actionable_batch_endpoint_extensional good C xs ys B hmem).mpr hact,
      hfuture
    ⟩


/-! ## Concrete endpoint/path separation witness -/

inductive W3 where
  | w0 | w1 | w2
  deriving DecidableEq, Repr

inductive A3 where
  | a0 | a1 | a01
  deriving DecidableEq, Repr

def goodW3 : W3 → A3 → Prop
  | W3.w0, A3.a0  => True
  | W3.w1, A3.a0  => False
  | W3.w2, A3.a0  => False
  | W3.w0, A3.a1  => False
  | W3.w1, A3.a1  => True
  | W3.w2, A3.a1  => False
  | W3.w0, A3.a01 => True
  | W3.w1, A3.a01 => True
  | W3.w2, A3.a01 => False

def baseC3 : CapSet A3 := fun a => a = A3.a0

def B01 : WSet W3 := fun x => x = W3.w0 ∨ x = W3.w1

theorem path_witness_after_a1_not_actionable :
    ¬ Actionable goodW3 (AddCapability baseC3 A3.a1) B01 := by
  intro h
  obtain ⟨a, ha, hgood⟩ := h
  rcases ha with ha | ha
  · subst a
    have := hgood W3.w1 (Or.inr rfl)
    simp [goodW3] at this
  · subst a
    have := hgood W3.w0 (Or.inl rfl)
    simp [goodW3] at this

theorem path_witness_after_a01_actionable :
    Actionable goodW3 (AddCapability baseC3 A3.a01) B01 := by
  refine ⟨A3.a01, Or.inr rfl, ?_⟩
  intro x hx
  rcases hx with rfl | rfl <;> simp [goodW3]

/--
Two repair orders have the same final actionability geometry, while their
first intermediate geometries differ on B01. This is a concrete formal witness
of endpoint/path separation in the static model.
-/
theorem endpoint_same_path_different_witness :
    (¬ Actionable goodW3 (AddCapability baseC3 A3.a1) B01) ∧
    Actionable goodW3 (AddCapability baseC3 A3.a01) B01 ∧
    (∀ B : WSet W3,
      Actionable goodW3 (AddCapabilities baseC3 [A3.a1, A3.a01]) B ↔
      Actionable goodW3 (AddCapabilities baseC3 [A3.a01, A3.a1]) B) := by
  constructor
  · exact path_witness_after_a1_not_actionable
  constructor
  · exact path_witness_after_a01_actionable
  · intro B
    apply actionable_batch_endpoint_extensional
    intro a
    cases a <;> simp


/-! ## Boundary debt and exact exposure geometry -/

def RemovePoint
    {World : Type u}
    (B : WSet World)
    (z : World) : WSet World :=
  fun x => B x ∧ x ≠ z

def BoundaryObstructed
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World)
    (z : World) : Prop :=
  B z ∧ Obstruction good C (RemovePoint B z)

theorem removePoint_subset
    {World : Type u}
    (B : WSet World)
    (z : World) :
    Subset (RemovePoint B z) B := by
  intro x hx
  exact hx.1

theorem removePoint_strict
    {World : Type u}
    (B : WSet World)
    (z : World)
    (hz : B z) :
    StrictSubset (RemovePoint B z) B := by
  constructor
  · exact removePoint_subset B z
  · intro h
    have hzrem := h z hz
    exact hzrem.2 rfl

/--
BOUNDARY CRITERION.
An obstruction is minimal exactly when every one-point deletion is actionable.
This holds without a finiteness assumption.
-/
theorem minimalObstruction_iff_all_point_deletions_actionable
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World) :
    MinimalObstruction good C B ↔
      Obstruction good C B ∧
      ∀ z, B z → Actionable good C (RemovePoint B z) := by
  constructor
  · rintro ⟨hobs, hmin⟩
    constructor
    · exact hobs
    · intro z hz
      exact hmin (RemovePoint B z) (removePoint_strict B z hz)
  · rintro ⟨hobs, hdel⟩
    constructor
    · exact hobs
    · intro G hGB
      apply Classical.byContradiction
      intro hnotAct
      have hex : ∃ z, B z ∧ ¬ G z := by
        apply Classical.byContradiction
        intro hnone
        apply hGB.2
        intro x hxB
        apply Classical.byContradiction
        intro hxnotG
        exact hnone ⟨x, hxB, hxnotG⟩
      obtain ⟨z, hzB, hznotG⟩ := hex
      have hGrem : Subset G (RemovePoint B z) := by
        intro x hxG
        constructor
        · exact hGB.1 x hxG
        · intro hxz
          subst x
          exact hznotG hxG
      exact hnotAct (actionable_downward good C hGrem (hdel z hzB))

/--
NO-SHARING LAW.
A single repair region that covers two distinct codimension-one faces of B
necessarily covers B itself. Therefore a repair that preserves B as an
obstruction can resolve at most one blocked boundary face.
-/
theorem two_boundary_faces_force_full_cover
    {World : Type u}
    (B G : WSet World)
    (x y : World)
    (hxB : B x)
    (hyB : B y)
    (hxy : x ≠ y)
    (hx : Subset (RemovePoint B x) G)
    (hy : Subset (RemovePoint B y) G) :
    Subset B G := by
  intro z hzB
  by_cases hzx : z = x
  · subst z
    apply hy
    exact ⟨hxB, hxy⟩
  · apply hx
    exact ⟨hzB, hzx⟩

/--
A preserving repair cannot simultaneously fix two distinct blocked boundary
faces of the same target obstruction.
-/
theorem preserving_repair_cannot_resolve_two_boundary_faces
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (b : Action)
    (B : WSet World)
    (x y : World)
    (hxB : B x)
    (hyB : B y)
    (hxy : x ≠ y)
    (hpreserve : ¬ Subset B (GoodRegion good b))
    (hx : Subset (RemovePoint B x) (GoodRegion good b))
    (hy : Subset (RemovePoint B y) (GoodRegion good b)) :
    False := by
  apply hpreserve
  exact two_boundary_faces_force_full_cover B (GoodRegion good b)
    x y hxB hyB hxy hx hy

/--
Each previously blocked boundary face of a target B that becomes minimal after
a batch repair must be covered by at least one added capability, while every
such capability must fail to cover B itself.
-/
theorem exposed_boundary_face_gets_preserving_repair
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (bs : List Action)
    (B : WSet World)
    (hnew : MinimalObstruction good (AddCapabilities C bs) B)
    (z : World)
    (hzB : B z)
    (hold : Obstruction good C (RemovePoint B z)) :
    ∃ b, b ∈ bs ∧
      Subset (RemovePoint B z) (GoodRegion good b) ∧
      ¬ Subset B (GoodRegion good b) := by
  have hdelNew :
      Actionable good (AddCapabilities C bs) (RemovePoint B z) :=
    (minimalObstruction_iff_all_point_deletions_actionable
      good (AddCapabilities C bs) B).mp hnew |>.2 z hzB
  have hdelChar :=
    (actionable_addCapabilities_iff good C bs (RemovePoint B z)).mp hdelNew
  have hBobsNew : Obstruction good (AddCapabilities C bs) B := hnew.1
  have hBchar :=
    (obstruction_addCapabilities_iff good C bs B).mp hBobsNew
  cases hdelChar with
  | inl holdAct =>
      exact False.elim (hold holdAct)
  | inr hrep =>
      obtain ⟨b, hb, hsub⟩ := hrep
      exact ⟨b, hb, hsub, hBchar.2 b hb⟩


/-! ## Boundary-repair injectivity -/

/--
INJECTIVE REPAIR ASSIGNMENT.
Assume a function pick assigns to every previously blocked boundary face of B
one added capability that resolves that face while preserving B as an
obstruction. Then distinct blocked boundary points must receive distinct
capabilities.

This is the structural content behind the finite cardinal lower bound:
one preserving repair cannot pay two units of boundary debt.
-/
theorem boundaryRepair_assignment_injective
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (bs : List Action)
    (B : WSet World)
    (pick : World → Action)
    (hpick :
      ∀ z, BoundaryObstructed good C B z →
        pick z ∈ bs ∧
        Subset (RemovePoint B z) (GoodRegion good (pick z)) ∧
        ¬ Subset B (GoodRegion good (pick z))) :
    ∀ x y,
      BoundaryObstructed good C B x →
      BoundaryObstructed good C B y →
      pick x = pick y →
      x = y := by
  intro x y hx hy hpickEq
  apply Classical.byContradiction
  intro hxy
  have hycover :
      Subset (RemovePoint B y) (GoodRegion good (pick x)) := by
    simpa [hpickEq] using (hpick y hy).2.1
  exact preserving_repair_cannot_resolve_two_boundary_faces
    good (pick x) B x y
    hx.1 hy.1 hxy
    (hpick x hx).2.2
    (hpick x hx).2.1
    hycover

/--
Every blocked boundary point of a newly exposed minimal obstruction admits at
least one preserving repair witness from the added batch.
-/
theorem boundaryRepair_witness_exists
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (bs : List Action)
    (B : WSet World)
    (hnew : MinimalObstruction good (AddCapabilities C bs) B) :
    ∀ z, BoundaryObstructed good C B z →
      ∃ b, b ∈ bs ∧
        Subset (RemovePoint B z) (GoodRegion good b) ∧
        ¬ Subset B (GoodRegion good b) := by
  intro z hz
  exact exposed_boundary_face_gets_preserving_repair
    good C bs B hnew z hz.1 hz.2


/-! ## General construction attaining boundary debt -/

def AddBoundaryRepairs
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World)
    (repairFor : World → Action) : CapSet Action :=
  fun a =>
    C a ∨
    ∃ z, BoundaryObstructed good C B z ∧ a = repairFor z

/--
UPPER-BOUND CONSTRUCTION.
Assume B is initially obstructed. For every blocked boundary point z, suppose
repairFor z covers the whole face B\{z} but still does not cover B. Then after
adding all these dedicated boundary repairs, B becomes a minimal obstruction.

Combined with boundary-repair injectivity, this is the structural equality:
one dedicated preserving repair per blocked boundary face is sufficient and
no preserving repair can serve two distinct blocked faces.
-/
theorem dedicated_boundary_repairs_expose_minimal
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World)
    (repairFor : World → Action)
    (hBobs : Obstruction good C B)
    (hcover :
      ∀ z, BoundaryObstructed good C B z →
        Subset (RemovePoint B z) (GoodRegion good (repairFor z)))
    (hpreserve :
      ∀ z, BoundaryObstructed good C B z →
        ¬ Subset B (GoodRegion good (repairFor z))) :
    MinimalObstruction good
      (AddBoundaryRepairs good C B repairFor) B := by
  apply (minimalObstruction_iff_all_point_deletions_actionable
    good (AddBoundaryRepairs good C B repairFor) B).2
  constructor
  · intro hact
    obtain ⟨a, ha, haGood⟩ := hact
    cases ha with
    | inl haC =>
        exact hBobs ⟨a, haC, haGood⟩
    | inr hnew =>
        obtain ⟨z, hzBlocked, hEq⟩ := hnew
        subst a
        exact hpreserve z hzBlocked (fun x hx => haGood x hx)
  · intro z hzB
    by_cases hzOld : Obstruction good C (RemovePoint B z)
    · have hzBlocked : BoundaryObstructed good C B z := ⟨hzB, hzOld⟩
      refine ⟨repairFor z, Or.inr ⟨z, hzBlocked, rfl⟩, ?_⟩
      intro x hx
      exact hcover z hzBlocked x hx
    · have hzActOld : Actionable good C (RemovePoint B z) := by
        apply Classical.byContradiction
        intro hnot
        exact hzOld hnot
      exact actionable_capability_mono good
        (C := C)
        (D := AddBoundaryRepairs good C B repairFor)
        (B := RemovePoint B z)
        (fun a ha => Or.inl ha)
        hzActOld


/-! ## Obstruction-basis reconstruction: negative semantics -/

def Contains
    {World : Type u}
    (B O : WSet World) : Prop :=
  Subset O B

def ObstructionBasis
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (Basis : (WSet World) → Prop) : Prop :=
  (∀ O, Basis O → Obstruction good C O) ∧
  (∀ B, Obstruction good C B → ∃ O, Basis O ∧ Contains B O)

/--
NEGATIVE RECONSTRUCTION LAW.
Given any complete obstruction basis, an ambiguity B is actionable exactly
when it contains no basis obstruction.
-/
theorem actionable_iff_avoids_obstructionBasis
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (Basis : (WSet World) → Prop)
    (hBasis : ObstructionBasis good C Basis)
    (B : WSet World) :
    Actionable good C B ↔
      ∀ O, Basis O → ¬ Contains B O := by
  constructor
  · intro hact O hO hcontains
    have hobsO : Obstruction good C O := hBasis.1 O hO
    exact hobsO (actionable_downward good C hcontains hact)
  · intro havoid
    apply Classical.byContradiction
    intro hnotAct
    have hobsB : Obstruction good C B := hnotAct
    obtain ⟨O, hO, hOB⟩ := hBasis.2 B hobsB
    exact havoid O hO hOB

/--
CANONICAL NEGATIVE SEMANTICS.
Two capability systems sharing the same complete obstruction basis have
exactly the same actionability judgement on every ambiguity set, even if their
action labels or redundant capabilities differ.
-/
theorem same_obstructionBasis_same_actionability
    {World : Type u} {Action₁ : Type v} {Action₂ : Type w}
    (good₁ : World → Action₁ → Prop)
    (good₂ : World → Action₂ → Prop)
    (C₁ : CapSet Action₁)
    (C₂ : CapSet Action₂)
    (Basis : (WSet World) → Prop)
    (h₁ : ObstructionBasis good₁ C₁ Basis)
    (h₂ : ObstructionBasis good₂ C₂ Basis) :
    ∀ B,
      Actionable good₁ C₁ B ↔
      Actionable good₂ C₂ B := by
  intro B
  rw [
    actionable_iff_avoids_obstructionBasis good₁ C₁ Basis h₁ B,
    actionable_iff_avoids_obstructionBasis good₂ C₂ Basis h₂ B
  ]

/--
Any complete obstruction basis is semantically sufficient to answer ACT versus
REFUSE for the static common-action model; the original action representation
is not needed once the basis has been certified.
-/
theorem obstructionBasis_decision_complete
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (Basis : (WSet World) → Prop)
    (hBasis : ObstructionBasis good C Basis) :
    ∀ B,
      (∀ O, Basis O → ¬ Contains B O) → Actionable good C B := by
  intro B h
  exact (actionable_iff_avoids_obstructionBasis good C Basis hBasis B).2 h


/-! ## Unified forbidden-basis decomposition -/

def PairSet
    {World : Type u}
    (x y : World) : WSet World :=
  fun z => z = x ∨ z = y

def FutureConflict
    {World : Type u}
    (futureEq : World → World → Prop)
    (x y : World) : Prop :=
  ¬ futureEq x y

/--
Future coherence is exactly the avoidance of all conflicting pairs.
-/
theorem futureCoherent_iff_avoids_conflictPairs
    {World : Type u}
    (futureEq : World → World → Prop)
    (B : WSet World) :
    FutureCoherent futureEq B ↔
      ∀ x y, FutureConflict futureEq x y →
        ¬ Subset (PairSet x y) B := by
  constructor
  · intro h x y hconf hsub
    apply hconf
    exact h x y
      (hsub x (Or.inl rfl))
      (hsub y (Or.inr rfl))
  · intro h x y hx hy
    apply Classical.byContradiction
    intro hconf
    exact h x y hconf (by
      intro z hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy)

/--
TOTAL FORBIDDEN-BASIS LAW.
Once a complete action-obstruction basis is known, unified sufficiency is
completely determined by two negative ingredients:
  1. higher-order action obstructions from the basis;
  2. pairwise future conflicts.
-/
theorem sufficient_iff_avoids_actionBasis_and_futurePairs
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    (Basis : (WSet World) → Prop)
    (hBasis : ObstructionBasis good C Basis)
    (B : WSet World) :
    Sufficient good C futureEq B ↔
      (∀ O, Basis O → ¬ Subset O B) ∧
      (∀ x y, FutureConflict futureEq x y →
        ¬ Subset (PairSet x y) B) := by
  unfold Sufficient
  rw [
    actionable_iff_avoids_obstructionBasis good C Basis hBasis B,
    futureCoherent_iff_avoids_conflictPairs futureEq B
  ]
  simp [Contains]

/--
If two systems have the same action obstruction basis and the same future
conflict relation, then they have exactly the same unified sufficiency
judgement on every ambiguity set.
-/
theorem same_negative_signature_same_sufficiency
    {World : Type u}
    {Action₁ : Type v} {Action₂ : Type w}
    (good₁ : World → Action₁ → Prop)
    (good₂ : World → Action₂ → Prop)
    (C₁ : CapSet Action₁)
    (C₂ : CapSet Action₂)
    (futureEq₁ futureEq₂ : World → World → Prop)
    (Basis : (WSet World) → Prop)
    (h₁ : ObstructionBasis good₁ C₁ Basis)
    (h₂ : ObstructionBasis good₂ C₂ Basis)
    (hFuture :
      ∀ x y, FutureConflict futureEq₁ x y ↔
             FutureConflict futureEq₂ x y) :
    ∀ B,
      Sufficient good₁ C₁ futureEq₁ B ↔
      Sufficient good₂ C₂ futureEq₂ B := by
  intro B
  rw [
    sufficient_iff_avoids_actionBasis_and_futurePairs
      good₁ C₁ futureEq₁ Basis h₁ B,
    sufficient_iff_avoids_actionBasis_and_futurePairs
      good₂ C₂ futureEq₂ Basis h₂ B
  ]
  constructor
  · rintro ⟨ha, hf⟩
    exact ⟨ha, fun x y hconf => hf x y ((hFuture x y).mpr hconf)⟩
  · rintro ⟨ha, hf⟩
    exact ⟨ha, fun x y hconf => hf x y ((hFuture x y).mp hconf)⟩


/-! ## Contract-capability masking -/

def MaskedByFuture
    {World : Type u}
    (futureEq : World → World → Prop)
    (O : WSet World) : Prop :=
  ∃ x y,
    FutureConflict futureEq x y ∧
    Subset (PairSet x y) O

def RelevantActionBasis
    {World : Type u}
    (futureEq : World → World → Prop)
    (Basis : (WSet World) → Prop)
    (O : WSet World) : Prop :=
  Basis O ∧ ¬ MaskedByFuture futureEq O

/--
MASKING LAW.
An action obstruction containing a future-conflict pair can never be the first
effective forbidden reason for a sufficient ambiguity: every ambiguity
containing that obstruction is already future-incoherent.
-/
theorem masked_action_obstruction_forces_future_failure
    {World : Type u}
    (futureEq : World → World → Prop)
    (O B : WSet World)
    (hmask : MaskedByFuture futureEq O)
    (hOB : Subset O B) :
    ¬ FutureCoherent futureEq B := by
  obtain ⟨x, y, hconf, hpairO⟩ := hmask
  intro hfuture
  apply hconf
  exact hfuture x y
    (hOB x (hpairO x (Or.inl rfl)))
    (hOB y (hpairO y (Or.inr rfl)))

/--
PRUNED TOTAL BASIS LAW.
In unified sufficiency, every action-basis obstruction masked by a future
conflict pair is redundant. It can be removed from the action basis without
changing the sufficiency judgement.
-/
theorem sufficient_iff_avoids_relevantActionBasis_and_futurePairs
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (futureEq : World → World → Prop)
    (Basis : (WSet World) → Prop)
    (hBasis : ObstructionBasis good C Basis)
    (B : WSet World) :
    Sufficient good C futureEq B ↔
      (∀ O, RelevantActionBasis futureEq Basis O → ¬ Subset O B) ∧
      (∀ x y, FutureConflict futureEq x y →
        ¬ Subset (PairSet x y) B) := by
  constructor
  · intro hs
    have hfull :=
      (sufficient_iff_avoids_actionBasis_and_futurePairs
        good C futureEq Basis hBasis B).mp hs
    constructor
    · intro O hrel
      exact hfull.1 O hrel.1
    · exact hfull.2
  · rintro ⟨hrelevant, hfuture⟩
    apply (sufficient_iff_avoids_actionBasis_and_futurePairs
      good C futureEq Basis hBasis B).mpr
    constructor
    · intro O hO hOB
      by_cases hmask : MaskedByFuture futureEq O
      · obtain ⟨x, y, hconf, hpairO⟩ := hmask
        exact hfuture x y hconf (fun z hz => hOB z (hpairO z hz))
      · exact hrelevant O ⟨hO, hmask⟩ hOB
    · exact hfuture

/--
Tightening the future contract (adding conflict pairs) can only mask more
action obstructions: every action obstruction still relevant under the
stricter contract was already relevant under the looser one.
-/
theorem relevantActionBasis_antitone_under_future_conflicts
    {World : Type u}
    (futureEqLoose futureEqStrict : World → World → Prop)
    (Basis : (WSet World) → Prop)
    (hconf :
      ∀ x y,
        FutureConflict futureEqLoose x y →
        FutureConflict futureEqStrict x y) :
    ∀ O,
      RelevantActionBasis futureEqStrict Basis O →
      RelevantActionBasis futureEqLoose Basis O := by
  intro O hrel
  constructor
  · exact hrel.1
  · intro hmaskLoose
    obtain ⟨x, y, hLoose, hpair⟩ := hmaskLoose
    exact hrel.2 ⟨x, y, hconf x y hLoose, hpair⟩


/-! ## Theory-space identification kernel -/

abbrev Theory (World : Type u) := WSet World → Prop

def ConsistentWith
    {World : Type u}
    (T : Theory World)
    (q : WSet World)
    (answer : Bool) : Prop :=
  match answer with
  | true => T q
  | false => ¬ T q

noncomputable def AnswerOf
    {World : Type u}
    (T : Theory World)
    (q : WSet World) : Bool := by
  classical
  exact if T q then true else false

def VersionSpace
    {World : Type u} {Hyp : Type v}
    (sem : Hyp → Theory World)
    (Obs : List (WSet World × Bool))
    (h : Hyp) : Prop :=
  ∀ qa ∈ Obs, ConsistentWith (sem h) qa.1 qa.2

theorem answerOf_consistent
    {World : Type u}
    (T : Theory World)
    (q : WSet World) :
    ConsistentWith T q (AnswerOf T q) := by
  classical
  unfold AnswerOf
  by_cases h : T q
  · simp [h, ConsistentWith]
  · simp [h, ConsistentWith]

theorem trueTheory_survives_observation
    {World : Type u} {Hyp : Type v}
    (sem : Hyp → Theory World)
    (truth : Hyp)
    (Obs : List (WSet World × Bool))
    (htruth : VersionSpace sem Obs truth)
    (q : WSet World) :
    VersionSpace sem
      (Obs ++ [(q, AnswerOf (sem truth) q)]) truth := by
  intro qa hmem
  simp only [List.mem_append, List.mem_singleton] at hmem
  cases hmem with
  | inl hold => exact htruth qa hold
  | inr hnew =>
      subst qa
      exact answerOf_consistent (sem truth) q

theorem versionSpace_antitone_under_more_observations
    {World : Type u} {Hyp : Type v}
    (sem : Hyp → Theory World)
    (Obs More : List (WSet World × Bool))
    (h : Hyp)
    (hmore : VersionSpace sem (Obs ++ More) h) :
    VersionSpace sem Obs h := by
  intro qa hqa
  exact hmore qa (by simp [hqa])

def Separates
    {World : Type u}
    (T₁ T₂ : Theory World)
    (q : WSet World) : Prop :=
  (T₁ q ∧ ¬ T₂ q) ∨ (¬ T₁ q ∧ T₂ q)

theorem separating_query_eliminates_competitor
    {World : Type u}
    (Ttruth Tother : Theory World)
    (q : WSet World)
    (hsep : Separates Ttruth Tother q) :
    ¬ ConsistentWith Tother q (AnswerOf Ttruth q) := by
  classical
  rcases hsep with hpos | hneg
  · have ht : Ttruth q := hpos.1
    have hno : ¬ Tother q := hpos.2
    simp [AnswerOf, ht, ConsistentWith, hno]
  · have ht : ¬ Ttruth q := hneg.1
    have hyes : Tother q := hneg.2
    simp [AnswerOf, ht, ConsistentWith, hyes]

theorem nonextensional_theories_have_separating_query
    {World : Type u}
    (T₁ T₂ : Theory World)
    (hne : ¬ ∀ q, T₁ q ↔ T₂ q) :
    ∃ q, Separates T₁ T₂ q := by
  classical
  by_cases hsep : ∃ q, Separates T₁ T₂ q
  · exact hsep
  · exfalso
    apply hne
    intro q
    by_cases h1 : T₁ q
    · by_cases h2 : T₂ q
      · exact ⟨fun _ => h2, fun _ => h1⟩
      · exact False.elim (hsep ⟨q, Or.inl ⟨h1, h2⟩⟩)
    · by_cases h2 : T₂ q
      · exact False.elim (hsep ⟨q, Or.inr ⟨h1, h2⟩⟩)
      · constructor
        · intro hT1
          exact False.elim (h1 hT1)
        · intro hT2
          exact False.elim (h2 hT2)

theorem exact_query_can_kill_any_wrong_theory
    {World : Type u}
    (Ttruth Tother : Theory World)
    (hne : ¬ ∀ q, Ttruth q ↔ Tother q) :
    ∃ q,
      ConsistentWith Ttruth q (AnswerOf Ttruth q) ∧
      ¬ ConsistentWith Tother q (AnswerOf Ttruth q) := by
  obtain ⟨q, hsep⟩ :=
    nonextensional_theories_have_separating_query Ttruth Tother hne
  exact ⟨q,
    answerOf_consistent Ttruth q,
    separating_query_eliminates_competitor Ttruth Tother q hsep⟩

/-! ## Self-similar refinement on theory space -/

def TheoryFiber
    {World : Type u} {Hyp : Type v}
    (sem : Hyp → Theory World)
    (q : WSet World)
    (answer : Bool)
    (H : Hyp → Prop) : Hyp → Prop :=
  fun h => H h ∧ ConsistentWith (sem h) q answer

/--
A theory query refines the current hypothesis set by intersection with one
answer fiber, exactly mirroring ordinary probe refinement on world sets.
-/
theorem theoryFiber_downward
    {World : Type u} {Hyp : Type v}
    (sem : Hyp → Theory World)
    (q : WSet World)
    (answer : Bool)
    (H : Hyp → Prop) :
    ∀ h, TheoryFiber sem q answer H h → H h := by
  intro h hh
  exact hh.1

/--
The true hypothesis always remains inside the answer fiber generated by its own
response.
-/
theorem truth_remains_in_theoryFiber
    {World : Type u} {Hyp : Type v}
    (sem : Hyp → Theory World)
    (truth : Hyp)
    (H : Hyp → Prop)
    (hH : H truth)
    (q : WSet World) :
    TheoryFiber sem q (AnswerOf (sem truth) q) H truth := by
  exact ⟨hH, answerOf_consistent (sem truth) q⟩

/--
Any extensionally wrong hypothesis can be excluded by one theory-space probe
while preserving the truth.
-/
theorem wrong_hypothesis_can_be_cut_from_theorySpace
    {World : Type u} {Hyp : Type v}
    (sem : Hyp → Theory World)
    (truth wrong : Hyp)
    (H : Hyp → Prop)
    (htruth : H truth)
    (hwrong : H wrong)
    (hne : ¬ ∀ q, sem truth q ↔ sem wrong q) :
    ∃ q,
      TheoryFiber sem q (AnswerOf (sem truth) q) H truth ∧
      ¬ TheoryFiber sem q (AnswerOf (sem truth) q) H wrong := by
  obtain ⟨q, htrue, hkill⟩ :=
    exact_query_can_kill_any_wrong_theory (sem truth) (sem wrong) hne
  refine ⟨q, ?_, ?_⟩
  · exact ⟨htruth, htrue⟩
  · intro h
    exact hkill h.2


/-! ## Meta-world collapse: flattening world and theory uncertainty -/

def MetaGood
    {Hyp : Type v} {World : Type u} {Action : Type w}
    (good : Hyp → World → Action → Prop) :
    (Hyp × World) → Action → Prop :=
  fun hw a => good hw.1 hw.2 a

def MetaAmbiguity
    {Hyp : Type v} {World : Type u}
    (H : Hyp → Prop)
    (B : WSet World) :
    WSet (Hyp × World) :=
  fun hw => H hw.1 ∧ B hw.2

def RobustActionable
    {Hyp : Type v} {World : Type u} {Action : Type w}
    (good : Hyp → World → Action → Prop)
    (C : CapSet Action)
    (H : Hyp → Prop)
    (B : WSet World) : Prop :=
  ∃ a, C a ∧
    ∀ h, H h →
      ∀ x, B x → good h x a

/--
META-WORLD ACTIONABILITY COLLAPSE.
Robust actionability under simultaneous uncertainty over theories H and worlds
B is exactly ordinary INSACERMO actionability on the product ambiguity H × B.
-/
theorem robustActionable_iff_metaActionable
    {Hyp : Type v} {World : Type u} {Action : Type w}
    (good : Hyp → World → Action → Prop)
    (C : CapSet Action)
    (H : Hyp → Prop)
    (B : WSet World) :
    RobustActionable good C H B ↔
      Actionable (MetaGood good) C (MetaAmbiguity H B) := by
  constructor
  · rintro ⟨a, haC, hgood⟩
    refine ⟨a, haC, ?_⟩
    intro hw hhw
    exact hgood hw.1 hhw.1 hw.2 hhw.2
  · rintro ⟨a, haC, hgood⟩
    refine ⟨a, haC, ?_⟩
    intro h hh x hx
    exact hgood (h, x) ⟨hh, hx⟩

def RobustFutureCoherent
    {Hyp : Type v} {World : Type u}
    (futureEq : Hyp → World → World → Prop)
    (H : Hyp → Prop)
    (B : WSet World) : Prop :=
  ∀ h, H h →
    ∀ x y, B x → B y → futureEq h x y

def MetaFutureEq
    {Hyp : Type v} {World : Type u}
    (futureEq : Hyp → World → World → Prop)
    (p q : Hyp × World) : Prop :=
  p.1 = q.1 → futureEq p.1 p.2 q.2

/--
META-WORLD FUTURE COLLAPSE.
Robust future coherence across all candidate theories is ordinary future
coherence on the product meta-world, with cross-theory pairs unconstrained and
same-theory pairs checked against that theory's future relation.
-/
theorem robustFutureCoherent_iff_metaFutureCoherent
    {Hyp : Type v} {World : Type u}
    (futureEq : Hyp → World → World → Prop)
    (H : Hyp → Prop)
    (B : WSet World) :
    RobustFutureCoherent futureEq H B ↔
      FutureCoherent (MetaFutureEq futureEq) (MetaAmbiguity H B) := by
  constructor
  · intro hrob p q hp hq
    intro hpq
    cases p with
    | mk h x =>
      cases q with
      | mk k y =>
        simp only at hpq
        subst k
        exact hrob h hp.1 x y hp.2 hq.2
  · intro hmeta h hh x y hx hy
    have hs := hmeta (h, x) (h, y) ⟨hh, hx⟩ ⟨hh, hy⟩
    exact hs rfl

def RobustSufficient
    {Hyp : Type v} {World : Type u} {Action : Type w}
    (good : Hyp → World → Action → Prop)
    (C : CapSet Action)
    (futureEq : Hyp → World → World → Prop)
    (H : Hyp → Prop)
    (B : WSet World) : Prop :=
  RobustActionable good C H B ∧
  RobustFutureCoherent futureEq H B

/--
HIERARCHY FLATTENING THEOREM.
Simultaneous uncertainty about which theory is true and which world is true
requires no new decision semantics: it is exactly the existing INSACERMO
sufficiency predicate on the product space Hyp × World.
-/
theorem robustSufficient_iff_metaSufficient
    {Hyp : Type v} {World : Type u} {Action : Type w}
    (good : Hyp → World → Action → Prop)
    (C : CapSet Action)
    (futureEq : Hyp → World → World → Prop)
    (H : Hyp → Prop)
    (B : WSet World) :
    RobustSufficient good C futureEq H B ↔
      Sufficient
        (MetaGood good) C
        (MetaFutureEq futureEq)
        (MetaAmbiguity H B) := by
  unfold RobustSufficient Sufficient
  rw [
    robustActionable_iff_metaActionable good C H B,
    robustFutureCoherent_iff_metaFutureCoherent futureEq H B
  ]

noncomputable def TheoryProbe
    {Hyp : Type v} {World : Type u}
    (sem : Hyp → Theory World)
    (q : WSet World) :
    (Hyp × World) → Bool :=
  fun hw => AnswerOf (sem hw.1) q

theorem answerOf_eq_iff_consistent
    {World : Type u}
    (T : Theory World)
    (q : WSet World)
    (answer : Bool) :
    AnswerOf T q = answer ↔ ConsistentWith T q answer := by
  classical
  cases answer <;> simp [AnswerOf, ConsistentWith] <;>
    by_cases h : T q <;> simp [h]

/--
THEORY PROBES ARE ORDINARY PROBES.
A query on candidate theories is exactly an ordinary probe fiber on the
meta-world product space: it refines the theory coordinate while preserving
the world coordinate.
-/
theorem theoryProbe_fiber_iff
    {Hyp : Type v} {World : Type u}
    (sem : Hyp → Theory World)
    (q : WSet World)
    (answer : Bool)
    (H : Hyp → Prop)
    (B : WSet World)
    (h : Hyp)
    (x : World) :
    Fiber (TheoryProbe sem q) (MetaAmbiguity H B) answer (h, x) ↔
      TheoryFiber sem q answer H h ∧ B x := by
  unfold Fiber MetaAmbiguity TheoryFiber TheoryProbe
  constructor
  · rintro ⟨⟨hh, hx⟩, hans⟩
    exact ⟨⟨hh, (answerOf_eq_iff_consistent (sem h) q answer).mp hans⟩, hx⟩
  · rintro ⟨⟨hh, hcons⟩, hx⟩
    exact ⟨⟨hh, hx⟩,
      (answerOf_eq_iff_consistent (sem h) q answer).mpr hcons⟩


/-! ## Theory decision quotient -/

def TheoryEqOn
    {World : Type u}
    (Gamma : WSet World → Prop)
    (T₁ T₂ : Theory World) : Prop :=
  ∀ q, Gamma q → (T₁ q ↔ T₂ q)

theorem theoryEqOn_refl
    {World : Type u}
    (Gamma : WSet World → Prop)
    (T : Theory World) :
    TheoryEqOn Gamma T T := by
  intro q hq
  exact Iff.rfl

theorem theoryEqOn_symm
    {World : Type u}
    (Gamma : WSet World → Prop)
    {T₁ T₂ : Theory World}
    (h : TheoryEqOn Gamma T₁ T₂) :
    TheoryEqOn Gamma T₂ T₁ := by
  intro q hq
  exact (h q hq).symm

theorem theoryEqOn_trans
    {World : Type u}
    (Gamma : WSet World → Prop)
    {T₁ T₂ T₃ : Theory World}
    (h12 : TheoryEqOn Gamma T₁ T₂)
    (h23 : TheoryEqOn Gamma T₂ T₃) :
    TheoryEqOn Gamma T₁ T₃ := by
  intro q hq
  exact Iff.trans (h12 q hq) (h23 q hq)

def TheoryConsensusOn
    {World : Type u} {Hyp : Type v}
    (sem : Hyp → Theory World)
    (H : Hyp → Prop)
    (Gamma : WSet World → Prop) : Prop :=
  ∀ h₁ h₂, H h₁ → H h₂ →
    TheoryEqOn Gamma (sem h₁) (sem h₂)

/--
DECISION-QUOTIENT STOPPING LAW.
If all remaining hypotheses are equivalent on the future contract Gamma, then
for every future-relevant query q, all remaining hypotheses give the same
ACT/REFUSE answer. Exact theory identification is therefore unnecessary for
Gamma-relative decision.
-/
theorem theoryConsensusOn_forces_query_consensus
    {World : Type u} {Hyp : Type v}
    (sem : Hyp → Theory World)
    (H : Hyp → Prop)
    (Gamma : WSet World → Prop)
    (hcons : TheoryConsensusOn sem H Gamma)
    {q : WSet World}
    (hq : Gamma q) :
    ∀ h₁ h₂, H h₁ → H h₂ →
      (sem h₁ q ↔ sem h₂ q) := by
  intro h₁ h₂ hh₁ hh₂
  exact hcons h₁ h₂ hh₁ hh₂ q hq

/--
Any two version-space hypotheses in one Gamma-equivalence class are
indistinguishable for every contract-relevant decision query.
-/
theorem one_theoryQuotient_class_is_decision_complete
    {World : Type u} {Hyp : Type v}
    (sem : Hyp → Theory World)
    (H : Hyp → Prop)
    (Gamma : WSet World → Prop)
    (hclass : TheoryConsensusOn sem H Gamma) :
    ∀ q, Gamma q →
      ∀ h₁ h₂, H h₁ → H h₂ →
        (sem h₁ q ↔ sem h₂ q) := by
  intro q hq h₁ h₂ hh₁ hh₂
  exact theoryConsensusOn_forces_query_consensus
    sem H Gamma hclass hq h₁ h₂ hh₁ hh₂


/-! ## Information-capability exchange: semantic core -/

def PointwiseServiceable
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World) : Prop :=
  ∀ x, B x → ∃ a, C a ∧ good x a

def RealizedSafeProbe
    {World : Type u} {Action : Type v} {Obs : Type w}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World)
    (observe : World → Obs) : Prop :=
  ∀ o, (∃ x, Fiber observe B o x) →
    Actionable good C (Fiber observe B o)

/--
INFORMATION CANNOT CREATE CAPABILITY.
Any probe that makes every realized branch actionable implies that every
possible world was already individually serviceable by some available action.
-/
theorem realizedSafeProbe_implies_pointwiseServiceable
    {World : Type u} {Action : Type v} {Obs : Type w}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World)
    (observe : World → Obs)
    (h : RealizedSafeProbe good C B observe) :
    PointwiseServiceable good C B := by
  intro x hx
  have hreal : ∃ y, Fiber observe B (observe x) y :=
    ⟨x, ⟨hx, rfl⟩⟩
  obtain ⟨a, haC, hgood⟩ := h (observe x) hreal
  exact ⟨a, haC, hgood x ⟨hx, rfl⟩⟩

/--
FULL-INFORMATION RESCUE.
If every possible world is individually serviceable, then the identity probe
is sufficient on every realized branch.
-/
theorem pointwiseServiceable_implies_identityProbeSafe
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World)
    (h : PointwiseServiceable good C B) :
    RealizedSafeProbe good C B (fun x => x) := by
  intro o hreal
  obtain ⟨x, hxB, hxo⟩ := hreal
  simp only at hxo
  subst x
  obtain ⟨a, haC, hgood⟩ := h o hxB
  refine ⟨a, haC, ?_⟩
  intro y hy
  have hyo : y = o := hy.2
  subst y
  exact hgood

theorem identityProbeSafe_iff_pointwiseServiceable
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World) :
    RealizedSafeProbe good C B (fun x => x) ↔
      PointwiseServiceable good C B := by
  constructor
  · intro h
    exact realizedSafeProbe_implies_pointwiseServiceable
      good C B (fun x => x) h
  · intro h
    exact pointwiseServiceable_implies_identityProbeSafe good C B h

/--
A realized-safe observation is exactly a contingent action rule on its realized
fibers: each observation outcome can be assigned one available action that is
good throughout that fiber. Nonempty Action is only needed to define an
irrelevant value on unrealized outcomes.
-/
theorem realizedSafeProbe_iff_contingentAction
    {World : Type u} {Action : Type v} {Obs : Type w}
    [Nonempty Action]
    (good : World → Action → Prop)
    (C : CapSet Action)
    (B : WSet World)
    (observe : World → Obs) :
    RealizedSafeProbe good C B observe ↔
      ∃ choose : Obs → Action,
        ∀ o, (∃ x, Fiber observe B o x) →
          C (choose o) ∧
          ∀ x, Fiber observe B o x → good x (choose o) := by
  classical
  constructor
  · intro h
    let defaultAction : Action := Classical.choice inferInstance
    have hex :
        ∀ o, ∃ a,
          ((∃ x, Fiber observe B o x) →
            C a ∧ ∀ x, Fiber observe B o x → good x a) := by
      intro o
      by_cases hreal : ∃ x, Fiber observe B o x
      · obtain ⟨a, haC, hgood⟩ := h o hreal
        exact ⟨a, fun _ => ⟨haC, hgood⟩⟩
      · exact ⟨defaultAction, fun hr => False.elim (hreal hr)⟩
    let choose : Obs → Action := fun o => Classical.choose (hex o)
    refine ⟨choose, ?_⟩
    intro o hreal
    exact (Classical.choose_spec (hex o)) hreal
  · rintro ⟨choose, hchoose⟩
    intro o hreal
    obtain ⟨haC, hgood⟩ := hchoose o hreal
    exact ⟨choose o, haC, hgood⟩

/-! ## Exact repair-information residual law -/

def ResidualOutside
    {World : Type u}
    (B G : WSet World) : WSet World :=
  fun x => B x ∧ ¬ G x

/--
EXACT REPAIR RESIDUAL LAW.
After adding one capability b, the whole ambiguity B is individually
serviceable exactly when the part of B not served by b was already
individually serviceable by the old capabilities.

This is the correct non-linear compensation law: one repair may cover
arbitrarily many worlds at once; information cannot replace a genuinely
unserviceable residual world.
-/
theorem pointwiseServiceable_addCapability_iff_residual
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (b : Action)
    (B : WSet World) :
    PointwiseServiceable good (AddCapability C b) B ↔
      PointwiseServiceable good C
        (ResidualOutside B (GoodRegion good b)) := by
  constructor
  · intro h x hx
    obtain ⟨a, ha, hgood⟩ := h x hx.1
    cases ha with
    | inl haC =>
        exact ⟨a, haC, hgood⟩
    | inr hab =>
        subst a
        exact False.elim (hx.2 hgood)
  · intro h x hx
    by_cases hgb : GoodRegion good b x
    · exact ⟨b, Or.inr rfl, hgb⟩
    · obtain ⟨a, haC, hgood⟩ := h x ⟨hx, hgb⟩
      exact ⟨a, Or.inl haC, hgood⟩

/--
FULL-INFORMATION + ONE-REPAIR LAW.
With full information available, adding b rescues B exactly when every world
outside b's service region was already individually serviceable.
-/
theorem identityProbeSafe_afterRepair_iff_residualServiceable
    {World : Type u} {Action : Type v}
    (good : World → Action → Prop)
    (C : CapSet Action)
    (b : Action)
    (B : WSet World) :
    RealizedSafeProbe good (AddCapability C b) B (fun x => x) ↔
      PointwiseServiceable good C
        (ResidualOutside B (GoodRegion good b)) := by
  rw [identityProbeSafe_iff_pointwiseServiceable]
  exact pointwiseServiceable_addCapability_iff_residual good C b B


end Insacermo
