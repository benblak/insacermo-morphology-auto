import InsacermoV13Kernel.FamilySeparatorDecomposition

namespace InsacermoV13Kernel

universe u v w

/-- The complete actionability signature of a world/interface state:
    which actions satisfy the declared contract there. -/
def ActionSignature {World : Type u} {Action : Type v}
    (admissible : World → Action → Prop) (x : World) :
    Action → Prop :=
  fun a => admissible x a

/-- Two interface states have the same complete actionability signature. -/
def SignatureEquivalent {World : Type u} {Action : Type v}
    (admissible : World → Action → Prop) (x y : World) : Prop :=
  ∀ a, admissible x a ↔ admissible y a

theorem signatureEquivalent_refl
    {World : Type u} {Action : Type v}
    {admissible : World → Action → Prop} {x : World} :
    SignatureEquivalent admissible x x := by
  intro a
  exact Iff.rfl

theorem signatureEquivalent_symm
    {World : Type u} {Action : Type v}
    {admissible : World → Action → Prop} {x y : World}
    (h : SignatureEquivalent admissible x y) :
    SignatureEquivalent admissible y x := by
  intro a
  exact (h a).symm

theorem signatureEquivalent_trans
    {World : Type u} {Action : Type v}
    {admissible : World → Action → Prop} {x y z : World}
    (hxy : SignatureEquivalent admissible x y)
    (hyz : SignatureEquivalent admissible y z) :
    SignatureEquivalent admissible x z := by
  intro a
  exact (hxy a).trans (hyz a)

/-- Pointwise feasibility ignores compression: every state individually has
    at least one currently available admissible action. -/
def PointwiseSafe {World : Type u} {Action : Type v}
    (available : Action → Prop)
    (admissible : World → Action → Prop) : Prop :=
  ∀ x, ∃ a, available a ∧ admissible x a

/-- The canonical complete-signature observation. -/
def SignatureObs {World : Type u} {Action : Type v}
    (admissible : World → Action → Prop) :
    World → (Action → Prop) :=
  fun x => ActionSignature admissible x

/-- Full actionability signatures are always sufficient:
    if every state individually has an available admissible action, then
    grouping exactly equal signatures is globally safe. Conversely, every
    globally safe signature observation implies pointwise feasibility. -/
theorem globalSafe_signatureObs_iff_pointwiseSafe
    {World : Type u} {Action : Type v}
    {available : Action → Prop}
    {admissible : World → Action → Prop} :
    GlobalSafe (SignatureObs admissible) available admissible
      ↔ PointwiseSafe available admissible := by
  constructor
  · intro hsafe x
    rcases hsafe x with ⟨a, ha, hall⟩
    exact ⟨a, ha, hall rfl⟩
  · intro hpoint x
    rcases hpoint x with ⟨a, ha, hax⟩
    refine ⟨a, ha, ?_⟩
    intro y hy
    have hprop : admissible y a = admissible x a := by
      simpa [SignatureObs, ActionSignature] using congrArg (fun f => f a) hy
    rw [hprop]
    exact hax

/-- Any observation that only merges equal complete signatures is safe whenever
    the underlying interface is pointwise feasible. -/
theorem globalSafe_of_signature_respecting
    {World : Type u} {Obs : Type v} {Action : Type w}
    {obs : World → Obs}
    {available : Action → Prop}
    {admissible : World → Action → Prop}
    (hsig : ∀ ⦃x y : World⦄, obs y = obs x →
      SignatureEquivalent admissible y x)
    (hpoint : PointwiseSafe available admissible) :
    GlobalSafe obs available admissible := by
  intro x
  rcases hpoint x with ⟨a, ha, hax⟩
  refine ⟨a, ha, ?_⟩
  intro y hy
  exact (hsig hy a).2 hax

/-- A three-state witness exposing the non-canonicity of minimum safe
    interface compression. -/
inductive InterfaceWitnessWorld where
  | left
  | middle
  | right

inductive InterfaceWitnessAction where
  | alpha
  | beta

open InterfaceWitnessWorld InterfaceWitnessAction

def interfaceWitnessAvailable : InterfaceWitnessAction → Prop :=
  fun _ => True

def interfaceWitnessAdmissible :
    InterfaceWitnessWorld → InterfaceWitnessAction → Prop
  | left, alpha => True
  | left, beta => False
  | middle, alpha => True
  | middle, beta => True
  | right, alpha => False
  | right, beta => True

/-- Safe two-message encoding using the alpha-side overlap. -/
def interfaceCodeA : InterfaceWitnessWorld → Fin 2
  | left => 0
  | middle => 0
  | right => 1

/-- Safe two-message encoding using the beta-side overlap. -/
def interfaceCodeB : InterfaceWitnessWorld → Fin 2
  | left => 0
  | middle => 1
  | right => 1

theorem interfaceCodeA_globalSafe :
    GlobalSafe interfaceCodeA
      interfaceWitnessAvailable interfaceWitnessAdmissible := by
  intro x
  cases x with
  | left =>
      refine ⟨alpha, trivial, ?_⟩
      intro y hy
      cases y <;> simp [interfaceCodeA, interfaceWitnessAdmissible] at hy ⊢
  | middle =>
      refine ⟨alpha, trivial, ?_⟩
      intro y hy
      cases y <;> simp [interfaceCodeA, interfaceWitnessAdmissible] at hy ⊢
  | right =>
      refine ⟨beta, trivial, ?_⟩
      intro y hy
      cases y <;> simp [interfaceCodeA, interfaceWitnessAdmissible] at hy ⊢

theorem interfaceCodeB_globalSafe :
    GlobalSafe interfaceCodeB
      interfaceWitnessAvailable interfaceWitnessAdmissible := by
  intro x
  cases x with
  | left =>
      refine ⟨alpha, trivial, ?_⟩
      intro y hy
      cases y <;> simp [interfaceCodeB, interfaceWitnessAdmissible] at hy ⊢
  | middle =>
      refine ⟨beta, trivial, ?_⟩
      intro y hy
      cases y <;> simp [interfaceCodeB, interfaceWitnessAdmissible] at hy ⊢
  | right =>
      refine ⟨beta, trivial, ?_⟩
      intro y hy
      cases y <;> simp [interfaceCodeB, interfaceWitnessAdmissible] at hy ⊢

theorem interfaceCodeA_safeEncoding :
    SafeEncoding interfaceWitnessAvailable interfaceWitnessAdmissible 2 :=
  ⟨interfaceCodeA, interfaceCodeA_globalSafe⟩

theorem interfaceCodeB_safeEncoding :
    SafeEncoding interfaceWitnessAvailable interfaceWitnessAdmissible 2 :=
  ⟨interfaceCodeB, interfaceCodeB_globalSafe⟩

/-- One message cannot be safe: left and right require incompatible actions. -/
theorem interfaceWitness_no_safeEncoding_one :
    ¬ SafeEncoding interfaceWitnessAvailable interfaceWitnessAdmissible 1 := by
  intro henc
  rcases henc with ⟨obs, hsafe⟩
  have halias : obs right = obs left := Subsingleton.elim _ _
  have hnot :
      ¬ FiberSafe obs interfaceWitnessAvailable
        interfaceWitnessAdmissible left := by
    apply not_fiberSafe_of_alias_conflict
      (x := left) (y := right) halias
    intro a ha
    cases a <;> simp [interfaceWitnessAdmissible]
  exact hnot (hsafe left)

/-- Two messages are the exact minimum for the witness. -/
theorem interfaceWitness_minSafeSymbols_two :
    IsMinSafeSymbols interfaceWitnessAvailable
      interfaceWitnessAdmissible 2 := by
  constructor
  · exact interfaceCodeA_safeEncoding
  · intro n henc
    cases n with
    | zero =>
        exfalso
        rcases henc with ⟨obs, hsafe⟩
        exact Fin.elim0 (obs left)
    | succ n =>
        cases n with
        | zero =>
            exfalso
            exact interfaceWitness_no_safeEncoding_one henc
        | succ k =>
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))

/-- The complete actionability signature distinguishes all three states. -/
theorem interfaceWitness_three_distinct_signatures :
    ActionSignature interfaceWitnessAdmissible left ≠
        ActionSignature interfaceWitnessAdmissible middle ∧
    ActionSignature interfaceWitnessAdmissible middle ≠
        ActionSignature interfaceWitnessAdmissible right ∧
    ActionSignature interfaceWitnessAdmissible left ≠
        ActionSignature interfaceWitnessAdmissible right := by
  constructor
  · intro h
    have hp := congrArg (fun f => f beta) h
    simp [ActionSignature, interfaceWitnessAdmissible] at hp
  constructor
  · intro h
    have hp := congrArg (fun f => f alpha) h
    simp [ActionSignature, interfaceWitnessAdmissible] at hp
  · intro h
    have hp := congrArg (fun f => f alpha) h
    simp [ActionSignature, interfaceWitnessAdmissible] at hp

/-- Therefore the complete-signature quotient can strictly over-separate:
    it has three distinct signatures while two messages are exactly sufficient. -/
theorem complete_signature_not_minimal_in_general :
    IsMinSafeSymbols interfaceWitnessAvailable
      interfaceWitnessAdmissible 2 ∧
    ActionSignature interfaceWitnessAdmissible left ≠
        ActionSignature interfaceWitnessAdmissible middle ∧
    ActionSignature interfaceWitnessAdmissible middle ≠
        ActionSignature interfaceWitnessAdmissible right ∧
    ActionSignature interfaceWitnessAdmissible left ≠
        ActionSignature interfaceWitnessAdmissible right := by
  exact
    ⟨interfaceWitness_minSafeSymbols_two,
     interfaceWitness_three_distinct_signatures.1,
     interfaceWitness_three_distinct_signatures.2.1,
     interfaceWitness_three_distinct_signatures.2.2⟩

/-- The two optimal two-message encodings are incomparable by refinement. -/
theorem interface_optimal_encodings_incomparable :
    ¬ Refines interfaceCodeA interfaceCodeB ∧
    ¬ Refines interfaceCodeB interfaceCodeA := by
  constructor
  · intro h
    have hbad : interfaceCodeA middle = interfaceCodeA right :=
      h (x := middle) (y := right) rfl
    simp [interfaceCodeA] at hbad
  · intro h
    have hbad : interfaceCodeB left = interfaceCodeB middle :=
      h (x := left) (y := middle) rfl
    simp [interfaceCodeB] at hbad

/-- Strong non-canonicity: the two optimal encodings have no globally-safe
    common coarsening. Any common coarsening must merge left with right, which
    destroys actionability. -/
theorem no_safe_common_coarsening_of_optimal_encodings :
    ¬ ∃ (Obs : Type) (obs : InterfaceWitnessWorld → Obs),
      GlobalSafe obs interfaceWitnessAvailable interfaceWitnessAdmissible ∧
      Refines obs interfaceCodeA ∧
      Refines obs interfaceCodeB := by
  rintro ⟨Obs, obs, hsafe, hA, hB⟩
  have hLM : obs left = obs middle :=
    hA (x := left) (y := middle) rfl
  have hMR : obs middle = obs right :=
    hB (x := middle) (y := right) rfl
  have halias : obs right = obs left :=
    (hLM.trans hMR).symm
  have hnot :
      ¬ FiberSafe obs interfaceWitnessAvailable
        interfaceWitnessAdmissible left := by
    apply not_fiberSafe_of_alias_conflict
      (x := left) (y := right) halias
    intro a ha
    cases a <;> simp [interfaceWitnessAdmissible]
  exact hnot (hsafe left)

/-- Existing INSACERMO cover equivalence, restated as the correct interface
    message object: n safe messages are equivalent to n available action
    regions covering the interface state space. -/
theorem interfaceMessages_iff_actionCover
    {World : Type u} {Action : Type v} [Nonempty World]
    {available : Action → Prop}
    {admissible : World → Action → Prop}
    {n : Nat} :
    SafeEncoding available admissible n ↔
      ActionCover available admissible n :=
  safeEncoding_iff_actionCover

end InsacermoV13Kernel
