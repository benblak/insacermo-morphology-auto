import InsacermoV13Kernel.InterfaceQuotient

namespace InsacermoV13Kernel

universe u v w u₁ u₂ v₁ v₂ w₁ w₂

/-- A certified interface protocol consists of an encoder from interface states
    to messages and a decoder from each message to one currently available
    action. Every state must satisfy the action decoded from its own message. -/
def CertifiedProtocol
    {World : Type u} {Action : Type v}
    (available : Action → Prop)
    (admissible : World → Action → Prop)
    (Message : Type w) : Prop :=
  ∃ encode : World → Message,
    ∃ decode : Message → Action,
      (∀ m, available (decode m)) ∧
      ∀ x, admissible x (decode (encode x))

/-- A certified protocol directly induces a globally safe observation:
    equal messages force the same certified decoded action. -/
theorem certifiedProtocol_globalSafe
    {World : Type u} {Action : Type v} {Message : Type w}
    {available : Action → Prop}
    {admissible : World → Action → Prop}
    (h : CertifiedProtocol available admissible Message) :
    ∃ obs : World → Message, GlobalSafe obs available admissible := by
  rcases h with ⟨encode, decode, havail, hcert⟩
  refine ⟨encode, ?_⟩
  intro x
  refine ⟨decode (encode x), havail (encode x), ?_⟩
  intro y hy
  simpa [hy] using hcert y

/-- Conversely, on a nonempty world space, any globally safe observation can
    be equipped with one certified decoder action per message. Unused messages
    receive a harmless available action taken from one realized fiber. -/
theorem certifiedProtocol_of_globalSafe
    {World : Type u} {Action : Type v} {Message : Type w}
    [Nonempty World]
    {obs : World → Message}
    {available : Action → Prop}
    {admissible : World → Action → Prop}
    (hsafe : GlobalSafe obs available admissible) :
    CertifiedProtocol available admissible Message := by
  classical
  let x0 : World := Classical.choice (inferInstance : Nonempty World)
  rcases hsafe x0 with ⟨a0, ha0, h0⟩
  have hper :
      ∀ m : Message, ∃ a,
        available a ∧
        ∀ ⦃x : World⦄, obs x = m → admissible x a := by
    intro m
    by_cases hm : ∃ x : World, obs x = m
    · rcases hm with ⟨x, hx⟩
      rcases hsafe x with ⟨a, ha, hall⟩
      refine ⟨a, ha, ?_⟩
      intro y hy
      exact hall (hy.trans hx.symm)
    · refine ⟨a0, ha0, ?_⟩
      intro y hy
      exact False.elim (hm ⟨y, hy⟩)
  let decode : Message → Action :=
    fun m => Classical.choose (hper m)
  refine ⟨obs, decode, ?_, ?_⟩
  · intro m
    exact (Classical.choose_spec (hper m)).1
  · intro x
    exact (Classical.choose_spec (hper (obs x))).2 rfl

/-- Exact typed protocol equivalence: on nonempty worlds, a message type admits
    a certified protocol iff it admits a globally safe observation. -/
theorem certifiedProtocol_iff_exists_globalSafe
    {World : Type u} {Action : Type v} {Message : Type w}
    [Nonempty World]
    {available : Action → Prop}
    {admissible : World → Action → Prop} :
    CertifiedProtocol available admissible Message ↔
      ∃ obs : World → Message, GlobalSafe obs available admissible := by
  constructor
  · exact certifiedProtocol_globalSafe
  · rintro ⟨obs, hsafe⟩
    exact certifiedProtocol_of_globalSafe hsafe

/-- n certified interface messages. -/
def CertifiedMessages
    {World : Type u} {Action : Type v}
    (available : Action → Prop)
    (admissible : World → Action → Prop)
    (n : Nat) : Prop :=
  CertifiedProtocol available admissible (Fin n)

/-- Certified messages and action covers are exactly the same finite object:
    each message names one available action region, and every state is assigned
    to a message whose decoded action covers it. -/
theorem certifiedMessages_iff_actionCover
    {World : Type u} {Action : Type v}
    {available : Action → Prop}
    {admissible : World → Action → Prop}
    {n : Nat} :
    CertifiedMessages available admissible n ↔
      ActionCover available admissible n := by
  constructor
  · rintro ⟨encode, decode, havail, hcert⟩
    refine ⟨decode, havail, ?_⟩
    intro x
    exact ⟨encode x, hcert x⟩
  · rintro ⟨actions, havail, hcover⟩
    classical
    let encode : World → Fin n :=
      fun x => Classical.choose (hcover x)
    refine ⟨encode, actions, havail, ?_⟩
    intro x
    dsimp [encode]
    exact Classical.choose_spec (hcover x)

/-- On nonempty worlds, certified messages are exactly safe information
    symbols. This turns the abstract information budget into an executable
    encoder/decoder certificate. -/
theorem certifiedMessages_iff_safeEncoding
    {World : Type u} {Action : Type v}
    [Nonempty World]
    {available : Action → Prop}
    {admissible : World → Action → Prop}
    {n : Nat} :
    CertifiedMessages available admissible n ↔
      SafeEncoding available admissible n := by
  rw [certifiedMessages_iff_actionCover,
      ← safeEncoding_iff_actionCover]

/-- m is an exact minimum certified-message budget. -/
def IsMinCertifiedMessages
    {World : Type u} {Action : Type v}
    (available : Action → Prop)
    (admissible : World → Action → Prop)
    (m : Nat) : Prop :=
  CertifiedMessages available admissible m ∧
    ∀ n, CertifiedMessages available admissible n → m ≤ n

/-- Minimum certified-message count equals minimum action-cover count. -/
theorem isMinCertifiedMessages_iff_isMinActionCover
    {World : Type u} {Action : Type v}
    {available : Action → Prop}
    {admissible : World → Action → Prop}
    {m : Nat} :
    IsMinCertifiedMessages available admissible m ↔
      IsMinActionCover available admissible m := by
  constructor
  · intro h
    refine ⟨certifiedMessages_iff_actionCover.mp h.1, ?_⟩
    intro n hn
    exact h.2 n (certifiedMessages_iff_actionCover.mpr hn)
  · intro h
    refine ⟨certifiedMessages_iff_actionCover.mpr h.1, ?_⟩
    intro n hn
    exact h.2 n (certifiedMessages_iff_actionCover.mp hn)

/-- Exact information/message equality at the minimum level. -/
theorem isMinCertifiedMessages_iff_isMinSafeSymbols
    {World : Type u} {Action : Type v}
    [Nonempty World]
    {available : Action → Prop}
    {admissible : World → Action → Prop}
    {m : Nat} :
    IsMinCertifiedMessages available admissible m ↔
      IsMinSafeSymbols available admissible m := by
  rw [isMinCertifiedMessages_iff_isMinActionCover,
      ← isMinSafeSymbols_iff_isMinActionCover]

/-- Exact message/obstruction equality at the minimum level. -/
theorem isMinCertifiedMessages_iff_isMinObstructionColors
    {World : Type u} {Action : Type v}
    [Nonempty World]
    {available : Action → Prop}
    {admissible : World → Action → Prop}
    {m : Nat} :
    IsMinCertifiedMessages available admissible m ↔
      IsMinObstructionColors available admissible m := by
  rw [isMinCertifiedMessages_iff_isMinActionCover,
      isMinActionCover_iff_isMinObstructionColors]

/-- Capability expansion preserves every certified-message budget. -/
theorem certifiedMessages_of_capability_expansion
    {World : Type u} {Action : Type v}
    {available₁ available₂ : Action → Prop}
    {admissible : World → Action → Prop}
    {n : Nat}
    (hcap : ∀ ⦃a : Action⦄, available₁ a → available₂ a)
    (hmsg : CertifiedMessages available₁ admissible n) :
    CertifiedMessages available₂ admissible n := by
  rcases hmsg with ⟨encode, decode, havail, hcert⟩
  exact
    ⟨encode, decode,
     (fun m => hcap (havail m)),
     hcert⟩

/-- Contract weakening preserves every certified-message budget. -/
theorem certifiedMessages_of_contract_weakening
    {World : Type u} {Action : Type v}
    {available : Action → Prop}
    {strong weak : World → Action → Prop}
    {n : Nat}
    (hcontract : ∀ ⦃x : World⦄ ⦃a : Action⦄,
      strong x a → weak x a)
    (hmsg : CertifiedMessages available strong n) :
    CertifiedMessages available weak n := by
  rcases hmsg with ⟨encode, decode, havail, hcert⟩
  refine ⟨encode, decode, havail, ?_⟩
  intro x
  exact hcontract (hcert x)

/-- Certified protocols compose exactly on independent products. The global
    message is the pair of local messages and the global decoded action is the
    pair of local decoded actions. -/
theorem certifiedProtocol_product
    {World₁ : Type u₁} {World₂ : Type u₂}
    {Action₁ : Type v₁} {Action₂ : Type v₂}
    {Message₁ : Type w₁} {Message₂ : Type w₂}
    {available₁ : Action₁ → Prop}
    {available₂ : Action₂ → Prop}
    {admissible₁ : World₁ → Action₁ → Prop}
    {admissible₂ : World₂ → Action₂ → Prop}
    (h₁ : CertifiedProtocol available₁ admissible₁ Message₁)
    (h₂ : CertifiedProtocol available₂ admissible₂ Message₂) :
    CertifiedProtocol
      (ProductAvailable available₁ available₂)
      (ProductAdmissible admissible₁ admissible₂)
      (Message₁ × Message₂) := by
  rcases h₁ with ⟨encode₁, decode₁, havail₁, hcert₁⟩
  rcases h₂ with ⟨encode₂, decode₂, havail₂, hcert₂⟩
  refine
    ⟨(fun x => (encode₁ x.1, encode₂ x.2)),
     (fun m => (decode₁ m.1, decode₂ m.2)),
     ?_, ?_⟩
  · intro m
    exact ⟨havail₁ m.1, havail₂ m.2⟩
  · intro x
    exact ⟨hcert₁ x.1, hcert₂ x.2⟩

/-- The three-state non-canonicity witness has exact certified-message
    complexity two. -/
theorem interfaceWitness_minCertifiedMessages_two :
    IsMinCertifiedMessages interfaceWitnessAvailable
      interfaceWitnessAdmissible 2 := by
  letI : Nonempty InterfaceWitnessWorld := ⟨InterfaceWitnessWorld.left⟩
  exact
    isMinCertifiedMessages_iff_isMinSafeSymbols.mpr
      interfaceWitness_minSafeSymbols_two

end InsacermoV13Kernel
