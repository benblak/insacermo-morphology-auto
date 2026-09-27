import InsacermoV13Kernel.InterfaceMessages

namespace InsacermoV13Kernel

universe uK uW uA uM uL uR uAL uAR uML uMR

/-- Context-dependent protocol semantics: each separator context may use its
    own encoder and decoder. -/
def IndexedCertifiedProtocol
    {K : Type uK} {World : Type uW} {Action : Type uA}
    (Message : Type uM)
    (available : Action → Prop)
    (admissible : K → World → Action → Prop) : Prop :=
  ∃ encode : K → World → Message,
    ∃ decode : K → Message → Action,
      (∀ k m, available (decode k m)) ∧
      ∀ k x, admissible k x (decode k (encode k x))

/-- Uniform message semantics: encoders may depend on context, but the decoder
    is shared across all contexts. Thus a message means the same certified
    action everywhere. -/
def UniformCertifiedProtocol
    {K : Type uK} {World : Type uW} {Action : Type uA}
    (Message : Type uM)
    (available : Action → Prop)
    (admissible : K → World → Action → Prop) : Prop :=
  ∃ encode : K → World → Message,
    ∃ decode : Message → Action,
      (∀ m, available (decode m)) ∧
      ∀ k x, admissible k x (decode (encode k x))

/-- Uniform semantics is a special case of indexed semantics. -/
theorem indexed_of_uniform
    {K : Type uK} {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    (h : UniformCertifiedProtocol Message available admissible) :
    IndexedCertifiedProtocol (Fin 1) available admissible := by
  rcases h with ⟨encode, decode, havail, hcert⟩
  exact
    ⟨encode,
     (fun _ m => decode m),
     (fun _ m => havail m),
     hcert⟩

/-- Lift a context-indexed admissibility predicate to a global state space. -/
def ContextLiftAdmissible
    {K : Type uK} {World : Type uW} {Action : Type uA}
    (admissible : K → World → Action → Prop) :
    K × World → Action → Prop :=
  fun x a => admissible x.1 x.2 a

/-- Context-erasure theorem.
    If message semantics is uniform across contexts, the exact separator
    context need not be transmitted: the message alone certifies an action. -/
theorem uniformProtocol_forgets_context
    {K : Type uK} {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    (h : UniformCertifiedProtocol Message available admissible) :
    CertifiedProtocol
      available
      (ContextLiftAdmissible admissible)
      Message := by
  rcases h with ⟨encode, decode, havail, hcert⟩
  refine
    ⟨(fun x => encode x.1 x.2),
     decode,
     havail,
     ?_⟩
  intro x
  exact hcert x.1 x.2

/-- With context-dependent decoder semantics, carrying the exact context is
    sufficient: the global message is (context, local-message). -/
theorem indexedProtocol_carries_context
    {K : Type uK} {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    (h : IndexedCertifiedProtocol Message available admissible) :
    CertifiedProtocol
      available
      (ContextLiftAdmissible admissible)
      (K × Message) := by
  rcases h with ⟨encode, decode, havail, hcert⟩
  refine
    ⟨(fun x => (x.1, encode x.1 x.2)),
     (fun m => decode m.1 m.2),
     ?_,
     ?_⟩
  · intro m
    exact havail m.1 m.2
  · intro x
    exact hcert x.1 x.2

/-- Two context-indexed component protocols compose through a shared separator
    by transmitting the exact context together with the pair of local messages. -/
theorem indexedSeparatorProtocols_compose
    {K : Type uK}
    {Left : Type uL} {Right : Type uR}
    {ActionL : Type uAL} {ActionR : Type uAR}
    {MessageL : Type uML} {MessageR : Type uMR}
    {availableL : ActionL → Prop}
    {availableR : ActionR → Prop}
    {admissibleL : K → Left → ActionL → Prop}
    {admissibleR : K → Right → ActionR → Prop}
    (hL : IndexedCertifiedProtocol MessageL availableL admissibleL)
    (hR : IndexedCertifiedProtocol MessageR availableR admissibleR) :
    CertifiedProtocol
      (ProductAvailable availableL availableR)
      (SeparatorAdmissible admissibleL admissibleR)
      (K × (MessageL × MessageR)) := by
  rcases hL with ⟨encodeL, decodeL, havailL, hcertL⟩
  rcases hR with ⟨encodeR, decodeR, havailR, hcertR⟩
  refine
    ⟨(fun x =>
        (x.1, (encodeL x.1 x.2.1, encodeR x.1 x.2.2))),
     (fun m =>
        (decodeL m.1 m.2.1, decodeR m.1 m.2.2)),
     ?_,
     ?_⟩
  · intro m
    exact
      ⟨havailL m.1 m.2.1,
       havailR m.1 m.2.2⟩
  · intro x
    exact
      ⟨hcertL x.1 x.2.1,
       hcertR x.1 x.2.2⟩

/-- Strong separator-erasure theorem.
    If each side has uniform message semantics across the shared context,
    the global system needs only the pair of local messages: the separator
    value itself disappears from communication. -/
theorem uniformSeparatorProtocols_forget_context
    {K : Type uK}
    {Left : Type uL} {Right : Type uR}
    {ActionL : Type uAL} {ActionR : Type uAR}
    {MessageL : Type uML} {MessageR : Type uMR}
    {availableL : ActionL → Prop}
    {availableR : ActionR → Prop}
    {admissibleL : K → Left → ActionL → Prop}
    {admissibleR : K → Right → ActionR → Prop}
    (hL : UniformCertifiedProtocol MessageL availableL admissibleL)
    (hR : UniformCertifiedProtocol MessageR availableR admissibleR) :
    CertifiedProtocol
      (ProductAvailable availableL availableR)
      (SeparatorAdmissible admissibleL admissibleR)
      (MessageL × MessageR) := by
  rcases hL with ⟨encodeL, decodeL, havailL, hcertL⟩
  rcases hR with ⟨encodeR, decodeR, havailR, hcertR⟩
  refine
    ⟨(fun x =>
        (encodeL x.1 x.2.1, encodeR x.1 x.2.2)),
     (fun m => (decodeL m.1, decodeR m.2)),
     ?_,
     ?_⟩
  · intro m
    exact ⟨havailL m.1, havailR m.2⟩
  · intro x
    exact
      ⟨hcertL x.1 x.2.1,
       hcertR x.1 x.2.2⟩

namespace ContextNecessityWitness

inductive Context
  | left
  | right

inductive Action
  | alpha
  | beta

open Context Action

def available : Action → Prop := fun _ => True

def admissible : Context → Unit → Action → Prop
  | left, _, alpha => True
  | left, _, beta => False
  | right, _, alpha => False
  | right, _, beta => True

def exactContextCode : Context × Unit → Fin 2
  | (left, _) => 0
  | (right, _) => 1

theorem exactContextCode_globalSafe :
    GlobalSafe exactContextCode
      available
      (ContextLiftAdmissible admissible) := by
  intro x
  cases x with
  | mk k u =>
      cases k with
      | left =>
          refine ⟨alpha, trivial, ?_⟩
          intro y hy
          cases y with
          | mk ky uy =>
              cases ky <;>
                simp [exactContextCode, ContextLiftAdmissible, admissible] at hy ⊢
      | right =>
          refine ⟨beta, trivial, ?_⟩
          intro y hy
          cases y with
          | mk ky uy =>
              cases ky <;>
                simp [exactContextCode, ContextLiftAdmissible, admissible] at hy ⊢

theorem two_messages_safe :
    SafeEncoding available (ContextLiftAdmissible admissible) 2 :=
  ⟨exactContextCode, exactContextCode_globalSafe⟩

theorem one_message_unsafe :
    ¬ SafeEncoding available (ContextLiftAdmissible admissible) 1 := by
  intro h
  rcases h with ⟨obs, hsafe⟩
  let xL : Context × Unit := (left, ())
  let xR : Context × Unit := (right, ())
  have halias : obs xR = obs xL := Subsingleton.elim _ _
  rcases hsafe xL with ⟨a, ha, hall⟩
  have hL :
      ContextLiftAdmissible admissible xL a :=
    hall rfl
  have hR :
      ContextLiftAdmissible admissible xR a :=
    hall halias
  cases a with
  | alpha =>
      exact hR
  | beta =>
      exact hL

theorem no_zero_messages :
    ¬ SafeEncoding available (ContextLiftAdmissible admissible) 0 := by
  intro h
  rcases h with ⟨obs, hsafe⟩
  exact Fin.elim0 (obs (left, ()))

theorem min_context_messages_two :
    IsMinSafeSymbols available (ContextLiftAdmissible admissible) 2 := by
  refine ⟨two_messages_safe, ?_⟩
  intro n hn
  cases n with
  | zero =>
      exact False.elim (no_zero_messages hn)
  | succ n =>
      cases n with
      | zero =>
          exact False.elim (one_message_unsafe hn)
      | succ k =>
          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))

/-- Each context separately needs only one local message. -/
def localEncode : Context → Unit → Fin 1 :=
  fun _ _ => 0

def localDecode : Context → Fin 1 → Action
  | left, _ => alpha
  | right, _ => beta

theorem indexed_one_local_message :
    IndexedCertifiedProtocol Message available admissible := by
  refine ⟨localEncode, localDecode, ?_, ?_⟩
  · intro k m
    trivial
  · intro k x
    cases k <;> trivial

/-- But one uniform message is impossible because its decoded action would
    need to work in both contexts. -/
theorem no_uniform_one_local_message :
    ¬ UniformCertifiedProtocol (Fin 1) available admissible := by
  rintro ⟨encode, decode, havail, hcert⟩
  have hsame :
      encode left () = encode right () :=
    Subsingleton.elim _ _
  have hL := hcert left ()
  have hR := hcert right ()
  have hdec :
      decode (encode left ()) = decode (encode right ()) := by
    rw [hsame]
  rw [← hdec] at hR
  cases hact : decode (encode left ()) with
  | alpha =>
      simpa [admissible, hact] using hR
  | beta =>
      simpa [admissible, hact] using hL

/-- Exact witness that separator context can carry irreducible future-relevant
    information: one local message per context suffices if context is carried,
    but one context-free message cannot suffice globally. -/
theorem context_can_be_irreducible :
    IndexedCertifiedProtocol (Fin 1) available admissible ∧
    ¬ UniformCertifiedProtocol (Fin 1) available admissible ∧
    IsMinSafeSymbols available (ContextLiftAdmissible admissible) 2 := by
  exact
    ⟨indexed_one_local_message,
     no_uniform_one_local_message,
     min_context_messages_two⟩

end ContextNecessityWitness

end InsacermoV13Kernel
