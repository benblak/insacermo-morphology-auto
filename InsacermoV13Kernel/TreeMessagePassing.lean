import InsacermoV13Kernel.ParetoInterfaceFrontier

namespace InsacermoV13Kernel

universe uLW uPW uLA uPA uLM uPM

/-- Two-level distributed certified protocol.
    A leaf compresses its local world into a local message and decodes its own
    action locally. The parent sees only the leaf message plus its own world,
    emits an upstream message, and decodes its own action from that upstream
    message. Internal leaf information need not be sent further upward. -/
def TwoLevelDistributedProtocol
    {LeafWorld : Type uLW} {ParentWorld : Type uPW}
    {LeafAction : Type uLA} {ParentAction : Type uPA}
    (LeafMessage : Type uLM) (ParentMessage : Type uPM)
    (leafAvailable : LeafAction → Prop)
    (parentAvailable : ParentAction → Prop)
    (leafAdmissible : LeafWorld → LeafAction → Prop)
    (parentAdmissible : ParentWorld → LeafMessage → ParentAction → Prop) : Prop :=
  ∃ leafEncode : LeafWorld → LeafMessage,
    ∃ leafDecode : LeafMessage → LeafAction,
    ∃ parentEncode : ParentWorld → LeafMessage → ParentMessage,
    ∃ parentDecode : ParentMessage → ParentAction,
      (∀ lm, leafAvailable (leafDecode lm)) ∧
      (∀ pm, parentAvailable (parentDecode pm)) ∧
      (∀ lw, leafAdmissible lw (leafDecode (leafEncode lw))) ∧
      ∀ pw lw,
        parentAdmissible
          pw
          (leafEncode lw)
          (parentDecode (parentEncode pw (leafEncode lw)))

/-- Any certified leaf protocol and certified parent protocol over the parent's
    local world plus the child's message compose into a two-level distributed
    protocol. -/
theorem twoLevelDistributed_of_localProtocols
    {LeafWorld : Type uLW} {ParentWorld : Type uPW}
    {LeafAction : Type uLA} {ParentAction : Type uPA}
    {LeafMessage : Type uLM} {ParentMessage : Type uPM}
    {leafAvailable : LeafAction → Prop}
    {parentAvailable : ParentAction → Prop}
    {leafAdmissible : LeafWorld → LeafAction → Prop}
    {parentAdmissible : ParentWorld → LeafMessage → ParentAction → Prop}
    (hleaf :
      CertifiedProtocol
        leafAvailable leafAdmissible LeafMessage)
    (hparent :
      CertifiedProtocol
        parentAvailable
        (fun z : ParentWorld × LeafMessage =>
          parentAdmissible z.1 z.2)
        ParentMessage) :
    TwoLevelDistributedProtocol
      LeafMessage ParentMessage
      leafAvailable parentAvailable
      leafAdmissible parentAdmissible := by
  rcases hleaf with
    ⟨leafEncode, leafDecode, hLeafAvail, hLeafCert⟩
  rcases hparent with
    ⟨parentEncode, parentDecode, hParentAvail, hParentCert⟩
  refine
    ⟨leafEncode,
     leafDecode,
     (fun pw lm => parentEncode (pw, lm)),
     parentDecode,
     hLeafAvail,
     hParentAvail,
     hLeafCert,
     ?_⟩
  intro pw lw
  exact hParentCert (pw, leafEncode lw)

/-- Flattened availability for the pair of parent and leaf actions. -/
def TwoLevelAvailable
    {LeafAction : Type uLA} {ParentAction : Type uPA}
    (leafAvailable : LeafAction → Prop)
    (parentAvailable : ParentAction → Prop) :
    ParentAction × LeafAction → Prop :=
  fun a => parentAvailable a.1 ∧ leafAvailable a.2

/-- Flattened admissibility for a fixed child encoder. -/
def TwoLevelAdmissible
    {LeafWorld : Type uLW} {ParentWorld : Type uPW}
    {LeafAction : Type uLA} {ParentAction : Type uPA}
    {LeafMessage : Type uLM}
    (leafEncode : LeafWorld → LeafMessage)
    (leafAdmissible : LeafWorld → LeafAction → Prop)
    (parentAdmissible : ParentWorld → LeafMessage → ParentAction → Prop) :
    ParentWorld × LeafWorld → ParentAction × LeafAction → Prop :=
  fun x a =>
    parentAdmissible x.1 (leafEncode x.2) a.1 ∧
      leafAdmissible x.2 a.2

namespace TreeMessageWitness

inductive LeafWorld
  | left
  | right

inductive LeafAction
  | alpha
  | beta

open LeafWorld LeafAction

def leafAvailable : LeafAction → Prop := fun _ => True

def parentAvailable : Unit → Prop := fun _ => True

def leafAdmissible : LeafWorld → LeafAction → Prop
  | left, alpha => True
  | left, beta => False
  | right, alpha => False
  | right, beta => True

def parentAdmissible : Unit → Fin 2 → Unit → Prop :=
  fun _ _ _ => True

def leafEncode : LeafWorld → Fin 2
  | left => 0
  | right => 1

def leafDecode : Fin 2 → LeafAction :=
  fun m => if m.1 = 0 then alpha else beta

def parentEncode : Unit → Fin 2 → Fin 1 :=
  fun _ _ => 0

def parentDecode : Fin 1 → Unit :=
  fun _ => ()

theorem distributed_protocol_one_upstream_message :
    TwoLevelDistributedProtocol
      (Fin 2) (Fin 1)
      leafAvailable parentAvailable
      leafAdmissible parentAdmissible := by
  refine
    ⟨leafEncode, leafDecode, parentEncode, parentDecode,
     ?_, ?_, ?_, ?_⟩
  · intro lm
    trivial
  · intro pm
    trivial
  · intro lw
    cases lw <;> simp [leafEncode, leafDecode, leafAdmissible]
  · intro pw lw
    trivial

def globalAvailable : Unit × LeafAction → Prop :=
  TwoLevelAvailable leafAvailable parentAvailable

def globalAdmissible :
    Unit × LeafWorld → Unit × LeafAction → Prop :=
  fun x a => leafAdmissible x.2 a.2

/-- A centralized protocol with only one upstream symbol cannot certify the
    complete global action: left and right require different leaf actions. -/
theorem no_centralized_one_message :
    ¬ CertifiedMessages globalAvailable globalAdmissible 1 := by
  rintro ⟨encode, decode, havail, hcert⟩
  let xL : Unit × LeafWorld := ((), left)
  let xR : Unit × LeafWorld := ((), right)
  have hsame : encode xL = encode xR := Subsingleton.elim _ _
  have hL := hcert xL
  have hR := hcert xR
  have hdec : decode (encode xL) = decode (encode xR) := by
    rw [hsame]
  have hLeafL : leafAdmissible left (decode (encode xL)).2 := hL
  have hLeafR : leafAdmissible right (decode (encode xR)).2 := hR
  rw [← hdec] at hLeafR
  cases hact : (decode (encode xL)).2 with
  | alpha =>
      simpa [leafAdmissible, hact] using hLeafR
  | beta =>
      simpa [leafAdmissible, hact] using hLeafL

def globalEncodeTwo : Unit × LeafWorld → Fin 2
  | (_, left) => 0
  | (_, right) => 1

def globalDecodeTwo : Fin 2 → Unit × LeafAction :=
  fun m =>
    if m.1 = 0 then ((), alpha) else ((), beta)

theorem centralized_two_messages :
    CertifiedMessages globalAvailable globalAdmissible 2 := by
  refine ⟨globalEncodeTwo, globalDecodeTwo, ?_, ?_⟩
  · intro m
    constructor <;> trivial
  · intro x
    rcases x with ⟨u, lw⟩
    cases lw <;>
      simp [globalEncodeTwo, globalDecodeTwo,
        globalAvailable, globalAdmissible,
        TwoLevelAvailable, leafAvailable,
        parentAvailable, leafAdmissible]

theorem centralized_minimum_two :
    IsMinCertifiedMessages globalAvailable globalAdmissible 2 := by
  refine ⟨centralized_two_messages, ?_⟩
  intro n hn
  cases n with
  | zero =>
      rcases hn with ⟨encode, decode, havail, hcert⟩
      exact Fin.elim0 (encode ((), left))
  | succ n =>
      cases n with
      | zero =>
          exact False.elim (no_centralized_one_message hn)
      | succ k =>
          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))

/-- Strict distributed-vs-centralized separation.
    One message can travel upward when the leaf keeps and decodes its own local
    two-symbol certificate, while a centralized one-message protocol for the
    full global action is impossible and needs exactly two symbols. -/
theorem local_information_can_remain_local :
    TwoLevelDistributedProtocol
        (Fin 2) (Fin 1)
        leafAvailable parentAvailable
        leafAdmissible parentAdmissible ∧
    ¬ CertifiedMessages globalAvailable globalAdmissible 1 ∧
    IsMinCertifiedMessages globalAvailable globalAdmissible 2 := by
  exact
    ⟨distributed_protocol_one_upstream_message,
     no_centralized_one_message,
     centralized_minimum_two⟩

end TreeMessageWitness

end InsacermoV13Kernel
