import InsacermoV13Kernel.TreeMessagePassing

namespace InsacermoV13Kernel

universe uW uA uM

/-- Finite binary tree of local worlds. -/
inductive CertTree (World : Type uW) where
  | leaf : World → CertTree World
  | branch : World → CertTree World → CertTree World → CertTree World

/-- What a node sees from below: no child messages at a leaf, or the pair of
    root messages emitted by its two children. -/
inductive ChildInterface (Message : Type uM) where
  | none : ChildInterface Message
  | pair : Message → Message → ChildInterface Message

/-- A single local rule reused at every node of the recursive tree.
    It sees only the node's local world and the messages crossing its child
    interfaces; it never sees the internal states of the subtrees. -/
def RecursiveNodeProtocol
    {World : Type uW} {Action : Type uA}
    (Message : Type uM)
    (available : Action → Prop)
    (admissible : World → ChildInterface Message → Action → Prop) : Prop :=
  ∃ encode : World → ChildInterface Message → Message,
    ∃ decode : Message → Action,
      (∀ m, available (decode m)) ∧
      ∀ w ci, admissible w ci (decode (encode w ci))

/-- Bottom-up message emitted by the root of a subtree. -/
def treeMessage
    {World : Type uW} {Message : Type uM}
    (encode : World → ChildInterface Message → Message) :
    CertTree World → Message
  | .leaf w =>
      encode w ChildInterface.none
  | .branch w left right =>
      encode w
        (ChildInterface.pair
          (treeMessage encode left)
          (treeMessage encode right))

/-- Local action selected at the root of a subtree. -/
def treeRootAction
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    (encode : World → ChildInterface Message → Message)
    (decode : Message → Action)
    (t : CertTree World) : Action :=
  decode (treeMessage encode t)

/-- Every node of a subtree is locally certified using only the messages
    supplied by its immediate children. -/
def TreeCertified
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    (available : Action → Prop)
    (admissible : World → ChildInterface Message → Action → Prop)
    (encode : World → ChildInterface Message → Message)
    (decode : Message → Action) :
    CertTree World → Prop
  | .leaf w =>
      available (decode (encode w ChildInterface.none)) ∧
      admissible
        w
        ChildInterface.none
        (decode (encode w ChildInterface.none))
  | .branch w left right =>
      let lm := treeMessage encode left
      let rm := treeMessage encode right
      let ci := ChildInterface.pair lm rm
      available (decode (encode w ci)) ∧
      admissible w ci (decode (encode w ci)) ∧
      TreeCertified available admissible encode decode left ∧
      TreeCertified available admissible encode decode right

/-- Recursive certification theorem.
    A single locally certified node rule is sufficient to certify every node
    of every finite binary tree, at arbitrary finite depth. -/
theorem recursiveTree_all_nodes_certified
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : World → ChildInterface Message → Action → Prop}
    (hlocal : RecursiveNodeProtocol Message available admissible) :
    ∃ encode : World → ChildInterface Message → Message,
      ∃ decode : Message → Action,
        ∀ t : CertTree World,
          TreeCertified available admissible encode decode t := by
  rcases hlocal with ⟨encode, decode, havail, hcert⟩
  refine ⟨encode, decode, ?_⟩
  intro t
  induction t with
  | leaf w =>
      exact
        ⟨havail (encode w ChildInterface.none),
         hcert w ChildInterface.none⟩
  | branch w left right ihLeft ihRight =>
      let lm := treeMessage encode left
      let rm := treeMessage encode right
      let ci := ChildInterface.pair lm rm
      exact
        ⟨havail (encode w ci),
         hcert w ci,
         ihLeft,
         ihRight⟩

/-- The parent root message depends on each child subtree only through that
    child's emitted root message. Internal child state is observationally
    irrelevant above the interface once the message is fixed. -/
theorem replace_left_subtree_same_message
    {World : Type uW} {Message : Type uM}
    {encode : World → ChildInterface Message → Message}
    {w : World}
    {left₁ left₂ right : CertTree World}
    (hleft : treeMessage encode left₁ = treeMessage encode left₂) :
    treeMessage encode (.branch w left₁ right) =
      treeMessage encode (.branch w left₂ right) := by
  simp [treeMessage, hleft]

theorem replace_right_subtree_same_message
    {World : Type uW} {Message : Type uM}
    {encode : World → ChildInterface Message → Message}
    {w : World}
    {left right₁ right₂ : CertTree World}
    (hright : treeMessage encode right₁ = treeMessage encode right₂) :
    treeMessage encode (.branch w left right₁) =
      treeMessage encode (.branch w left right₂) := by
  simp [treeMessage, hright]

/-- The same replacement invariance holds for the action chosen at the parent. -/
theorem replace_left_subtree_same_parent_action
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {encode : World → ChildInterface Message → Message}
    {decode : Message → Action}
    {w : World}
    {left₁ left₂ right : CertTree World}
    (hleft : treeMessage encode left₁ = treeMessage encode left₂) :
    treeRootAction encode decode (.branch w left₁ right) =
      treeRootAction encode decode (.branch w left₂ right) := by
  unfold treeRootAction
  rw [replace_left_subtree_same_message hleft]

/-- Two children can be replaced simultaneously by message-equivalent
    subtrees without changing the parent's emitted message. -/
theorem replace_both_subtrees_same_message
    {World : Type uW} {Message : Type uM}
    {encode : World → ChildInterface Message → Message}
    {w : World}
    {left₁ left₂ right₁ right₂ : CertTree World}
    (hleft : treeMessage encode left₁ = treeMessage encode left₂)
    (hright : treeMessage encode right₁ = treeMessage encode right₂) :
    treeMessage encode (.branch w left₁ right₁) =
      treeMessage encode (.branch w left₂ right₂) := by
  calc
    treeMessage encode (.branch w left₁ right₁) =
        treeMessage encode (.branch w left₂ right₁) :=
      replace_left_subtree_same_message hleft
    _ =
        treeMessage encode (.branch w left₂ right₂) :=
      replace_right_subtree_same_message hright

namespace RecursiveTreeWitness

inductive World
  | zero
  | one

inductive Action
  | alpha
  | beta

open World Action

def available : Action → Prop := fun _ => True

/-- The local obligation at a node depends only on its own world.
    Child messages are deliberately irrelevant here, which gives a clean
    witness that arbitrarily much hidden subtree state can remain local. -/
def admissible : World → ChildInterface (Fin 2) → Action → Prop
  | zero, _, alpha => True
  | one, _, beta => True
  | _, _, _ => False

def encode : World → ChildInterface (Fin 2) → Fin 2
  | zero, _ => 0
  | one, _ => 1

def decode : Fin 2 → Action :=
  fun m => if m.1 = 0 then alpha else beta

theorem local_rule_certified :
    RecursiveNodeProtocol (Fin 2) available admissible := by
  refine ⟨encode, decode, ?_, ?_⟩
  · intro m
    trivial
  · intro w ci
    cases w <;> simp [encode, decode, admissible]

/-- Every finite binary tree over the witness worlds is certified by the same
    two-message local rule, regardless of depth or number of nodes. -/
theorem every_finite_tree_certified :
    ∃ enc : World → ChildInterface (Fin 2) → Fin 2,
      ∃ dec : Fin 2 → Action,
        ∀ t : CertTree World,
          TreeCertified available admissible enc dec t := by
  exact recursiveTree_all_nodes_certified local_rule_certified

def hiddenLeft₁ : CertTree World :=
  .leaf zero

def hiddenLeft₂ : CertTree World :=
  .branch zero
    (.branch zero (.leaf one) (.leaf zero))
    (.branch one (.leaf zero) (.leaf one))

def parent : World := one
def rightSibling : CertTree World := .leaf one

/-- Two structurally very different subtrees with the same root world emit
    exactly the same interface message. -/
theorem hidden_subtrees_same_interface_message :
    treeMessage encode hiddenLeft₁ =
      treeMessage encode hiddenLeft₂ := by
  rfl

/-- Therefore replacing the tiny subtree by a much deeper one is invisible to
    the parent at the interface. -/
theorem hidden_subtree_replacement_invisible :
    treeMessage encode (.branch parent hiddenLeft₁ rightSibling) =
      treeMessage encode (.branch parent hiddenLeft₂ rightSibling) := by
  exact
    replace_left_subtree_same_message
      hidden_subtrees_same_interface_message

end RecursiveTreeWitness

end InsacermoV13Kernel
