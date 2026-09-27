import InsacermoV13Kernel.RecursiveTreeCertificates

namespace InsacermoV13Kernel

universe uW uA uM

/-- A finite binary tree context with exactly one hole.
    Plugging a subtree into the hole places it at arbitrary finite depth. -/
inductive TreeContext (World : Type uW) where
  | hole : TreeContext World
  | left : World → TreeContext World → CertTree World → TreeContext World
  | right : World → CertTree World → TreeContext World → TreeContext World

/-- Fill the unique hole of a tree context. -/
def plug {World : Type uW} :
    TreeContext World → CertTree World → CertTree World
  | .hole, t => t
  | .left w ctx sibling, t =>
      .branch w (plug ctx t) sibling
  | .right w sibling ctx, t =>
      .branch w sibling (plug ctx t)

/-- Context congruence for interface messages.
    Message-equivalent subtrees remain message-equivalent in every finite
    ancestor environment. -/
theorem treeMessage_context_congruence
    {World : Type uW} {Message : Type uM}
    {encode : World → ChildInterface Message → Message}
    {t₁ t₂ : CertTree World}
    (hmsg : treeMessage encode t₁ = treeMessage encode t₂) :
    ∀ ctx : TreeContext World,
      treeMessage encode (plug ctx t₁) =
        treeMessage encode (plug ctx t₂) := by
  intro ctx
  induction ctx with
  | hole =>
      exact hmsg
  | left w ctx sibling ih =>
      exact replace_left_subtree_same_message ih
  | right w sibling ctx ih =>
      exact replace_right_subtree_same_message ih

/-- The action selected at the root of every ancestor context is therefore
    invariant under replacement by a message-equivalent subtree. -/
theorem treeRootAction_context_congruence
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {encode : World → ChildInterface Message → Message}
    {decode : Message → Action}
    {t₁ t₂ : CertTree World}
    (hmsg : treeMessage encode t₁ = treeMessage encode t₂) :
    ∀ ctx : TreeContext World,
      treeRootAction encode decode (plug ctx t₁) =
        treeRootAction encode decode (plug ctx t₂) := by
  intro ctx
  unfold treeRootAction
  rw [treeMessage_context_congruence hmsg ctx]

/-- Certified replacement principle.
    If a whole tree containing t₁ is certified, t₂ is itself certified, and
    t₁,t₂ expose the same interface message, then replacing t₁ by t₂ anywhere
    in the ancestor context preserves certification of the whole tree. -/
theorem treeCertified_context_replacement
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : World → ChildInterface Message → Action → Prop}
    {encode : World → ChildInterface Message → Message}
    {decode : Message → Action}
    {t₁ t₂ : CertTree World}
    (hmsg : treeMessage encode t₁ = treeMessage encode t₂)
    (ht₂ :
      TreeCertified available admissible encode decode t₂) :
    ∀ ctx : TreeContext World,
      TreeCertified available admissible encode decode (plug ctx t₁) →
      TreeCertified available admissible encode decode (plug ctx t₂) := by
  intro ctx
  induction ctx with
  | hole =>
      intro hwhole
      exact ht₂
  | left w ctx sibling ih =>
      intro hwhole
      simp [plug, TreeCertified] at hwhole ⊢
      rcases hwhole with ⟨hav, hadm, hleft, hsib⟩
      have hctxmsg :
          treeMessage encode (plug ctx t₁) =
            treeMessage encode (plug ctx t₂) :=
        treeMessage_context_congruence hmsg ctx
      have hav' : available
          (decode
            (encode w
              (ChildInterface.pair
                (treeMessage encode (plug ctx t₂))
                (treeMessage encode sibling)))) := by
        simpa [hctxmsg] using hav
      have hadm' : admissible w
          (ChildInterface.pair
            (treeMessage encode (plug ctx t₂))
            (treeMessage encode sibling))
          (decode
            (encode w
              (ChildInterface.pair
                (treeMessage encode (plug ctx t₂))
                (treeMessage encode sibling)))) := by
        simpa [hctxmsg] using hadm
      exact ⟨hav', hadm', ih hleft, hsib⟩
  | right w sibling ctx ih =>
      intro hwhole
      simp [plug, TreeCertified] at hwhole ⊢
      rcases hwhole with ⟨hav, hadm, hsib, hright⟩
      have hctxmsg :
          treeMessage encode (plug ctx t₁) =
            treeMessage encode (plug ctx t₂) :=
        treeMessage_context_congruence hmsg ctx
      have hav' : available
          (decode
            (encode w
              (ChildInterface.pair
                (treeMessage encode sibling)
                (treeMessage encode (plug ctx t₂))))) := by
        simpa [hctxmsg] using hav
      have hadm' : admissible w
          (ChildInterface.pair
            (treeMessage encode sibling)
            (treeMessage encode (plug ctx t₂)))
          (decode
            (encode w
              (ChildInterface.pair
                (treeMessage encode sibling)
                (treeMessage encode (plug ctx t₂))))) := by
        simpa [hctxmsg] using hadm
      exact ⟨hav', hadm', hsib, ih hright⟩

/-- Bidirectional form: if both candidate subtrees are internally certified and
    emit the same interface message, no ancestor context can distinguish them
    at the level of whole-tree certification. -/
theorem treeCertified_context_equivalence
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : World → ChildInterface Message → Action → Prop}
    {encode : World → ChildInterface Message → Message}
    {decode : Message → Action}
    {t₁ t₂ : CertTree World}
    (hmsg : treeMessage encode t₁ = treeMessage encode t₂)
    (ht₁ :
      TreeCertified available admissible encode decode t₁)
    (ht₂ :
      TreeCertified available admissible encode decode t₂) :
    ∀ ctx : TreeContext World,
      TreeCertified available admissible encode decode (plug ctx t₁) ↔
      TreeCertified available admissible encode decode (plug ctx t₂) := by
  intro ctx
  constructor
  · exact treeCertified_context_replacement hmsg ht₂ ctx
  · exact treeCertified_context_replacement hmsg.symm ht₁ ctx

namespace TreeContextCongruenceWitness

open RecursiveTreeWitness
open RecursiveTreeWitness.World

def deepContext : TreeContext World :=
  .left one
    (.right zero
      (.leaf one)
      (.left one
        .hole
        (.leaf zero)))
    (.branch zero (.leaf zero) (.leaf one))

/-- The earlier tiny and deep hidden subtrees remain indistinguishable after
    being embedded several ancestors above the replacement point. -/
theorem deep_ancestor_message_invariance :
    treeMessage encode (plug deepContext hiddenLeft₁) =
      treeMessage encode (plug deepContext hiddenLeft₂) := by
  exact
    treeMessage_context_congruence
      hidden_subtrees_same_interface_message
      deepContext

theorem hiddenLeft₁_certified :
    TreeCertified available admissible encode decode hiddenLeft₁ := by
  simp [hiddenLeft₁, TreeCertified, encode, decode, admissible, available]

theorem hiddenLeft₂_certified :
    TreeCertified available admissible encode decode hiddenLeft₂ := by
  simp [hiddenLeft₂, TreeCertified, treeMessage,
    encode, decode, admissible, available]

/-- Full finite-context substitutability witness: even after embedding the
    candidate subtree deep inside an ancestor environment, certification is
    unchanged. -/
theorem deep_ancestor_certification_equivalence :
    TreeCertified available admissible encode decode
        (plug deepContext hiddenLeft₁) ↔
      TreeCertified available admissible encode decode
        (plug deepContext hiddenLeft₂) := by
  exact
    treeCertified_context_equivalence
      hidden_subtrees_same_interface_message
      hiddenLeft₁_certified
      hiddenLeft₂_certified
      deepContext

end TreeContextCongruenceWitness

end InsacermoV13Kernel
