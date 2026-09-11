import InsacermoActionabilityInformation.FiberCommonActions

namespace InsacermoActionabilityInformation

/-- A finite set of worlds has a common available good action. -/
def HasCommonActionOn {S A : Type*} [DecidableEq S]
    (Good : S → A → Prop) (C : Set A) (F : Finset S) : Prop :=
  ∃ a, a ∈ C ∧ ∀ s, s ∈ F → Good s a

/-- A finite common-action obstruction: the worlds in `F` admit no single
currently available action that is good for all of them. -/
def CommonActionObstruction {S A : Type*} [DecidableEq S]
    (Good : S → A → Prop) (C : Set A) (F : Finset S) : Prop :=
  F.Nonempty ∧ ¬ HasCommonActionOn Good C F

/-- Minimal finite common-action obstruction: the full set is obstructed but
every nonempty proper subconfiguration has a common available good action. -/
def MinimalCommonActionObstruction {S A : Type*} [DecidableEq S]
    (Good : S → A → Prop) (C : Set A) (F : Finset S) : Prop :=
  CommonActionObstruction Good C F ∧
    ∀ G, G ⊂ F → G.Nonempty → HasCommonActionOn Good C G

/-- Any finite obstruction lying inside one realized observation fiber blocks
`SafeRep`. This is the generic hyperedge obstruction principle. -/
theorem finiteObstruction_inside_fiber_blocks_safeRep
    {S A Y : Type*} [DecidableEq S]
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y}
    {F : Finset S} {y : Y}
    (hobs : CommonActionObstruction Good C F)
    (hsub : ∀ s, s ∈ F → s ∈ B)
    (hfiber : ∀ s, s ∈ F → h s = y) :
    ¬ SafeRep Good B C h := by
  intro hsafe
  rcases hobs.1 with ⟨s0, hs0F⟩
  have hs0B := hsub s0 hs0F
  have hy : RealizedFiber B h y := ⟨s0, hs0B, hfiber s0 hs0F⟩
  rcases (safeRep_iff_fiberCommonActions_hits_capability.mp hsafe) y hy with
    ⟨a, haC, haFiber⟩
  apply hobs.2
  refine ⟨a, haC, ?_⟩
  intro s hsF
  exact haFiber s (hsub s hsF) (hfiber s hsF)

/-- Pairwise compatibility of three worlds under an available capability set. -/
def PairwiseCompatibleTriple {S A : Type*}
    (Good : S → A → Prop) (C : Set A) (s₁ s₂ s₃ : S) : Prop :=
  (∃ a, a ∈ C ∧ Good s₁ a ∧ Good s₂ a) ∧
  (∃ a, a ∈ C ∧ Good s₁ a ∧ Good s₃ a) ∧
  (∃ a, a ∈ C ∧ Good s₂ a ∧ Good s₃ a)

/-- A genuine rank-3 obstruction: every pair is compatible, but the triple has
no common available good action. -/
def RankThreeObstruction {S A : Type*}
    (Good : S → A → Prop) (C : Set A) (s₁ s₂ s₃ : S) : Prop :=
  PairwiseCompatibleTriple Good C s₁ s₂ s₃ ∧
  ¬ ∃ a, a ∈ C ∧ Good s₁ a ∧ Good s₂ a ∧ Good s₃ a

/-- A rank-3 obstruction aliased into one observation value blocks `SafeRep`,
even though every pair is individually compatible. -/
theorem rankThreeObstruction_blocks_safeRep
    {S A Y : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y}
    {s₁ s₂ s₃ : S} {y : Y}
    (hobs : RankThreeObstruction Good C s₁ s₂ s₃)
    (hB₁ : s₁ ∈ B) (hB₂ : s₂ ∈ B) (hB₃ : s₃ ∈ B)
    (h₁ : h s₁ = y) (h₂ : h s₂ = y) (h₃ : h s₃ = y) :
    ¬ SafeRep Good B C h := by
  intro hsafe
  have hy : RealizedFiber B h y := ⟨s₁, hB₁, h₁⟩
  rcases (safeRep_iff_fiberCommonActions_hits_capability.mp hsafe) y hy with
    ⟨a, haC, hall⟩
  apply hobs.2
  exact ⟨a, haC,
    hall s₁ hB₁ h₁,
    hall s₂ hB₂ h₂,
    hall s₃ hB₃ h₃⟩

/-! ### Explicit rank-3 witness -/

inductive TripleWorld
  | s1 | s2 | s3
  deriving DecidableEq, Fintype

inductive TripleAction
  | a | b | c
  deriving DecidableEq, Fintype

open TripleWorld TripleAction

/-- Classical 3-cycle action relation:
`s1` allows {a,b}, `s2` allows {b,c}, `s3` allows {a,c}. -/
def TripleGood : TripleWorld → TripleAction → Prop
  | s1, a => True
  | s1, b => True
  | s2, b => True
  | s2, c => True
  | s3, a => True
  | s3, c => True
  | _, _ => False

/-- All actions are available. -/
def TripleCaps : Set TripleAction := Set.univ

/-- All three worlds are deliberately aliased into one observation value. -/
def TripleAliasObs : TripleWorld → Unit := fun _ => ()

/-- Every pair of worlds shares an available good action. -/
theorem tripleWitness_pairwiseCompatible :
    PairwiseCompatibleTriple TripleGood TripleCaps s1 s2 s3 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨b, Set.mem_univ b, True.intro, True.intro⟩
  · exact ⟨a, Set.mem_univ a, True.intro, True.intro⟩
  · exact ⟨c, Set.mem_univ c, True.intro, True.intro⟩

/-- But no single action is good for all three worlds. -/
theorem tripleWitness_noCommonAction :
    ¬ ∃ x, x ∈ TripleCaps ∧
      TripleGood s1 x ∧ TripleGood s2 x ∧ TripleGood s3 x := by
  rintro ⟨x, _hxC, h1, h2, h3⟩
  cases x with
  | a => exact h2
  | b => exact h3
  | c => exact h1

/-- Exact rank-3 obstruction certificate. -/
theorem tripleWitness_rankThree :
    RankThreeObstruction TripleGood TripleCaps s1 s2 s3 := by
  exact ⟨tripleWitness_pairwiseCompatible, tripleWitness_noCommonAction⟩

/-- Pairwise compatibility is not sufficient for global actionability: the
constant representation is unsafe even though all three pairs are compatible. -/
theorem pairwiseCompatibility_does_not_imply_safeRep :
    PairwiseCompatibleTriple TripleGood TripleCaps s1 s2 s3 ∧
    ¬ SafeRep TripleGood Set.univ TripleCaps TripleAliasObs := by
  refine ⟨tripleWitness_pairwiseCompatible, ?_⟩
  exact rankThreeObstruction_blocks_safeRep
    tripleWitness_rankThree
    (Set.mem_univ s1) (Set.mem_univ s2) (Set.mem_univ s3)
    rfl rfl rfl

/-- The full three-world set is a finite common-action obstruction. -/
theorem tripleWitness_finsetObstruction :
    CommonActionObstruction TripleGood TripleCaps ({s1, s2, s3} : Finset TripleWorld) := by
  constructor
  · exact ⟨s1, by simp⟩
  · intro hcommon
    rcases hcommon with ⟨x, hxC, hall⟩
    apply tripleWitness_noCommonAction
    refine ⟨x, hxC, ?_, ?_, ?_⟩
    · exact hall s1 (by simp)
    · exact hall s2 (by simp)
    · exact hall s3 (by simp)

/-- Each of the three two-world subconfigurations has a common action. -/
theorem tripleWitness_pair12_common :
    HasCommonActionOn TripleGood TripleCaps ({s1, s2} : Finset TripleWorld) := by
  refine ⟨b, Set.mem_univ b, ?_⟩
  intro s hs
  simp at hs
  rcases hs with h | h
  · subst s; exact True.intro
  · subst s; exact True.intro

theorem tripleWitness_pair13_common :
    HasCommonActionOn TripleGood TripleCaps ({s1, s3} : Finset TripleWorld) := by
  refine ⟨a, Set.mem_univ a, ?_⟩
  intro s hs
  simp at hs
  rcases hs with h | h
  · subst s; exact True.intro
  · subst s; exact True.intro

theorem tripleWitness_pair23_common :
    HasCommonActionOn TripleGood TripleCaps ({s2, s3} : Finset TripleWorld) := by
  refine ⟨c, Set.mem_univ c, ?_⟩
  intro s hs
  simp at hs
  rcases hs with h | h
  · subst s; exact True.intro
  · subst s; exact True.intro

end InsacermoActionabilityInformation
