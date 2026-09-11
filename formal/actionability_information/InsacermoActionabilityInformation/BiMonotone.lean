import Mathlib

namespace InsacermoActionabilityInformation

/-- A representation is safe when every realized code on the ambiguity set
admits one common action from the current capability set. -/
def SafeRep {S A Y : Type*}
    (Good : S → A → Prop) (B : Set S) (C : Set A) (h : S → Y) : Prop :=
  ∀ y, (∃ s, s ∈ B ∧ h s = y) →
    ∃ a, a ∈ C ∧ ∀ s, s ∈ B → h s = y → Good s a

/-- `fine` refines `coarse` when the coarse code is a deterministic function
of the fine code. Thus every fine fiber is contained in a coarse fiber. -/
def Refines {S YFine YCoarse : Type*}
    (fine : S → YFine) (coarse : S → YCoarse) : Prop :=
  ∃ f : YFine → YCoarse, ∀ s, coarse s = f (fine s)

/-- Core product-order theorem: safety is monotone jointly in information
refinement and capability inclusion. -/
theorem safeRep_of_refines_of_capabilitySubset
    {S A YFine YCoarse : Type*}
    {Good : S → A → Prop} {B : Set S}
    {C C' : Set A} {fine : S → YFine} {coarse : S → YCoarse}
    (hsafe : SafeRep Good B C coarse)
    (href : Refines fine coarse)
    (hcap : C ⊆ C') :
    SafeRep Good B C' fine := by
  rcases href with ⟨f, hf⟩
  intro y hy
  rcases hy with ⟨s0, hs0B, hs0y⟩
  have hreal : ∃ s, s ∈ B ∧ coarse s = f y := by
    refine ⟨s0, hs0B, ?_⟩
    rw [hf s0, hs0y]
  rcases hsafe (f y) hreal with ⟨a, haC, hgood⟩
  refine ⟨a, hcap haC, ?_⟩
  intro s hsB hsy
  apply hgood s hsB
  rw [hf s, hsy]

/-- Capability-only monotonicity is a special case of the product theorem. -/
theorem safeRep_capability_mono
    {S A Y : Type*}
    {Good : S → A → Prop} {B : Set S}
    {C C' : Set A} {h : S → Y}
    (hsafe : SafeRep Good B C h)
    (hcap : C ⊆ C') :
    SafeRep Good B C' h := by
  apply safeRep_of_refines_of_capabilitySubset hsafe
  · exact ⟨id, by intro s; rfl⟩
  · exact hcap

/-- Information-refinement monotonicity is the other special case. -/
theorem safeRep_information_mono
    {S A YFine YCoarse : Type*}
    {Good : S → A → Prop} {B : Set S}
    {C : Set A} {fine : S → YFine} {coarse : S → YCoarse}
    (hsafe : SafeRep Good B C coarse)
    (href : Refines fine coarse) :
    SafeRep Good B C fine := by
  exact safeRep_of_refines_of_capabilitySubset hsafe href (Set.Subset.rfl)

/- A two-world witness showing that the same baseline obstruction can be
repaired either by more information (PROBE direction) or by more capability
(REPAIR direction). -/
namespace ProbeRepairWitness

inductive World where
  | w0
  | w1
  deriving DecidableEq

inductive Action where
  | a0
  | a1
  | universal
  deriving DecidableEq

inductive CoarseCode where
  | star
  deriving DecidableEq

inductive FineCode where
  | c0
  | c1
  deriving DecidableEq

def Good : World → Action → Prop
  | .w0, .a0 => True
  | .w1, .a1 => True
  | .w0, .universal => True
  | .w1, .universal => True
  | _, _ => False

def baseCaps : Set Action := {a | a = .a0 ∨ a = .a1}

def expandedCaps : Set Action := Set.univ

def coarseObs : World → CoarseCode := fun _ => .star

def fineObs : World → FineCode
  | .w0 => .c0
  | .w1 => .c1

theorem fine_refines_coarse : Refines fineObs coarseObs := by
  refine ⟨fun _ => CoarseCode.star, ?_⟩
  intro s
  cases s <;> rfl

theorem baseline_not_safe :
    ¬ SafeRep Good Set.univ baseCaps coarseObs := by
  intro h
  have hreal : ∃ s, s ∈ (Set.univ : Set World) ∧ coarseObs s = CoarseCode.star := by
    exact ⟨.w0, by simp, rfl⟩
  rcases h .star hreal with ⟨a, ha, hgood⟩
  have g0 : Good .w0 a := hgood .w0 (by simp) rfl
  have g1 : Good .w1 a := hgood .w1 (by simp) rfl
  cases a <;> simp [baseCaps, Good] at ha g0 g1

theorem probe_route_safe :
    SafeRep Good Set.univ baseCaps fineObs := by
  intro y _
  cases y with
  | c0 =>
      refine ⟨.a0, ?_, ?_⟩
      · simp [baseCaps]
      · intro s _ hs
        cases s <;> simp [fineObs, Good] at hs ⊢
  | c1 =>
      refine ⟨.a1, ?_, ?_⟩
      · simp [baseCaps]
      · intro s _ hs
        cases s <;> simp [fineObs, Good] at hs ⊢

theorem repair_route_safe :
    SafeRep Good Set.univ expandedCaps coarseObs := by
  intro _ _
  refine ⟨.universal, by simp [expandedCaps], ?_⟩
  intro s _ _
  cases s <;> simp [Good]

theorem base_subset_expanded : baseCaps ⊆ expandedCaps := by
  intro a _
  simp [expandedCaps]

/-- The witness packages the engine geometry: the same unsafe coarse/base point
has an information-only safe move and a capability-only safe move. -/
theorem probe_and_repair_are_both_valid_routes :
    (¬ SafeRep Good Set.univ baseCaps coarseObs) ∧
    (Refines fineObs coarseObs ∧ SafeRep Good Set.univ baseCaps fineObs) ∧
    (baseCaps ⊆ expandedCaps ∧ SafeRep Good Set.univ expandedCaps coarseObs) := by
  exact ⟨baseline_not_safe,
    ⟨fine_refines_coarse, probe_route_safe⟩,
    ⟨base_subset_expanded, repair_route_safe⟩⟩

end ProbeRepairWitness

end InsacermoActionabilityInformation
