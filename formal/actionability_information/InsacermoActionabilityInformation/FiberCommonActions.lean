import InsacermoActionabilityInformation.CapabilityGainNonSubmodular

namespace InsacermoActionabilityInformation

/-- Actions that are good for every realized world in one observation fiber. -/
def FiberCommonActions {S A Y : Type*}
    (Good : S → A → Prop) (B : Set S) (h : S → Y) (y : Y) : Set A :=
  {a | ∀ s, s ∈ B → h s = y → Good s a}

/-- An observation value is realized by at least one admissible world. -/
def RealizedFiber {S Y : Type*} (B : Set S) (h : S → Y) (y : Y) : Prop :=
  ∃ s, s ∈ B ∧ h s = y

/-- Exact fiber criterion for arbitrary (possibly nondeterministic) `Good`.
A representation is safe iff every realized observation fiber has at least one
available action that is good for every world in that fiber. -/
theorem safeRep_iff_fiberCommonActions_hits_capability
    {S A Y : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y} :
    SafeRep Good B C h ↔
      ∀ y, RealizedFiber B h y →
        ∃ a, a ∈ C ∧ a ∈ FiberCommonActions Good B h y := by
  constructor
  · intro hsafe y hy
    rcases hsafe y hy with ⟨a, haC, hall⟩
    exact ⟨a, haC, hall⟩
  · intro hfiber y hy
    rcases hfiber y hy with ⟨a, haC, hall⟩
    exact ⟨a, haC, hall⟩

/-- Equivalent set-intersection form: every realized fiber's common-good action
set must intersect the currently available capability set. -/
theorem safeRep_iff_fiberCommonActions_intersects
    {S A Y : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y} :
    SafeRep Good B C h ↔
      ∀ y, RealizedFiber B h y →
        (FiberCommonActions Good B h y ∩ C).Nonempty := by
  rw [safeRep_iff_fiberCommonActions_hits_capability]
  constructor
  · intro h y hy
    rcases h y hy with ⟨a, haC, haF⟩
    exact ⟨a, haF, haC⟩
  · intro h y hy
    rcases h y hy with ⟨a, haF, haC⟩
    exact ⟨a, haC, haF⟩

/-- A realized fiber whose common-good action set misses the capability set is
an exact local obstruction to `SafeRep`. -/
theorem fiberCapabilityObstruction_blocks_safeRep
    {S A Y : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y} {y : Y}
    (hreal : RealizedFiber B h y)
    (hmiss : (FiberCommonActions Good B h y ∩ C) = ∅) :
    ¬ SafeRep Good B C h := by
  intro hsafe
  have hhit := (safeRep_iff_fiberCommonActions_intersects.mp hsafe) y hreal
  rw [hmiss] at hhit
  exact Set.not_nonempty_empty hhit

/-- Capability expansion can repair one local fiber obstruction without
repairing another; global `SafeRep` requires hitting every realized fiber.
This is the structural source of capability complementarity. -/
theorem safeRep_requires_all_realized_fibers_hit
    {S A Y : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y}
    (hsafe : SafeRep Good B C h) :
    ∀ y, RealizedFiber B h y →
      (FiberCommonActions Good B h y ∩ C).Nonempty :=
  safeRep_iff_fiberCommonActions_intersects.mp hsafe

end InsacermoActionabilityInformation
