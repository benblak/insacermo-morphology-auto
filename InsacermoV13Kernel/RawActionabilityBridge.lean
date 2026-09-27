namespace InsacermoV13Kernel

universe u v w

/-- `fine` refines `coarse` when equality at the fine observation level
    always implies equality at the coarse level. -/
def Refines {World : Type u} {Coarse : Type v} {Fine : Type w}
    (coarse : World → Coarse) (fine : World → Fine) : Prop :=
  ∀ ⦃x y : World⦄, fine x = fine y → coarse x = coarse y

/-- A world is actionably certified at an observation level when there is one
    currently available action admissible for every world in its observation fiber. -/
def FiberSafe {World : Type u} {Obs : Type v} {Action : Type w}
    (obs : World → Obs) (available : Action → Prop)
    (admissible : World → Action → Prop) (x : World) : Prop :=
  ∃ a, available a ∧ ∀ ⦃y : World⦄, obs y = obs x → admissible y a

/-- Refinement cannot destroy an already valid common-action certificate. -/
theorem fiberSafe_of_refinement
    {World : Type u} {Coarse : Type v} {Fine : Type w} {Action : Type*}
    {coarse : World → Coarse} {fine : World → Fine}
    {available : Action → Prop} {admissible : World → Action → Prop}
    {x : World}
    (href : Refines coarse fine)
    (hsafe : FiberSafe coarse available admissible x) :
    FiberSafe fine available admissible x := by
  rcases hsafe with ⟨a, haAvail, ha⟩
  refine ⟨a, haAvail, ?_⟩
  intro y hFine
  exact ha (href hFine)

/-- Refinement is transitive. -/
theorem Refines.trans
    {World : Type u} {A : Type v} {B : Type w} {C : Type*}
    {rA : World → A} {rB : World → B} {rC : World → C}
    (hAB : Refines rA rB) (hBC : Refines rB rC) : Refines rA rC := by
  intro x y hC
  exact hAB (hBC hC)

/-- Expanding currently available capability cannot invalidate a certificate. -/
theorem fiberSafe_of_capability_expansion
    {World : Type u} {Obs : Type v} {Action : Type w}
    {obs : World → Obs} {available₁ available₂ : Action → Prop}
    {admissible : World → Action → Prop} {x : World}
    (hcap : ∀ ⦃a : Action⦄, available₁ a → available₂ a)
    (hsafe : FiberSafe obs available₁ admissible x) :
    FiberSafe obs available₂ admissible x := by
  rcases hsafe with ⟨a, haAvail, ha⟩
  exact ⟨a, hcap haAvail, ha⟩

/-- If two worlds are observationally aliased and every available action fails
    on at least one of them, the fiber cannot be certified ACT. -/
theorem not_fiberSafe_of_alias_conflict
    {World : Type u} {Obs : Type v} {Action : Type w}
    {obs : World → Obs} {available : Action → Prop}
    {admissible : World → Action → Prop} {x y : World}
    (halias : obs y = obs x)
    (hconflict : ∀ a, available a → ¬ (admissible x a ∧ admissible y a)) :
    ¬ FiberSafe obs available admissible x := by
  intro hsafe
  rcases hsafe with ⟨a, haAvail, ha⟩
  have hx : admissible x a := ha rfl
  have hy : admissible y a := ha halias
  exact hconflict a haAvail ⟨hx, hy⟩

/-- A probe/refinement cannot turn a certified-safe fiber into an unsafe one. -/
theorem no_safe_to_unsafe_under_probe
    {World : Type u} {Coarse : Type v} {Fine : Type w} {Action : Type*}
    {coarse : World → Coarse} {fine : World → Fine}
    {available : Action → Prop} {admissible : World → Action → Prop}
    {x : World}
    (href : Refines coarse fine) :
    FiberSafe coarse available admissible x →
      FiberSafe fine available admissible x :=
  fiberSafe_of_refinement href

end InsacermoV13Kernel
