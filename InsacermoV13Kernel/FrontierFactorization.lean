import InsacermoV13Kernel.FrontierUniversality

namespace InsacermoV13Kernel

universe u₁ u₂ v₁ v₂ w₁ w₂

/-- Componentwise observation on an independent product system. -/
def ProductObs
    {World₁ : Type u₁} {World₂ : Type u₂}
    {Obs₁ : Type v₁} {Obs₂ : Type v₂}
    (obs₁ : World₁ → Obs₁) (obs₂ : World₂ → Obs₂) :
    World₁ × World₂ → Obs₁ × Obs₂ :=
  fun x => (obs₁ x.1, obs₂ x.2)

/-- A product action is available exactly when both component actions are available. -/
def ProductAvailable
    {Action₁ : Type w₁} {Action₂ : Type w₂}
    (available₁ : Action₁ → Prop) (available₂ : Action₂ → Prop) :
    Action₁ × Action₂ → Prop :=
  fun a => available₁ a.1 ∧ available₂ a.2

/-- Independent admissibility: each component action is judged only against
    its own component world. This is the no-hidden-coupling hypothesis. -/
def ProductAdmissible
    {World₁ : Type u₁} {World₂ : Type u₂}
    {Action₁ : Type w₁} {Action₂ : Type w₂}
    (admissible₁ : World₁ → Action₁ → Prop)
    (admissible₂ : World₂ → Action₂ → Prop) :
    World₁ × World₂ → Action₁ × Action₂ → Prop :=
  fun x a => admissible₁ x.1 a.1 ∧ admissible₂ x.2 a.2

/-- Exact operational factorization.
    For nonempty independent components, the product system is globally safe
    iff every component system is globally safe. -/
theorem globalSafe_product_iff
    {World₁ : Type u₁} {World₂ : Type u₂}
    {Obs₁ : Type v₁} {Obs₂ : Type v₂}
    {Action₁ : Type w₁} {Action₂ : Type w₂}
    [Nonempty World₁] [Nonempty World₂]
    {obs₁ : World₁ → Obs₁} {obs₂ : World₂ → Obs₂}
    {available₁ : Action₁ → Prop} {available₂ : Action₂ → Prop}
    {admissible₁ : World₁ → Action₁ → Prop}
    {admissible₂ : World₂ → Action₂ → Prop} :
    GlobalSafe
        (ProductObs obs₁ obs₂)
        (ProductAvailable available₁ available₂)
        (ProductAdmissible admissible₁ admissible₂)
      ↔
    GlobalSafe obs₁ available₁ admissible₁ ∧
      GlobalSafe obs₂ available₂ admissible₂ := by
  constructor
  · intro hprod
    constructor
    · intro x₁
      let x₂ : World₂ := Classical.choice (inferInstance : Nonempty World₂)
      rcases hprod (x₁, x₂) with ⟨a, ha, hall⟩
      refine ⟨a.1, ha.1, ?_⟩
      intro y₁ hy₁
      have hpair :
          ProductObs obs₁ obs₂ (y₁, x₂) =
            ProductObs obs₁ obs₂ (x₁, x₂) := by
        simp [ProductObs, hy₁]
      exact (hall hpair).1
    · intro x₂
      let x₁ : World₁ := Classical.choice (inferInstance : Nonempty World₁)
      rcases hprod (x₁, x₂) with ⟨a, ha, hall⟩
      refine ⟨a.2, ha.2, ?_⟩
      intro y₂ hy₂
      have hpair :
          ProductObs obs₁ obs₂ (x₁, y₂) =
            ProductObs obs₁ obs₂ (x₁, x₂) := by
        simp [ProductObs, hy₂]
      exact (hall hpair).2
  · rintro ⟨h₁, h₂⟩
    intro x
    rcases h₁ x.1 with ⟨a₁, ha₁, hall₁⟩
    rcases h₂ x.2 with ⟨a₂, ha₂, hall₂⟩
    refine ⟨(a₁, a₂), ⟨ha₁, ha₂⟩, ?_⟩
    intro y hy
    have hy₁ : obs₁ y.1 = obs₁ x.1 := by
      simpa [ProductObs] using congrArg Prod.fst hy
    have hy₂ : obs₂ y.2 = obs₂ x.2 := by
      simpa [ProductObs] using congrArg Prod.snd hy
    exact ⟨hall₁ hy₁, hall₂ hy₂⟩

/-- Product feasibility region. -/
def ProductRegion
    {P₁ : Type u₁} {P₂ : Type u₂}
    (U₁ : P₁ → Prop) (U₂ : P₂ → Prop) :
    P₁ × P₂ → Prop :=
  fun p => U₁ p.1 ∧ U₂ p.2

/-- Componentwise resource order. -/
def ProductLe
    {P₁ : Type u₁} {P₂ : Type u₂}
    (le₁ : P₁ → P₁ → Prop) (le₂ : P₂ → P₂ → Prop) :
    P₁ × P₂ → P₁ × P₂ → Prop :=
  fun p q => le₁ p.1 q.1 ∧ le₂ p.2 q.2

/-- Upper-closed feasibility is preserved by independent products. -/
theorem productRegion_upperClosed
    {P₁ : Type u₁} {P₂ : Type u₂}
    {U₁ : P₁ → Prop} {U₂ : P₂ → Prop}
    {le₁ : P₁ → P₁ → Prop} {le₂ : P₂ → P₂ → Prop}
    (h₁ : UpperClosed U₁ le₁)
    (h₂ : UpperClosed U₂ le₂) :
    UpperClosed (ProductRegion U₁ U₂) (ProductLe le₁ le₂) := by
  intro p q hp hpq
  exact ⟨h₁ hp.1 hpq.1, h₂ hp.2 hpq.2⟩

/-- Generated upper regions factor exactly across independent components. -/
theorem generatedUpper_product_iff
    {P₁ : Type u₁} {P₂ : Type u₂}
    {seed₁ : P₁ → Prop} {seed₂ : P₂ → Prop}
    {le₁ : P₁ → P₁ → Prop} {le₂ : P₂ → P₂ → Prop}
    {p : P₁ × P₂} :
    GeneratedUpper
        (ProductRegion seed₁ seed₂)
        (ProductLe le₁ le₂)
        p
      ↔
    GeneratedUpper seed₁ le₁ p.1 ∧
      GeneratedUpper seed₂ le₂ p.2 := by
  constructor
  · rintro ⟨a, ha, hap⟩
    exact
      ⟨⟨a.1, ha.1, hap.1⟩,
       ⟨a.2, ha.2, hap.2⟩⟩
  · rintro ⟨⟨a₁, ha₁, hap₁⟩, ⟨a₂, ha₂, hap₂⟩⟩
    exact
      ⟨(a₁, a₂),
       ⟨ha₁, ha₂⟩,
       ⟨hap₁, hap₂⟩⟩

/-- Minimal frontier points factor exactly across independent components.
    Reflexivity is needed only to hold the untouched coordinate fixed while
    testing minimality in the other coordinate. -/
theorem minimalGenerated_product_iff
    {P₁ : Type u₁} {P₂ : Type u₂}
    {seed₁ : P₁ → Prop} {seed₂ : P₂ → Prop}
    {le₁ : P₁ → P₁ → Prop} {le₂ : P₂ → P₂ → Prop}
    (hrefl₁ : ∀ p : P₁, le₁ p p)
    (hrefl₂ : ∀ p : P₂, le₂ p p)
    {p : P₁ × P₂} :
    MinimalGenerated
        (ProductRegion seed₁ seed₂)
        (ProductLe le₁ le₂)
        p
      ↔
    MinimalGenerated seed₁ le₁ p.1 ∧
      MinimalGenerated seed₂ le₂ p.2 := by
  constructor
  · intro hp
    have hgen :
        GeneratedUpper seed₁ le₁ p.1 ∧
          GeneratedUpper seed₂ le₂ p.2 :=
      generatedUpper_product_iff.mp hp.1
    constructor
    · refine ⟨hgen.1, ?_⟩
      intro q₁ hq₁ hq₁p
      have hqProd :
          GeneratedUpper
            (ProductRegion seed₁ seed₂)
            (ProductLe le₁ le₂)
            (q₁, p.2) :=
        generatedUpper_product_iff.mpr ⟨hq₁, hgen.2⟩
      have hleProd :
          ProductLe le₁ le₂ (q₁, p.2) p :=
        ⟨hq₁p, hrefl₂ p.2⟩
      exact (hp.2 hqProd hleProd).1
    · refine ⟨hgen.2, ?_⟩
      intro q₂ hq₂ hq₂p
      have hqProd :
          GeneratedUpper
            (ProductRegion seed₁ seed₂)
            (ProductLe le₁ le₂)
            (p.1, q₂) :=
        generatedUpper_product_iff.mpr ⟨hgen.1, hq₂⟩
      have hleProd :
          ProductLe le₁ le₂ (p.1, q₂) p :=
        ⟨hrefl₁ p.1, hq₂p⟩
      exact (hp.2 hqProd hleProd).2
  · rintro ⟨hp₁, hp₂⟩
    refine ⟨generatedUpper_product_iff.mpr ⟨hp₁.1, hp₂.1⟩, ?_⟩
    intro q hq hqp
    have hqSplit :
        GeneratedUpper seed₁ le₁ q.1 ∧
          GeneratedUpper seed₂ le₂ q.2 :=
      generatedUpper_product_iff.mp hq
    exact
      ⟨hp₁.2 hqSplit.1 hqp.1,
       hp₂.2 hqSplit.2 hqp.2⟩

/-- Additive resource cost on a product system. -/
def AdditiveCost
    {P₁ : Type u₁} {P₂ : Type u₂}
    (cost₁ : P₁ → Nat) (cost₂ : P₂ → Nat) :
    P₁ × P₂ → Nat :=
  fun p => cost₁ p.1 + cost₂ p.2

/-- Exact optimization decomposition without introducing an argmin operator:
    componentwise lower bounds and attaining witnesses combine into a global
    optimal witness for the product region. -/
theorem additiveCost_product_optimal
    {P₁ : Type u₁} {P₂ : Type u₂}
    {U₁ : P₁ → Prop} {U₂ : P₂ → Prop}
    {cost₁ : P₁ → Nat} {cost₂ : P₂ → Nat}
    {m₁ m₂ : Nat}
    (hlower₁ : ∀ p₁, U₁ p₁ → m₁ ≤ cost₁ p₁)
    (hlower₂ : ∀ p₂, U₂ p₂ → m₂ ≤ cost₂ p₂)
    (hattain₁ : ∃ p₁, U₁ p₁ ∧ cost₁ p₁ = m₁)
    (hattain₂ : ∃ p₂, U₂ p₂ ∧ cost₂ p₂ = m₂) :
    ∃ p : P₁ × P₂,
      ProductRegion U₁ U₂ p ∧
      AdditiveCost cost₁ cost₂ p = m₁ + m₂ ∧
      ∀ q : P₁ × P₂,
        ProductRegion U₁ U₂ q →
          AdditiveCost cost₁ cost₂ p ≤ AdditiveCost cost₁ cost₂ q := by
  rcases hattain₁ with ⟨p₁, hp₁, hcost₁⟩
  rcases hattain₂ with ⟨p₂, hp₂, hcost₂⟩
  refine ⟨(p₁, p₂), ⟨hp₁, hp₂⟩, ?_, ?_⟩
  · simp [AdditiveCost, hcost₁, hcost₂]
  · intro q hq
    have h₁ : m₁ ≤ cost₁ q.1 := hlower₁ q.1 hq.1
    have h₂ : m₂ ≤ cost₂ q.2 := hlower₂ q.2 hq.2
    simpa [AdditiveCost, hcost₁, hcost₂] using Nat.add_le_add h₁ h₂

/-- The product of two monotone component regions has an exact one-world
    INSACERMO realization and its safety predicate is precisely the conjunction
    of the two component predicates. -/
theorem factorized_upper_region_realizable
    {P₁ : Type u₁} {P₂ : Type u₂}
    {U₁ : P₁ → Prop} {U₂ : P₂ → Prop}
    {le₁ : P₁ → P₁ → Prop} {le₂ : P₂ → P₂ → Prop}
    (hrefl₁ : ∀ p : P₁, le₁ p p)
    (hrefl₂ : ∀ p : P₂, le₂ p p)
    (hupper₁ : UpperClosed U₁ le₁)
    (hupper₂ : UpperClosed U₂ le₂)
    {p : P₁ × P₂} :
    GlobalSafe
        FrontierRealization.obs
        (FrontierRealization.availableAt
          (ProductRegion U₁ U₂)
          (ProductLe le₁ le₂)
          p)
        FrontierRealization.admissible
      ↔
    U₁ p.1 ∧ U₂ p.2 := by
  have hrefl :
      ∀ q : P₁ × P₂, ProductLe le₁ le₂ q q := by
    intro q
    exact ⟨hrefl₁ q.1, hrefl₂ q.2⟩
  have hupper :
      UpperClosed
        (ProductRegion U₁ U₂)
        (ProductLe le₁ le₂) :=
    productRegion_upperClosed hupper₁ hupper₂
  exact
    FrontierRealization.arbitrary_upper_region_realizable
      hrefl hupper

end InsacermoV13Kernel
