import InsacermoV13Kernel.FrontierFactorization

namespace InsacermoV13Kernel

universe uκ uL uR vL vR wL wR

/-- A separator-aware observation records the shared context exactly and
    keeps separate observations for the left and right subsystems. -/
def SeparatorObs
    {K : Type uκ} {Left : Type uL} {Right : Type uR}
    {ObsL : Type vL} {ObsR : Type vR}
    (obsL : K → Left → ObsL)
    (obsR : K → Right → ObsR) :
    K × (Left × Right) → K × (ObsL × ObsR) :=
  fun x => (x.1, (obsL x.1 x.2.1, obsR x.1 x.2.2))

/-- Separator-aware admissibility: after conditioning on the same shared
    context k, the left and right action constraints are independent. -/
def SeparatorAdmissible
    {K : Type uκ} {Left : Type uL} {Right : Type uR}
    {ActionL : Type wL} {ActionR : Type wR}
    (admissibleL : K → Left → ActionL → Prop)
    (admissibleR : K → Right → ActionR → Prop) :
    K × (Left × Right) → ActionL × ActionR → Prop :=
  fun x a =>
    admissibleL x.1 x.2.1 a.1 ∧
      admissibleR x.1 x.2.2 a.2

/-- Equality of separator-aware observations cannot cross separator contexts. -/
theorem separatorObs_eq_implies_context_eq
    {K : Type uκ} {Left : Type uL} {Right : Type uR}
    {ObsL : Type vL} {ObsR : Type vR}
    {obsL : K → Left → ObsL}
    {obsR : K → Right → ObsR}
    {x y : K × (Left × Right)}
    (h :
      SeparatorObs obsL obsR y =
        SeparatorObs obsL obsR x) :
    y.1 = x.1 := by
  exact congrArg Prod.fst h

/-- Exact separator decomposition.
    When the separator context is observed exactly, and left/right admissibility
    only couple through that context, global safety is equivalent to solving
    both sides independently for every separator value. -/
theorem globalSafe_separator_iff
    {K : Type uκ} {Left : Type uL} {Right : Type uR}
    {ObsL : Type vL} {ObsR : Type vR}
    {ActionL : Type wL} {ActionR : Type wR}
    [Nonempty Left] [Nonempty Right]
    {obsL : K → Left → ObsL}
    {obsR : K → Right → ObsR}
    {availableL : ActionL → Prop}
    {availableR : ActionR → Prop}
    {admissibleL : K → Left → ActionL → Prop}
    {admissibleR : K → Right → ActionR → Prop} :
    GlobalSafe
        (SeparatorObs obsL obsR)
        (ProductAvailable availableL availableR)
        (SeparatorAdmissible admissibleL admissibleR)
      ↔
    (∀ k,
      GlobalSafe (obsL k) availableL (admissibleL k) ∧
      GlobalSafe (obsR k) availableR (admissibleR k)) := by
  constructor
  · intro hglobal k
    constructor
    · intro xL
      let xR : Right := Classical.choice (inferInstance : Nonempty Right)
      rcases hglobal (k, (xL, xR)) with ⟨a, ha, hall⟩
      refine ⟨a.1, ha.1, ?_⟩
      intro yL hyL
      have hobs :
          SeparatorObs obsL obsR (k, (yL, xR)) =
            SeparatorObs obsL obsR (k, (xL, xR)) := by
        simp [SeparatorObs, hyL]
      exact (hall hobs).1
    · intro xR
      let xL : Left := Classical.choice (inferInstance : Nonempty Left)
      rcases hglobal (k, (xL, xR)) with ⟨a, ha, hall⟩
      refine ⟨a.2, ha.2, ?_⟩
      intro yR hyR
      have hobs :
          SeparatorObs obsL obsR (k, (xL, yR)) =
            SeparatorObs obsL obsR (k, (xL, xR)) := by
        simp [SeparatorObs, hyR]
      exact (hall hobs).2
  · intro hlocal
    intro x
    rcases hlocal x.1 with ⟨hL, hR⟩
    rcases hL x.2.1 with ⟨aL, haL, hallL⟩
    rcases hR x.2.2 with ⟨aR, haR, hallR⟩
    refine ⟨(aL, aR), ⟨haL, haR⟩, ?_⟩
    intro y hy
    have hk : y.1 = x.1 :=
      separatorObs_eq_implies_context_eq hy
    have hyL :
        obsL x.1 y.2.1 = obsL x.1 x.2.1 := by
      have hleft :
          (SeparatorObs obsL obsR y).2.1 =
            (SeparatorObs obsL obsR x).2.1 :=
        congrArg (fun z => z.2.1) hy
      simpa [SeparatorObs, hk] using hleft
    have hyR :
        obsR x.1 y.2.2 = obsR x.1 x.2.2 := by
      have hright :
          (SeparatorObs obsL obsR y).2.2 =
            (SeparatorObs obsL obsR x).2.2 :=
        congrArg (fun z => z.2.2) hy
      simpa [SeparatorObs, hk] using hright
    have hAdmLx : admissibleL x.1 y.2.1 aL :=
      hallL hyL
    have hAdmRx : admissibleR x.1 y.2.2 aR :=
      hallR hyR
    simpa [SeparatorAdmissible, hk] using And.intro hAdmLx hAdmRx

/-- Finite-separator specialization. A separator with k visible contexts
    reduces the global safety question to exactly k context-indexed pairs of
    local safety obligations. -/
theorem globalSafe_fin_separator_iff
    {k : Nat}
    {Left : Type uL} {Right : Type uR}
    {ObsL : Type vL} {ObsR : Type vR}
    {ActionL : Type wL} {ActionR : Type wR}
    [Nonempty Left] [Nonempty Right]
    {obsL : Fin k → Left → ObsL}
    {obsR : Fin k → Right → ObsR}
    {availableL : ActionL → Prop}
    {availableR : ActionR → Prop}
    {admissibleL : Fin k → Left → ActionL → Prop}
    {admissibleR : Fin k → Right → ActionR → Prop} :
    GlobalSafe
        (SeparatorObs obsL obsR)
        (ProductAvailable availableL availableR)
        (SeparatorAdmissible admissibleL admissibleR)
      ↔
    (∀ i : Fin k,
      GlobalSafe (obsL i) availableL (admissibleL i) ∧
      GlobalSafe (obsR i) availableR (admissibleR i)) := by
  exact globalSafe_separator_iff

/-- The one-context case collapses to ordinary product factorization. This
    makes the previous factorization theorem the width-zero boundary case of
    separator decomposition. -/
theorem globalSafe_single_separator_iff
    {Left : Type uL} {Right : Type uR}
    {ObsL : Type vL} {ObsR : Type vR}
    {ActionL : Type wL} {ActionR : Type wR}
    [Nonempty Left] [Nonempty Right]
    {obsL : Unit → Left → ObsL}
    {obsR : Unit → Right → ObsR}
    {availableL : ActionL → Prop}
    {availableR : ActionR → Prop}
    {admissibleL : Unit → Left → ActionL → Prop}
    {admissibleR : Unit → Right → ActionR → Prop} :
    GlobalSafe
        (SeparatorObs obsL obsR)
        (ProductAvailable availableL availableR)
        (SeparatorAdmissible admissibleL admissibleR)
      ↔
    GlobalSafe (obsL ()) availableL (admissibleL ()) ∧
      GlobalSafe (obsR ()) availableR (admissibleR ()) := by
  rw [globalSafe_separator_iff]
  constructor
  · intro h
    exact h ()
  · intro h k
    cases k
    exact h

/-- Context-indexed product feasibility region. -/
def SeparatorRegion
    {K : Type uκ} {P₁ : Type uL} {P₂ : Type uR}
    (U₁ : K → P₁ → Prop)
    (U₂ : K → P₂ → Prop) :
    K × (P₁ × P₂) → Prop :=
  fun p => U₁ p.1 p.2.1 ∧ U₂ p.1 p.2.2

/-- Separator-preserving order: resource comparison is permitted only inside
    the same separator context. -/
def SeparatorLe
    {K : Type uκ} {P₁ : Type uL} {P₂ : Type uR}
    (le₁ : K → P₁ → P₁ → Prop)
    (le₂ : K → P₂ → P₂ → Prop) :
    K × (P₁ × P₂) → K × (P₁ × P₂) → Prop :=
  fun p q =>
    p.1 = q.1 ∧
      le₁ p.1 p.2.1 q.2.1 ∧
      le₂ p.1 p.2.2 q.2.2

/-- If every separator slice is upward closed, the glued region is upward
    closed for the separator-preserving order. -/
theorem separatorRegion_upperClosed
    {K : Type uκ} {P₁ : Type uL} {P₂ : Type uR}
    {U₁ : K → P₁ → Prop}
    {U₂ : K → P₂ → Prop}
    {le₁ : K → P₁ → P₁ → Prop}
    {le₂ : K → P₂ → P₂ → Prop}
    (h₁ : ∀ k, UpperClosed (U₁ k) (le₁ k))
    (h₂ : ∀ k, UpperClosed (U₂ k) (le₂ k)) :
    UpperClosed
      (SeparatorRegion U₁ U₂)
      (SeparatorLe le₁ le₂) := by
  intro p q hp hpq
  have hk : p.1 = q.1 := hpq.1
  subst q
  exact
    ⟨h₁ p.1 hp.1 hpq.2.1,
     h₂ p.1 hp.2 hpq.2.2⟩

/-- Exact slice-wise characterization of generated upper regions under a
    separator-preserving resource order. -/
theorem generatedUpper_separator_iff
    {K : Type uκ} {P₁ : Type uL} {P₂ : Type uR}
    {seed₁ : K → P₁ → Prop}
    {seed₂ : K → P₂ → Prop}
    {le₁ : K → P₁ → P₁ → Prop}
    {le₂ : K → P₂ → P₂ → Prop}
    {p : K × (P₁ × P₂)} :
    GeneratedUpper
        (SeparatorRegion seed₁ seed₂)
        (SeparatorLe le₁ le₂)
        p
      ↔
    GeneratedUpper (seed₁ p.1) (le₁ p.1) p.2.1 ∧
      GeneratedUpper (seed₂ p.1) (le₂ p.1) p.2.2 := by
  constructor
  · rintro ⟨a, ha, hap⟩
    have hk : a.1 = p.1 := hap.1
    subst a
    exact
      ⟨⟨p.2.1, ha.1, hap.2.1⟩,
       ⟨p.2.2, ha.2, hap.2.2⟩⟩
  · rintro ⟨⟨a₁, ha₁, hap₁⟩, ⟨a₂, ha₂, hap₂⟩⟩
    exact
      ⟨(p.1, (a₁, a₂)),
       ⟨ha₁, ha₂⟩,
       ⟨rfl, hap₁, hap₂⟩⟩

end InsacermoV13Kernel
