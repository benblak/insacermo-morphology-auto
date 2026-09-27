import InsacermoV13Kernel.SeparatorDecomposition

namespace InsacermoV13Kernel

universe uκ uι uW uO uA

/-- Observation of an arbitrary family of components sharing one exactly
    observed separator context. -/
def FamilySeparatorObs
    {K : Type uκ} {I : Type uι}
    {World : Type uW} {Obs : Type uO}
    (obs : I → K → World → Obs) :
    K × (I → World) → K × (I → Obs) :=
  fun x => (x.1, fun i => obs i x.1 (x.2 i))

/-- A family action is available exactly when every component action is. -/
def FamilyAvailable
    {I : Type uι} {Action : Type uA}
    (available : I → Action → Prop) :
    (I → Action) → Prop :=
  fun a => ∀ i, available i (a i)

/-- Conditional independence given the separator context: once k is fixed,
    every component admissibility predicate depends only on its own local
    world and local action. -/
def FamilySeparatorAdmissible
    {K : Type uκ} {I : Type uι}
    {World : Type uW} {Action : Type uA}
    (admissible : I → K → World → Action → Prop) :
    K × (I → World) → (I → Action) → Prop :=
  fun x a => ∀ i, admissible i x.1 (x.2 i) (a i)

/-- Equality of family-separator observations preserves the shared context. -/
theorem familySeparatorObs_eq_implies_context_eq
    {K : Type uκ} {I : Type uι}
    {World : Type uW} {Obs : Type uO}
    {obs : I → K → World → Obs}
    {x y : K × (I → World)}
    (h : FamilySeparatorObs obs y = FamilySeparatorObs obs x) :
    y.1 = x.1 := by
  have hk :
      (FamilySeparatorObs obs y).1 =
        (FamilySeparatorObs obs x).1 :=
    congrArg (fun z => z.1) h
  simpa [FamilySeparatorObs] using hk

/-- Arbitrary-arity separator decomposition.
    If all coupling between components is mediated by an exactly observed
    context k, global safety is equivalent to local safety of every component
    in every context. -/
theorem globalSafe_family_separator_iff
    {K : Type uκ} {I : Type uι}
    {World : Type uW} {Obs : Type uO} {Action : Type uA}
    [Nonempty World]
    {obs : I → K → World → Obs}
    {available : I → Action → Prop}
    {admissible : I → K → World → Action → Prop} :
    GlobalSafe
        (FamilySeparatorObs obs)
        (FamilyAvailable available)
        (FamilySeparatorAdmissible admissible)
      ↔
    (∀ k i,
      GlobalSafe (obs i k) (available i) (admissible i k)) := by
  classical
  constructor
  · intro hglobal k i
    intro x
    let base : I → World :=
      fun _ => Classical.choice (inferInstance : Nonempty World)
    let xv : I → World :=
      fun j => if h : j = i then h ▸ x else base j
    rcases hglobal (k, xv) with ⟨a, ha, hall⟩
    refine ⟨a i, ha i, ?_⟩
    intro y hy
    let yv : I → World :=
      fun j => if h : j = i then h ▸ y else base j
    have hobs :
        FamilySeparatorObs obs (k, yv) =
          FamilySeparatorObs obs (k, xv) := by
      apply Prod.ext rfl
      funext j
      by_cases hji : j = i
      · subst j
        simp [FamilySeparatorObs, xv, yv, hy]
      · simp [FamilySeparatorObs, xv, yv, hji]
    have hAdm :
        FamilySeparatorAdmissible admissible (k, yv) a :=
      hall hobs
    have hi : yv i = y := by
      simp [yv]
    simpa [FamilySeparatorAdmissible, hi] using hAdm i
  · intro hlocal
    intro x
    have hcert :
        ∀ i, ∃ a,
          available i a ∧
          ∀ ⦃y : World⦄,
            obs i x.1 y = obs i x.1 (x.2 i) →
              admissible i x.1 y a := by
      intro i
      exact hlocal x.1 i (x.2 i)
    let a : I → Action :=
      fun i => Classical.choose (hcert i)
    have ha :
        ∀ i, available i (a i) := by
      intro i
      exact (Classical.choose_spec (hcert i)).1
    have hall :
        ∀ i ⦃y : World⦄,
          obs i x.1 y = obs i x.1 (x.2 i) →
            admissible i x.1 y (a i) := by
      intro i y hy
      exact (Classical.choose_spec (hcert i)).2 hy
    refine ⟨a, ?_, ?_⟩
    · exact ha
    · intro y hy
      have hk : y.1 = x.1 :=
        familySeparatorObs_eq_implies_context_eq hy
      intro i
      have hcomponentRaw :
          (FamilySeparatorObs obs y).2 i =
            (FamilySeparatorObs obs x).2 i :=
        congrArg (fun z => z.2 i) hy
      have hcomponent :
          obs i x.1 (y.2 i) =
            obs i x.1 (x.2 i) := by
        simpa [FamilySeparatorObs, hk] using hcomponentRaw
      have hadm :
          admissible i x.1 (y.2 i) (a i) :=
        hall i hcomponent
      simpa [hk] using hadm

/-- Finite family specialization: n components coupled only through the
    visible separator reduce exactly to n local safety obligations per context. -/
theorem globalSafe_fin_family_separator_iff
    {K : Type uκ} {n : Nat}
    {World : Type uW} {Obs : Type uO} {Action : Type uA}
    [Nonempty World]
    {obs : Fin n → K → World → Obs}
    {available : Fin n → Action → Prop}
    {admissible : Fin n → K → World → Action → Prop} :
    GlobalSafe
        (FamilySeparatorObs obs)
        (FamilyAvailable available)
        (FamilySeparatorAdmissible admissible)
      ↔
    (∀ k i,
      GlobalSafe (obs i k) (available i) (admissible i k)) := by
  exact globalSafe_family_separator_iff

/-- The empty family is always globally safe: with no local obligations there
    is a unique empty action vector and no admissibility condition to violate. -/
theorem globalSafe_empty_family
    {K : Type uκ}
    {World : Type uW} {Obs : Type uO} {Action : Type uA}
    [Nonempty World]
    {obs : Fin 0 → K → World → Obs}
    {available : Fin 0 → Action → Prop}
    {admissible : Fin 0 → K → World → Action → Prop} :
    GlobalSafe
      (FamilySeparatorObs obs)
      (FamilyAvailable available)
      (FamilySeparatorAdmissible admissible) := by
  rw [globalSafe_fin_family_separator_iff]
  intro k i
  exact Fin.elim0 i

/-- One local component per context is exactly the corresponding local
    GlobalSafe obligation. -/
theorem globalSafe_singleton_family_iff
    {K : Type uκ}
    {World : Type uW} {Obs : Type uO} {Action : Type uA}
    [Nonempty World]
    {obs : Fin 1 → K → World → Obs}
    {available : Fin 1 → Action → Prop}
    {admissible : Fin 1 → K → World → Action → Prop} :
    GlobalSafe
        (FamilySeparatorObs obs)
        (FamilyAvailable available)
        (FamilySeparatorAdmissible admissible)
      ↔
    (∀ k,
      GlobalSafe (obs 0 k) (available 0) (admissible 0 k)) := by
  rw [globalSafe_fin_family_separator_iff]
  constructor
  · intro h k
    exact h k 0
  · intro h k i
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    simpa [hi] using h k

end InsacermoV13Kernel
