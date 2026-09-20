import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

namespace InsacermoActionabilityInformation

/--
A finite-horizon future query is represented by a time offset and a state predicate.
The query names are abstract; the same query index is transported across conjugate systems.
-/
structure FutureQuery (Q : Type*) (X : Type*) where
  name : Q
  time : Nat
  pred : X → Prop

/-- Satisfaction of a future query from initial state x under dynamics f. -/
def Satisfies {Q X : Type*} (f : X → X) (q : FutureQuery Q X) (x : X) : Prop :=
  q.pred ((f^[q.time]) x)

/--
A finite bundle of named future requirements is feasible when one initial state
realizes every named query in the bundle.
-/
def BundleFeasible
    {Q X : Type*} [DecidableEq Q]
    (f : X → X) (queries : Q → FutureQuery Q X)
    (F : Finset Q) : Prop :=
  ∃ x : X, ∀ q ∈ F, Satisfies f (queries q) x

/--
Minimal obstruction: the full bundle is infeasible, but deleting any one member
makes it feasible.
-/
def MinimalObstruction
    {Q X : Type*} [DecidableEq Q]
    (f : X → X) (queries : Q → FutureQuery Q X)
    (F : Finset Q) : Prop :=
  ¬ BundleFeasible f queries F ∧
  ∀ q ∈ F, BundleFeasible f queries (F.erase q)

/--
Facet of the finite feasible-bundle complex relative to a declared finite query universe U.
-/
def FeasibleFacet
    {Q X : Type*} [DecidableEq Q]
    (f : X → X) (queries : Q → FutureQuery Q X)
    (U F : Finset Q) : Prop :=
  F ⊆ U ∧
  BundleFeasible f queries F ∧
  ∀ G : Finset Q, F ⊂ G → G ⊆ U → ¬ BundleFeasible f queries G

/-- Iteration commutes with a conjugacy. -/
theorem iterate_conjugacy
    {X Y : Type*}
    (e : X ≃ Y) (f : X → X) (g : Y → Y)
    (hconj : ∀ x, e (f x) = g (e x)) :
    ∀ n x, e ((f^[n]) x) = (g^[n]) (e x) := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      simp only [Function.iterate_succ_apply]
      rw [hconj]
      exact congrArg g (ih x)

/--
General transport theorem for one future query under a dynamical conjugacy,
provided the query predicate is transported by the same equivalence.
-/
theorem satisfies_conjugacy
    {Q X Y : Type*}
    (e : X ≃ Y) (f : X → X) (g : Y → Y)
    (qx : FutureQuery Q X) (qy : FutureQuery Q Y)
    (same_time : qx.time = qy.time)
    (hconj : ∀ x, e (f x) = g (e x))
    (hpred : ∀ x, qx.pred x ↔ qy.pred (e x)) :
    ∀ x, Satisfies f qx x ↔ Satisfies g qy (e x) := by
  intro x
  unfold Satisfies
  subst same_time
  rw [← iterate_conjugacy e f g hconj qy.time x]
  exact hpred ((f^[qy.time]) x)

/--
MAIN V2 CONJUGACY THEOREM.

If two dynamical systems are conjugate and every declared future query is
transported by that conjugacy with the same time offset, then every finite
future bundle has exactly the same feasibility status in both systems.
-/
theorem future_bundle_feasibility_conjugacy
    {Q X Y : Type*} [DecidableEq Q]
    (e : X ≃ Y) (f : X → X) (g : Y → Y)
    (qx : Q → FutureQuery Q X) (qy : Q → FutureQuery Q Y)
    (hconj : ∀ x, e (f x) = g (e x))
    (htime : ∀ q, (qx q).time = (qy q).time)
    (hpred : ∀ q x, (qx q).pred x ↔ (qy q).pred (e x)) :
    ∀ F : Finset Q,
      BundleFeasible f qx F ↔ BundleFeasible g qy F := by
  intro F
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    intro q hq
    exact (satisfies_conjugacy e f g (qx q) (qy q)
      (htime q) hconj (hpred q) x).mp (hx q hq)
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    intro q hq
    have hs := (satisfies_conjugacy e f g (qx q) (qy q)
      (htime q) hconj (hpred q) (e.symm y))
    simpa using hs.mpr (hy q hq)

/-- Minimal obstruction certificates are invariant under transported conjugacy. -/
theorem minimal_obstruction_conjugacy
    {Q X Y : Type*} [DecidableEq Q]
    (e : X ≃ Y) (f : X → X) (g : Y → Y)
    (qx : Q → FutureQuery Q X) (qy : Q → FutureQuery Q Y)
    (hconj : ∀ x, e (f x) = g (e x))
    (htime : ∀ q, (qx q).time = (qy q).time)
    (hpred : ∀ q x, (qx q).pred x ↔ (qy q).pred (e x)) :
    ∀ F : Finset Q,
      MinimalObstruction f qx F ↔ MinimalObstruction g qy F := by
  intro F
  unfold MinimalObstruction
  constructor
  · rintro ⟨hbad, hmin⟩
    constructor
    · intro hgood
      exact hbad ((future_bundle_feasibility_conjugacy e f g qx qy hconj htime hpred F).mpr hgood)
    · intro q hq
      exact (future_bundle_feasibility_conjugacy e f g qx qy hconj htime hpred (F.erase q)).mp
        (hmin q hq)
  · rintro ⟨hbad, hmin⟩
    constructor
    · intro hgood
      exact hbad ((future_bundle_feasibility_conjugacy e f g qx qy hconj htime hpred F).mp hgood)
    · intro q hq
      exact (future_bundle_feasibility_conjugacy e f g qx qy hconj htime hpred (F.erase q)).mpr
        (hmin q hq)

/--
Maximal feasible faces (facets) relative to the same declared query universe
are invariant under transported conjugacy.
-/
theorem feasible_facet_conjugacy
    {Q X Y : Type*} [DecidableEq Q]
    (e : X ≃ Y) (f : X → X) (g : Y → Y)
    (qx : Q → FutureQuery Q X) (qy : Q → FutureQuery Q Y)
    (hconj : ∀ x, e (f x) = g (e x))
    (htime : ∀ q, (qx q).time = (qy q).time)
    (hpred : ∀ q x, (qx q).pred x ↔ (qy q).pred (e x)) :
    ∀ U F : Finset Q,
      FeasibleFacet f qx U F ↔ FeasibleFacet g qy U F := by
  intro U F
  unfold FeasibleFacet
  constructor
  · rintro ⟨hFU, hF, hmax⟩
    refine ⟨hFU, (future_bundle_feasibility_conjugacy e f g qx qy hconj htime hpred F).mp hF, ?_⟩
    intro G hFG hGU hG
    exact hmax G hFG hGU
      ((future_bundle_feasibility_conjugacy e f g qx qy hconj htime hpred G).mpr hG)
  · rintro ⟨hFU, hF, hmax⟩
    refine ⟨hFU, (future_bundle_feasibility_conjugacy e f g qx qy hconj htime hpred F).mpr hF, ?_⟩
    intro G hFG hGU hG
    exact hmax G hFG hGU
      ((future_bundle_feasibility_conjugacy e f g qx qy hconj htime hpred G).mp hG)

/--
Corollary: the complete finite feasible-bundle complex is identical under
transported dynamical conjugacy.
-/
theorem future_complex_extensional_invariance
    {Q X Y : Type*} [DecidableEq Q]
    (e : X ≃ Y) (f : X → X) (g : Y → Y)
    (qx : Q → FutureQuery Q X) (qy : Q → FutureQuery Q Y)
    (hconj : ∀ x, e (f x) = g (e x))
    (htime : ∀ q, (qx q).time = (qy q).time)
    (hpred : ∀ q x, (qx q).pred x ↔ (qy q).pred (e x)) :
    {F : Finset Q | BundleFeasible f qx F}
      =
    {F : Finset Q | BundleFeasible g qy F} := by
  ext F
  exact future_bundle_feasibility_conjugacy e f g qx qy hconj htime hpred F

end InsacermoActionabilityInformation
