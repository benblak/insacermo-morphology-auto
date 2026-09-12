import InsacermoActionabilityInformation.BeliefBellmanPlanner

namespace InsacermoActionabilityInformation

/-- Expected continuation value under an exact finite rational transition law. -/
noncomputable def expectedNext
    {X A : Type*} [Fintype X]
    (P : X → A → FiniteLaw X) (x : X) (a : A) (V : X → ℝ) : ℝ :=
  Finset.univ.sum (fun y => ((P x a).mass y : ℝ) * V y)

/-- A normalized finite transition law is 1-Lipschitz for uniform pointwise
value perturbations. -/
theorem expectedNext_uniform_close
    {X A : Type*} [Fintype X]
    (P : X → A → FiniteLaw X) (x : X) (a : A)
    (V W : X → ℝ) (delta : ℝ)
    (hdelta : ∀ y, |V y - W y| ≤ delta) :
    |expectedNext P x a V - expectedNext P x a W| ≤ delta := by
  classical
  have hmass_nonneg : ∀ y, 0 ≤ ((P x a).mass y : ℝ) := by
    intro y
    exact_mod_cast (P x a).nonneg y
  have hmass_one : Finset.univ.sum (fun y => ((P x a).mass y : ℝ)) = 1 := by
    exact_mod_cast (P x a).total_one
  have hdiff :
      expectedNext P x a V - expectedNext P x a W =
        Finset.univ.sum (fun y => ((P x a).mass y : ℝ) * (V y - W y)) := by
    simp [expectedNext, Finset.sum_sub_distrib, mul_sub]
  apply abs_le.mpr
  constructor
  · rw [hdiff]
    calc
      -delta = Finset.univ.sum (fun y => ((P x a).mass y : ℝ) * (-delta)) := by
        rw [← Finset.sum_mul, hmass_one, one_mul]
      _ ≤ Finset.univ.sum
          (fun y => ((P x a).mass y : ℝ) * (V y - W y)) := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_left (abs_le.mp (hdelta y)).1 (hmass_nonneg y)
  · rw [hdiff]
    calc
      Finset.univ.sum (fun y => ((P x a).mass y : ℝ) * (V y - W y)) ≤
          Finset.univ.sum (fun y => ((P x a).mass y : ℝ) * delta) := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_left (abs_le.mp (hdelta y)).2 (hmass_nonneg y)
      _ = delta := by
        rw [← Finset.sum_mul, hmass_one, one_mul]

/-- Discounted one-step Q-value on a finite closed decision-state graph. -/
noncomputable def infiniteQ
    {X A : Type*} [Fintype X]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma : ℝ) (V : X → ℝ) (x : X) (a : A) : ℝ :=
  stageCost x a + gamma * expectedNext P x a V

/-- Discounted Q-values inherit the discount factor as their uniform
Lipschitz constant. -/
theorem infiniteQ_uniform_close
    {X A : Type*} [Fintype X]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma delta : ℝ) (hgamma : 0 ≤ gamma)
    (V W : X → ℝ)
    (hdelta : ∀ y, |V y - W y| ≤ delta)
    (x : X) (a : A) :
    |infiniteQ P stageCost gamma V x a -
      infiniteQ P stageCost gamma W x a| ≤ gamma * delta := by
  have hexp := expectedNext_uniform_close P x a V W delta hdelta
  have hrewrite :
      infiniteQ P stageCost gamma V x a -
          infiniteQ P stageCost gamma W x a =
        gamma * (expectedNext P x a V - expectedNext P x a W) := by
    simp [infiniteQ]
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg hgamma]
  exact mul_le_mul_of_nonneg_left hexp hgamma

/-- Minimum of a real-valued family over a finite nonempty action type. -/
noncomputable def realActionMin
    {B A : Type*} [Fintype A] [Nonempty A]
    (Q : B → A → ℝ) (b : B) : ℝ :=
  (Finset.univ.image (fun a => Q b a)).min' (by simp)

/-- The real finite-action minimum is attained. -/
theorem exists_action_eq_realActionMin
    {B A : Type*} [Fintype A] [Nonempty A]
    (Q : B → A → ℝ) (b : B) :
    ∃ a : A, Q b a = realActionMin Q b := by
  classical
  have hmem : realActionMin Q b ∈ Finset.univ.image (fun a => Q b a) := by
    unfold realActionMin
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨a, ha, hEq⟩
  exact ⟨a, hEq⟩

/-- The real finite-action minimum is below every candidate value. -/
theorem realActionMin_le
    {B A : Type*} [Fintype A] [Nonempty A]
    (Q : B → A → ℝ) (b : B) (a : A) :
    realActionMin Q b ≤ Q b a := by
  classical
  unfold realActionMin
  apply Finset.min'_le
  simp

/-- Pointwise epsilon-close action-value families have epsilon-close minima. -/
theorem realActionMin_uniform_close
    {B A : Type*} [Fintype A] [Nonempty A]
    (Q R : B → A → ℝ) (b : B) (eps : ℝ)
    (hclose : ∀ a, |Q b a - R b a| ≤ eps) :
    |realActionMin Q b - realActionMin R b| ≤ eps := by
  classical
  rcases exists_action_eq_realActionMin Q b with ⟨aq, haq⟩
  rcases exists_action_eq_realActionMin R b with ⟨ar, har⟩
  have hqle : realActionMin Q b ≤ Q b ar := realActionMin_le Q b ar
  have hrle : realActionMin R b ≤ R b aq := realActionMin_le R b aq
  have hcar := (abs_le.mp (hclose ar)).2
  have hcaq := (abs_le.mp (hclose aq)).1
  rw [haq] at hcaq
  rw [har] at hcar
  apply abs_le.mpr
  constructor <;> linarith

/-- Discounted Bellman operator on a finite closed decision-state graph. -/
noncomputable def infiniteBellman
    {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma : ℝ) (V : X → ℝ) (x : X) : ℝ :=
  realActionMin (infiniteQ P stageCost gamma V) x

/-- Pointwise finite-sup contraction bound for the Bellman operator. -/
theorem infiniteBellman_uniform_close
    {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma delta : ℝ) (hgamma : 0 ≤ gamma)
    (V W : X → ℝ)
    (hdelta : ∀ y, |V y - W y| ≤ delta)
    (x : X) :
    |infiniteBellman P stageCost gamma V x -
      infiniteBellman P stageCost gamma W x| ≤ gamma * delta := by
  unfold infiniteBellman
  apply realActionMin_uniform_close
  intro a
  exact infiniteQ_uniform_close P stageCost gamma delta hgamma V W hdelta x a

/-- Exact finite sup-distance between two real value functions. -/
noncomputable def finiteSupDistance
    {X : Type*} [Fintype X] [Nonempty X]
    (V W : X → ℝ) : ℝ :=
  (Finset.univ.image (fun x => |V x - W x|)).max' (by simp)

/-- Every pointwise discrepancy is bounded by the finite sup-distance. -/
theorem abs_sub_le_finiteSupDistance
    {X : Type*} [Fintype X] [Nonempty X]
    (V W : X → ℝ) (x : X) :
    |V x - W x| ≤ finiteSupDistance V W := by
  classical
  unfold finiteSupDistance
  apply Finset.le_max'
  simp

/-- The finite sup-distance is attained at some state. -/
theorem exists_state_eq_finiteSupDistance
    {X : Type*} [Fintype X] [Nonempty X]
    (V W : X → ℝ) :
    ∃ x : X, |V x - W x| = finiteSupDistance V W := by
  classical
  have hmem : finiteSupDistance V W ∈
      Finset.univ.image (fun x => |V x - W x|) := by
    unfold finiteSupDistance
    exact Finset.max'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨x, hx, hEq⟩
  exact ⟨x, hEq⟩

/-- Bellman fixed-point predicate. -/
def InfiniteBellmanFixedPoint
    {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma : ℝ) (V : X → ℝ) : Prop :=
  ∀ x, infiniteBellman P stageCost gamma V x = V x

/-- Under `0 <= gamma < 1`, a discounted Bellman fixed point is unique whenever
it exists. This theorem proves uniqueness, not existence. -/
theorem infiniteBellman_fixedPoint_unique
    {X A : Type*} [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma : ℝ) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    {V W : X → ℝ}
    (hV : InfiniteBellmanFixedPoint P stageCost gamma V)
    (hW : InfiniteBellmanFixedPoint P stageCost gamma W) :
    V = W := by
  classical
  let d : ℝ := finiteSupDistance V W
  have hpoint : ∀ x, |V x - W x| ≤ d := by
    intro x
    exact abs_sub_le_finiteSupDistance V W x
  rcases exists_state_eq_finiteSupDistance V W with ⟨x0, hx0⟩
  have hcontract :=
    infiniteBellman_uniform_close P stageCost gamma d hgamma0 V W hpoint x0
  rw [hV x0, hW x0, hx0] at hcontract
  have hcontract' : d ≤ gamma * d := by
    simpa [d] using hcontract
  have hd0 : 0 ≤ d := by
    change 0 ≤ finiteSupDistance V W
    rw [← hx0]
    exact abs_nonneg _
  have hd : d = 0 := by
    nlinarith [hcontract']
  have hdist0 : finiteSupDistance V W = 0 := by
    simpa [d] using hd
  funext x
  have hx := abs_sub_le_finiteSupDistance V W x
  rw [hdist0] at hx
  have habs : |V x - W x| = 0 := le_antisymm hx (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-- Infinite-horizon Bellman-optimality contract relative to a supplied value
function, intended to be instantiated by a proved fixed point. -/
def InfiniteBellmanGood
    {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma : ℝ) (Vstar : X → ℝ) (x : X) (a : A) : Prop :=
  infiniteQ P stageCost gamma Vstar x a =
    realActionMin (infiniteQ P stageCost gamma Vstar) x

/-- At every finite decision state, at least one action minimizes the supplied
infinite-horizon Q-family. -/
theorem exists_infiniteBellmanOptimalAction
    {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma : ℝ) (Vstar : X → ℝ) (x : X) :
    ∃ a : A, InfiniteBellmanGood P stageCost gamma Vstar x a := by
  exact exists_action_eq_realActionMin (infiniteQ P stageCost gamma Vstar) x

/-- INSACERMO SafeRep instantiated with an infinite-horizon Bellman-optimal
action contract. -/
def InfiniteBellmanSafeRep
    {X A Y : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma : ℝ) (Vstar : X → ℝ)
    (B : Set X) (C : Set A) (h : X → Y) : Prop :=
  SafeRep (InfiniteBellmanGood P stageCost gamma Vstar) B C h

/-- Capability expansion remains monotone for infinite-horizon Bellman
actionability. -/
theorem infiniteBellmanSafeRep_capability_mono
    {X A Y : Type*} [Fintype X] [Fintype A] [Nonempty A]
    {P : X → A → FiniteLaw X} {stageCost : X → A → ℝ}
    {gamma : ℝ} {Vstar : X → ℝ} {B : Set X}
    {C C' : Set A} {h : X → Y}
    (hsafe : InfiniteBellmanSafeRep P stageCost gamma Vstar B C h)
    (hcap : C ⊆ C') :
    InfiniteBellmanSafeRep P stageCost gamma Vstar B C' h := by
  exact safeRep_capability_mono hsafe hcap

/-- Information refinement remains monotone for infinite-horizon Bellman
actionability. -/
theorem infiniteBellmanSafeRep_information_mono
    {X A YFine YCoarse : Type*} [Fintype X] [Fintype A] [Nonempty A]
    {P : X → A → FiniteLaw X} {stageCost : X → A → ℝ}
    {gamma : ℝ} {Vstar : X → ℝ} {B : Set X} {C : Set A}
    {fine : X → YFine} {coarse : X → YCoarse}
    (hsafe : InfiniteBellmanSafeRep P stageCost gamma Vstar B C coarse)
    (href : Refines fine coarse) :
    InfiniteBellmanSafeRep P stageCost gamma Vstar B C fine := by
  exact safeRep_information_mono hsafe href

/-- With full state information and all actions available, the supplied
Bellman-optimality contract is actionable at every admissible state. -/
theorem infiniteBellmanSafeRep_identity_univ
    {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma : ℝ) (Vstar : X → ℝ) (B : Set X) :
    InfiniteBellmanSafeRep P stageCost gamma Vstar B Set.univ id := by
  intro x hxReal
  rcases hxReal with ⟨x0, hx0B, hx0⟩
  subst x
  rcases exists_infiniteBellmanOptimalAction P stageCost gamma Vstar x0 with ⟨a, ha⟩
  refine ⟨a, by simp, ?_⟩
  intro x' hx'B hx'eq
  change x' = x0 at hx'eq
  simpa [hx'eq] using ha

/-- Candidate-level infinite-horizon Bellman safety for the existing sequential
INSACERMO planner. -/
def InfiniteBellmanCandidateSafe
    {I X A Y : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma : ℝ) (Vstar : X → ℝ)
    (B : Set X) (caps : I → Set A) (obs : I → X → Y) (i : I) : Prop :=
  InfiniteBellmanSafeRep P stageCost gamma Vstar B (caps i) (obs i)

/-- Infinite-horizon Bellman actionability plugs into the already verified
ACT / REFUSE / optimal PROBE-REPAIR-PROBE+REPAIR router without changing the
planner semantics. -/
theorem infiniteBellmanPlanner_router_complete
    {I X A Y : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → FiniteLaw X)
    (stageCost : X → A → ℝ)
    (gamma : ℝ) (Vstar : X → ℝ)
    (B : Set X) (caps : I → Set A) (obs : I → X → Y)
    (BaseAllowed PreserveOK : I → Move I → Prop) (i : I) :
    InfiniteBellmanCandidateSafe P stageCost gamma Vstar B caps obs i ∨
      (¬ InfiniteBellmanCandidateSafe P stageCost gamma Vstar B caps obs i ∧
        ¬ ReachableSafe
          (InfiniteBellmanCandidateSafe P stageCost gamma Vstar B caps obs)
          (LegalStep BaseAllowed PreserveOK) i) ∨
      (¬ InfiniteBellmanCandidateSafe P stageCost gamma Vstar B caps obs i ∧
        ReachableSafe
          (InfiniteBellmanCandidateSafe P stageCost gamma Vstar B caps obs)
          (LegalStep BaseAllowed PreserveOK) i ∧
        ∃ k, OptimalFrontierKind
          (InfiniteBellmanCandidateSafe P stageCost gamma Vstar B caps obs)
          (LegalStep BaseAllowed PreserveOK) i k) := by
  exact planner_router_complete
    (InfiniteBellmanCandidateSafe P stageCost gamma Vstar B caps obs)
    (LegalStep BaseAllowed PreserveOK) i

end InsacermoActionabilityInformation
