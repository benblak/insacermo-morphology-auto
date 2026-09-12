import InsacermoActionabilityInformation.FiniteBayesFilter

namespace InsacermoActionabilityInformation

/-- Totalized Bayesian update for finite-horizon recursion.  On positive-evidence
branches this is the exact Bayesian posterior.  On impossible observations a
fixed fallback belief is returned; the associated observation probability is
zero, so the Bellman expectation is independent of that fallback. -/
noncomputable def totalBayesUpdate
    {S A O : Type*} [Fintype S] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (b : FiniteLaw S) (a : A) (o : O) : FiniteLaw S :=
  if h : 0 < evidence T Z b a o then bayesUpdate T Z b a o h else fallback

/-- On every positive-evidence branch, totalization is definitionally the
verified exact Bayesian update. -/
theorem totalBayesUpdate_eq_bayesUpdate_of_pos
    {S A O : Type*} [Fintype S] [Fintype O]
    {T : A → S → FiniteLaw S}
    {Z : A → S → FiniteLaw O}
    {fallback : FiniteLaw S}
    {b : FiniteLaw S} {a : A} {o : O}
    (hpos : 0 < evidence T Z b a o) :
    totalBayesUpdate T Z fallback b a o = bayesUpdate T Z b a o hpos := by
  simp [totalBayesUpdate, hpos]

/-- Since evidence is already known nonnegative, failure of strict positivity
means that the observation has exactly zero predictive probability. -/
theorem evidence_eq_zero_of_not_pos
    {S A O : Type*} [Fintype S] [Fintype O]
    {T : A → S → FiniteLaw S}
    {Z : A → S → FiniteLaw O}
    {b : FiniteLaw S} {a : A} {o : O}
    (hnot : ¬ 0 < evidence T Z b a o) :
    evidence T Z b a o = 0 := by
  exact le_antisymm (not_lt.mp hnot) (evidence_nonneg T Z b a o)

/-- An impossible observation contributes exactly zero to any continuation
expectation, so the fallback used by `totalBayesUpdate` is semantically inert. -/
theorem zeroEvidence_continuation_term
    {S A O : Type*} [Fintype S] [Fintype O]
    {T : A → S → FiniteLaw S}
    {Z : A → S → FiniteLaw O}
    {fallback : FiniteLaw S}
    {b : FiniteLaw S} {a : A} {o : O}
    (V : FiniteLaw S → ℚ)
    (hnot : ¬ 0 < evidence T Z b a o) :
    evidence T Z b a o * V (totalBayesUpdate T Z fallback b a o) = 0 := by
  rw [evidence_eq_zero_of_not_pos hnot]
  simp

/-- One-step Bellman Q-value on the exact finite belief model. -/
noncomputable def beliefQ
    {S A O : Type*} [Fintype S] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (V : FiniteLaw S → ℚ)
    (b : FiniteLaw S) (a : A) : ℚ :=
  stageCost b a +
    Finset.univ.sum (fun o =>
      evidence T Z b a o * V (totalBayesUpdate T Z fallback b a o))

/-- Finite nonempty action minimization for a Bellman Q-family. -/
noncomputable def finiteActionMin
    {B A : Type*} [Fintype A] [Nonempty A]
    (Q : B → A → ℚ) (b : B) : ℚ :=
  (Finset.univ.image (fun a => Q b a)).min' (by simp)

/-- The finite-action minimum is attained. -/
theorem exists_action_eq_finiteActionMin
    {B A : Type*} [Fintype A] [Nonempty A]
    (Q : B → A → ℚ) (b : B) :
    ∃ a : A, Q b a = finiteActionMin Q b := by
  classical
  have hmem : finiteActionMin Q b ∈ Finset.univ.image (fun a => Q b a) := by
    unfold finiteActionMin
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨a, ha, hEq⟩
  exact ⟨a, hEq⟩

/-- The finite-action minimum is below every candidate action value. -/
theorem finiteActionMin_le
    {B A : Type*} [Fintype A] [Nonempty A]
    (Q : B → A → ℚ) (b : B) (a : A) :
    finiteActionMin Q b ≤ Q b a := by
  classical
  unfold finiteActionMin
  apply Finset.min'_le
  simp

/-- Finite-horizon Bellman value on exact rational belief states. -/
noncomputable def beliefValue
    {S A O : Type*} [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ) : Nat → FiniteLaw S → ℚ
  | 0, b => terminalCost b
  | n + 1, b =>
      finiteActionMin
        (beliefQ T Z fallback stageCost
          (beliefValue T Z fallback stageCost terminalCost n)) b

/-- Exact Bellman successor equation. -/
theorem beliefValue_succ
    {S A O : Type*} [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ)
    (n : Nat) (b : FiniteLaw S) :
    beliefValue T Z fallback stageCost terminalCost (n + 1) b =
      finiteActionMin
        (beliefQ T Z fallback stageCost
          (beliefValue T Z fallback stageCost terminalCost n)) b := by
  rfl

/-- Bellman optimality as the actionability contract on belief states. -/
def BellmanGood
    {S A O : Type*} [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ)
    (n : Nat) (b : FiniteLaw S) (a : A) : Prop :=
  beliefQ T Z fallback stageCost
      (beliefValue T Z fallback stageCost terminalCost n) b a =
    finiteActionMin
      (beliefQ T Z fallback stageCost
        (beliefValue T Z fallback stageCost terminalCost n)) b

/-- At every exact belief and every finite horizon, at least one Bellman-optimal
action exists. -/
theorem exists_bellmanOptimalAction
    {S A O : Type*} [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ)
    (n : Nat) (b : FiniteLaw S) :
    ∃ a : A, BellmanGood T Z fallback stageCost terminalCost n b a := by
  exact exists_action_eq_finiteActionMin
    (beliefQ T Z fallback stageCost
      (beliefValue T Z fallback stageCost terminalCost n)) b

/-- INSACERMO actionability instantiated with exact Bellman-optimal actions. -/
def BellmanSafeRep
    {S A O Y : Type*} [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ)
    (n : Nat)
    (B : Set (FiniteLaw S)) (C : Set A) (h : FiniteLaw S → Y) : Prop :=
  SafeRep (BellmanGood T Z fallback stageCost terminalCost n) B C h

/-- Capability expansion remains monotone for Bellman-generated actionability. -/
theorem bellmanSafeRep_capability_mono
    {S A O Y : Type*} [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    {T : A → S → FiniteLaw S}
    {Z : A → S → FiniteLaw O}
    {fallback : FiniteLaw S}
    {stageCost : FiniteLaw S → A → ℚ}
    {terminalCost : FiniteLaw S → ℚ}
    {n : Nat} {B : Set (FiniteLaw S)} {C C' : Set A}
    {h : FiniteLaw S → Y}
    (hsafe : BellmanSafeRep T Z fallback stageCost terminalCost n B C h)
    (hcap : C ⊆ C') :
    BellmanSafeRep T Z fallback stageCost terminalCost n B C' h := by
  exact safeRep_capability_mono hsafe hcap

/-- Finer external belief representation remains monotone for Bellman actionability. -/
theorem bellmanSafeRep_information_mono
    {S A O YFine YCoarse : Type*}
    [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    {T : A → S → FiniteLaw S}
    {Z : A → S → FiniteLaw O}
    {fallback : FiniteLaw S}
    {stageCost : FiniteLaw S → A → ℚ}
    {terminalCost : FiniteLaw S → ℚ}
    {n : Nat} {B : Set (FiniteLaw S)} {C : Set A}
    {fine : FiniteLaw S → YFine} {coarse : FiniteLaw S → YCoarse}
    (hsafe : BellmanSafeRep T Z fallback stageCost terminalCost n B C coarse)
    (href : Refines fine coarse) :
    BellmanSafeRep T Z fallback stageCost terminalCost n B C fine := by
  exact safeRep_information_mono hsafe href

/-- With every action available and the full belief itself observed, Bellman
actionability always holds on any set of admissible beliefs. -/
theorem bellmanSafeRep_identity_univ
    {S A O : Type*} [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ)
    (n : Nat) (B : Set (FiniteLaw S)) :
    BellmanSafeRep T Z fallback stageCost terminalCost n B Set.univ id := by
  intro b hbReal
  rcases hbReal with ⟨b0, hb0B, hb0⟩
  subst b
  rcases exists_bellmanOptimalAction T Z fallback stageCost terminalCost n b0 with ⟨a, ha⟩
  refine ⟨a, by simp, ?_⟩
  intro b' hb'B hb'eq
  change b' = b0 at hb'eq
  simpa [hb'eq] using ha

end InsacermoActionabilityInformation
