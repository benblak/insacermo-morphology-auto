import InsacermoActionabilityInformation.EventualFutureGeometry

namespace InsacermoActionabilityInformation

namespace EventualObstructionRank

open FutureRobustness
open TemporalJointContractComplex
open TemporalObstructionPersistence
open FutureDepthSpectrum
open EventualFutureGeometry

/-- There exists at least one finite future bundle that is never jointly
recoverable at any finite horizon. -/
def HasEventualObstruction
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) : Prop :=
  ∃ F : Finset Q, ¬ (EventualFutureComplex Avail Step x).feasible F

/-- There is an eventually impossible future bundle of exactly cardinality k. -/
def EventualObstructionAtCard
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (k : ℕ) : Prop :=
  ∃ F : Finset Q,
    F.card = k ∧
    ¬ (EventualFutureComplex Avail Step x).feasible F

/-- The least cardinality at which an eventual obstruction appears.
This is defined only when at least one finite eventual obstruction exists. -/
noncomputable def Rank
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X)
    (hobs : HasEventualObstruction Avail Step x) : ℕ := by
  classical
  exact Nat.find (by
    rcases hobs with ⟨F, hF⟩
    exact ⟨F.card, F, rfl, hF⟩)

/-- The empty future bundle is always eventually feasible. -/
theorem eventualFutureComplex_empty_feasible
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} :
    (EventualFutureComplex Avail Step x).feasible (∅ : Finset Q) := by
  change HasFiniteJointRecoveryDepth Avail Step x (∅ : Finset Q)
  refine ⟨0, ?_⟩
  change JointRecoverable Avail Step 0 x (∅ : Set Q)
  exact jointRecoverable_empty Avail Step 0 x

/-- The rank is witnessed by an actual eventually impossible bundle. -/
theorem rank_spec
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X}
    (hobs : HasEventualObstruction Avail Step x) :
    EventualObstructionAtCard Avail Step x
      (Rank Avail Step x hobs) := by
  classical
  unfold Rank
  exact Nat.find_spec (by
    rcases hobs with ⟨F, hF⟩
    exact ⟨F.card, F, rfl, hF⟩)

/-- Any explicit eventual obstruction gives an upper bound on the rank. -/
theorem rank_le_of_obstruction
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X}
    (hobs : HasEventualObstruction Avail Step x)
    {F : Finset Q}
    (hF : ¬ (EventualFutureComplex Avail Step x).feasible F) :
    Rank Avail Step x hobs ≤ F.card := by
  classical
  unfold Rank
  apply Nat.find_min'
  exact ⟨F, rfl, hF⟩

/-- No eventual obstruction can occur below the rank. -/
theorem no_obstruction_below_rank
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X}
    (hobs : HasEventualObstruction Avail Step x)
    {F : Finset Q}
    (hcard : F.card < Rank Avail Step x hobs) :
    (EventualFutureComplex Avail Step x).feasible F := by
  by_contra hF
  have hle : Rank Avail Step x hobs ≤ F.card :=
    rank_le_of_obstruction hobs hF
  exact (Nat.not_le_of_gt hcard) hle

/-- Eventual obstruction rank is always strictly positive. -/
theorem rank_pos
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X}
    (hobs : HasEventualObstruction Avail Step x) :
    0 < Rank Avail Step x hobs := by
  have hempty :
      (EventualFutureComplex Avail Step x).feasible (∅ : Finset Q) :=
    eventualFutureComplex_empty_feasible
  rcases rank_spec hobs with ⟨F, hcard, hbad⟩
  by_contra hnot
  have hrank0 : Rank Avail Step x hobs = 0 := Nat.eq_zero_of_not_pos hnot
  have hF0 : F.card = 0 := by simpa [hrank0] using hcard
  have hFempty : F = ∅ := Finset.card_eq_zero.mp hF0
  subst F
  exact hbad hempty

/-- A minimum-cardinality eventual obstruction is automatically an eventual
minimal obstruction: every proper sub-bundle has smaller cardinality and is
therefore eventually feasible. -/
theorem rank_has_minimal_obstruction_witness
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X}
    (hobs : HasEventualObstruction Avail Step x) :
    ∃ F : Finset Q,
      F.card = Rank Avail Step x hobs ∧
      EventualMinimalObstruction Avail Step x F := by
  rcases rank_spec hobs with ⟨F, hcard, hbad⟩
  refine ⟨F, hcard, ?_⟩
  constructor
  · exact hbad
  · intro G hGF
    have hcardlt : G.card < F.card := Finset.card_lt_card hGF
    have hcardlt' : G.card < Rank Avail Step x hobs := by
      simpa [hcard] using hcardlt
    exact no_obstruction_below_rank hobs hcardlt'

/-- Conversely, every eventual minimal obstruction bounds the global rank by
its cardinality. -/
theorem rank_le_minimal_obstruction_card
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X}
    (hobs : HasEventualObstruction Avail Step x)
    {F : Finset Q}
    (hmin : EventualMinimalObstruction Avail Step x F) :
    Rank Avail Step x hobs ≤ F.card := by
  exact rank_le_of_obstruction hobs hmin.1

/-- A hidden joint pair is always an eventual obstruction of cardinality at
most two, so whenever any eventual obstruction exists the global rank is ≤ 2. -/
theorem rank_le_two_of_hiddenJointPair
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {q r : Q}
    (hpair : HiddenJointPair Avail Step x q r) :
    ∃ hobs : HasEventualObstruction Avail Step x,
      Rank Avail Step x hobs ≤ 2 := by
  have hbad :
      ¬ (EventualFutureComplex Avail Step x).feasible ({q, r} : Finset Q) := by
    exact (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).1 hpair.2.2
  let hobs : HasEventualObstruction Avail Step x := ⟨{q, r}, hbad⟩
  refine ⟨hobs, ?_⟩
  have hle := rank_le_of_obstruction hobs hbad
  exact le_trans hle (by simp)

end EventualObstructionRank

end InsacermoActionabilityInformation
