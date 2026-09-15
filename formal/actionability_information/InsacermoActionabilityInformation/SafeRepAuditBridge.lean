import InsacermoActionabilityInformation.FiberCommonActions
import InsacermoActionabilityInformation.HypergraphObstructionRankBridge

namespace InsacermoActionabilityInformation

namespace SafeRepAudit

variable {S A Y : Type*} [DecidableEq S] [DecidableEq Y]

/-- The finite part of an admissible world set that is collapsed into one
representation value. -/
def fiberFinset (B : Finset S) (h : S → Y) (y : Y) : Finset S :=
  B.filter (fun s => h s = y)

theorem mem_fiberFinset {B : Finset S} {h : S → Y} {y : Y} {s : S} :
    s ∈ fiberFinset B h y ↔ s ∈ B ∧ h s = y := by
  simp [fiberFinset]

/-- A representation passes the depth-`k` fiber audit when every subcontract
of at most `k` worlds inside every realized representation fiber has a common
available good action. -/
def PassesFiberAudit
    (Good : S → A → Prop) (C : Set A) (k : ℕ)
    (B : Finset S) (h : S → Y) : Prop :=
  ∀ y, RealizedFiber (↑B : Set S) h y →
    FiniteContractAudit.PassesLocalAudit
      (ActionabilityAudit.commonActionSat Good C) k (fiberFinset B h y)

/-- Main INSACERMO bridge: once common-action obstruction rank is bounded by
`k`, depth-`k` local audits of every realized representation fiber certify the
whole representation as safe. -/
theorem safeRep_of_obstructionRankAtMost_of_passesFiberAudit
    {Good : S → A → Prop} {C : Set A} {k : ℕ}
    {B : Finset S} {h : S → Y}
    (hC : C.Nonempty)
    (hrank : ActionabilityAudit.CommonActionObstructionRankAtMost Good C k)
    (haudit : PassesFiberAudit Good C k B h) :
    SafeRep Good (↑B : Set S) C h := by
  intro y hyreal
  have hcomplete :
      FiniteContractAudit.LocalAuditComplete
        (ActionabilityAudit.commonActionSat Good C) k :=
    (ActionabilityAudit.commonActionObstructionRankAtMost_iff_localAuditComplete
      hC k).mp hrank
  have hsat :
      ActionabilityAudit.commonActionSat Good C (fiberFinset B h y) :=
    hcomplete (fiberFinset B h y) (haudit y hyreal)
  change HasCommonActionOn Good C (fiberFinset B h y) at hsat
  rcases hsat with ⟨a, haC, hall⟩
  refine ⟨a, haC, ?_⟩
  intro s hsB hsy
  apply hall s
  simp [fiberFinset, hsB, hsy]

/-- Safety always implies every finite local fiber audit, at every depth:
one common action for the whole fiber restricts to every audited subcontract. -/
theorem safeRep_implies_passesFiberAudit
    {Good : S → A → Prop} {C : Set A} {k : ℕ}
    {B : Finset S} {h : S → Y}
    (hsafe : SafeRep Good (↑B : Set S) C h) :
    PassesFiberAudit Good C k B h := by
  intro y hyreal G hGsub _hcard
  rcases hsafe y hyreal with ⟨a, haC, hall⟩
  change HasCommonActionOn Good C G
  refine ⟨a, haC, ?_⟩
  intro s hsG
  have hsFiber : s ∈ fiberFinset B h y := hGsub hsG
  have hs : s ∈ B ∧ h s = y := (mem_fiberFinset).mp hsFiber
  exact hall s (by simpa using hs.1) hs.2

/-- Exact contract-relative audit criterion for safe information destruction:
under obstruction rank at most `k`, a finite representation is safe if and
only if every realized fiber passes all audits through cardinality `k`. -/
theorem safeRep_iff_passesFiberAudit_of_obstructionRankAtMost
    {Good : S → A → Prop} {C : Set A} {k : ℕ}
    {B : Finset S} {h : S → Y}
    (hC : C.Nonempty)
    (hrank : ActionabilityAudit.CommonActionObstructionRankAtMost Good C k) :
    SafeRep Good (↑B : Set S) C h ↔ PassesFiberAudit Good C k B h := by
  constructor
  · exact safeRep_implies_passesFiberAudit
  · exact safeRep_of_obstructionRankAtMost_of_passesFiberAudit hC hrank

/-- Sharp failure beyond the audit depth.  A minimal obstruction larger than
`k` itself passes every depth-`k` subcontract audit, yet collapsing all its
worlds to one code (the constant representation) is unsafe. -/
theorem largeMinimalObstruction_gives_locallyAudited_unsafe_constantRep
    {Good : S → A → Prop} {C : Set A} {k : ℕ} {M : Finset S}
    (hC : C.Nonempty)
    (hmin : MinimalCommonActionObstruction Good C M)
    (hk : k < M.card) :
    FiniteContractAudit.PassesLocalAudit
        (ActionabilityAudit.commonActionSat Good C) k M ∧
      ¬ SafeRep Good (↑M : Set S) C (fun _ : S => ()) := by
  have habstract :
      FiniteContractAudit.IsMinimalUnsat
        (ActionabilityAudit.commonActionSat Good C) M :=
    (ActionabilityAudit.minimalCommonActionObstruction_iff_abstract hC).mp hmin
  have hblind :=
    FiniteContractAudit.minimalUnsat_large_is_localAudit_blindSpot
      (ActionabilityAudit.commonActionSat Good C) habstract hk
  refine ⟨hblind.1, ?_⟩
  apply finiteObstruction_inside_fiber_blocks_safeRep (hobs := hmin.1)
  · intro s hs
    simpa using hs
  · intro _s _hs
    rfl

/-- If common-action obstructions are unbounded, then every fixed local audit
depth admits a maximally destructive constant representation that passes all
its local checks while remaining globally unsafe. -/
theorem unboundedObstructions_defeat_every_fixed_safeDestructionAudit
    {Good : S → A → Prop} {C : Set A}
    (hC : C.Nonempty)
    (hunbounded :
      ∀ k : ℕ, ∃ M : Finset S,
        MinimalCommonActionObstruction Good C M ∧ k < M.card) :
    ∀ k : ℕ, ∃ M : Finset S,
      FiniteContractAudit.PassesLocalAudit
          (ActionabilityAudit.commonActionSat Good C) k M ∧
        ¬ SafeRep Good (↑M : Set S) C (fun _ : S => ()) := by
  intro k
  rcases hunbounded k with ⟨M, hmin, hk⟩
  exact ⟨M, largeMinimalObstruction_gives_locallyAudited_unsafe_constantRep
    hC hmin hk⟩

end SafeRepAudit

end InsacermoActionabilityInformation
