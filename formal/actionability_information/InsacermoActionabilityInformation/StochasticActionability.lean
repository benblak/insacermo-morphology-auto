import InsacermoActionabilityInformation.HypergraphActionability

namespace InsacermoActionabilityInformation

/-- A finite rational probability law. This first stochastic extension is
intentionally finite and exact: probabilities and losses are rational, so no
analytic approximation is hidden in the actionability predicate. -/
structure FiniteLaw (O : Type*) [Fintype O] where
  mass : O → ℚ
  nonneg : ∀ o, 0 ≤ mass o
  total_one : (Finset.univ.sum mass) = 1

/-- Expected loss of a finite rational law. -/
def ExpectedLoss {O : Type*} [Fintype O]
    (P : FiniteLaw O) (loss : O → ℚ) : ℚ :=
  Finset.univ.sum (fun o => P.mass o * loss o)

/-- Risk acceptability induced by a fixed finite outcome law, loss function,
and expected-loss threshold. -/
def RiskGood {S A O : Type*} [Fintype O]
    (Law : S → A → FiniteLaw O) (loss : O → ℚ) (theta : ℚ)
    (s : S) (a : A) : Prop :=
  ExpectedLoss (Law s a) loss ≤ theta

/-- The stochastic actionability kernel is the frozen `SafeRep` kernel
instantiated by the risk-induced admissibility predicate. -/
def RiskSafeRep {S A O Y : Type*} [Fintype O]
    (Law : S → A → FiniteLaw O) (loss : O → ℚ) (theta : ℚ)
    (B : Set S) (C : Set A) (h : S → Y) : Prop :=
  SafeRep (RiskGood Law loss theta) B C h

/-- Capability expansion cannot destroy a representation that is already safe
under a fixed stochastic law, loss, and risk threshold. -/
theorem riskSafeRep_capability_mono
    {S A O Y : Type*} [Fintype O]
    {Law : S → A → FiniteLaw O} {loss : O → ℚ} {theta : ℚ}
    {B : Set S} {C C' : Set A} {h : S → Y}
    (hsafe : RiskSafeRep Law loss theta B C h)
    (hcap : C ⊆ C') :
    RiskSafeRep Law loss theta B C' h := by
  exact safeRep_capability_mono hsafe hcap

/-- Finer information cannot destroy stochastic actionability under a fixed
law, loss, threshold, and capability set. -/
theorem riskSafeRep_information_mono
    {S A O YFine YCoarse : Type*} [Fintype O]
    {Law : S → A → FiniteLaw O} {loss : O → ℚ} {theta : ℚ}
    {B : Set S} {C : Set A}
    {fine : S → YFine} {coarse : S → YCoarse}
    (hsafe : RiskSafeRep Law loss theta B C coarse)
    (href : Refines fine coarse) :
    RiskSafeRep Law loss theta B C fine := by
  exact safeRep_information_mono hsafe href

/-- Joint product-order monotonicity survives the finite stochastic
instantiation unchanged. -/
theorem riskSafeRep_of_refines_of_capabilitySubset
    {S A O YFine YCoarse : Type*} [Fintype O]
    {Law : S → A → FiniteLaw O} {loss : O → ℚ} {theta : ℚ}
    {B : Set S} {C C' : Set A}
    {fine : S → YFine} {coarse : S → YCoarse}
    (hsafe : RiskSafeRep Law loss theta B C coarse)
    (href : Refines fine coarse)
    (hcap : C ⊆ C') :
    RiskSafeRep Law loss theta B C' fine := by
  exact safeRep_of_refines_of_capabilitySubset hsafe href hcap

/-- Relaxing the expected-loss threshold cannot destroy an already-safe
representation. This is a contract monotonicity result specific to the first
stochastic instantiation. -/
theorem riskSafeRep_threshold_mono
    {S A O Y : Type*} [Fintype O]
    {Law : S → A → FiniteLaw O} {loss : O → ℚ}
    {theta theta' : ℚ} {B : Set S} {C : Set A} {h : S → Y}
    (hsafe : RiskSafeRep Law loss theta B C h)
    (hth : theta ≤ theta') :
    RiskSafeRep Law loss theta' B C h := by
  intro y hy
  rcases hsafe y hy with ⟨a, haC, hgood⟩
  refine ⟨a, haC, ?_⟩
  intro s hsB hsy
  exact le_trans (hgood s hsB hsy) hth

/-- The capability-relative minimal-obstruction hypergraph induced by the
stochastic risk contract. -/
def RiskMinimalObstructionHypergraph
    {S A O : Type*} [Fintype O] [DecidableEq S]
    (Law : S → A → FiniteLaw O) (loss : O → ℚ) (theta : ℚ)
    (C : Set A) : Set (Finset S) :=
  MinimalObstructionHypergraph (RiskGood Law loss theta) C

/-- Hypergraph safety under the stochastic risk contract. -/
def RiskHypergraphSafe
    {S A O Y : Type*} [Fintype O] [DecidableEq S]
    (Law : S → A → FiniteLaw O) (loss : O → ℚ) (theta : ℚ)
    (B : Set S) (C : Set A) (h : S → Y) : Prop :=
  HypergraphSafe (RiskGood Law loss theta) B C h

/-- Exact finite stochastic obstruction theorem: stochasticity by itself does
not alter the finite hypergraph characterization when risk admissibility is a
fixed local predicate. -/
theorem riskSafeRep_iff_riskHypergraphSafe
    {S A O Y : Type*} [Fintype S] [DecidableEq S] [Fintype O]
    {Law : S → A → FiniteLaw O} {loss : O → ℚ} {theta : ℚ}
    {B : Set S} {C : Set A} {h : S → Y} :
    RiskSafeRep Law loss theta B C h ↔
      RiskHypergraphSafe Law loss theta B C h := by
  exact safeRep_iff_hypergraphSafe

/-- Equivalently, finite stochastic actionability is characterized by absence
of a minimal risk-induced common-action obstruction inside every realized
observation fiber. -/
theorem riskSafeRep_iff_no_minimal_fiber_obstruction
    {S A O Y : Type*} [Fintype S] [DecidableEq S] [Fintype O]
    {Law : S → A → FiniteLaw O} {loss : O → ℚ} {theta : ℚ}
    {B : Set S} {C : Set A} {h : S → Y} :
    RiskSafeRep Law loss theta B C h ↔
      ¬ FiberContainsMinimalObstruction (RiskGood Law loss theta) B C h := by
  exact safeRep_iff_no_minimal_fiber_obstruction

end InsacermoActionabilityInformation
