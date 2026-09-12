import InsacermoActionabilityInformation.StochasticActionability
import InsacermoActionabilityInformation.BeliefStateActionability

namespace InsacermoActionabilityInformation

/-- Predicted next-state mass under a finite belief and transition kernel. -/
def predictMass {S A : Type*} [Fintype S]
    (T : A → S → FiniteLaw S) (b : FiniteLaw S) (a : A) (sp : S) : ℚ :=
  Finset.univ.sum (fun s => b.mass s * (T a s).mass sp)

/-- Prediction preserves nonnegativity. -/
theorem predictMass_nonneg
    {S A : Type*} [Fintype S]
    (T : A → S → FiniteLaw S) (b : FiniteLaw S) (a : A) (sp : S) :
    0 ≤ predictMass T b a sp := by
  unfold predictMass
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (b.nonneg s) ((T a s).nonneg sp))

/-- Prediction preserves total mass exactly. -/
theorem predictMass_total_one
    {S A : Type*} [Fintype S]
    (T : A → S → FiniteLaw S) (b : FiniteLaw S) (a : A) :
    Finset.univ.sum (predictMass T b a) = 1 := by
  classical
  unfold predictMass
  rw [Finset.sum_comm]
  calc
    Finset.univ.sum (fun s => Finset.univ.sum (fun sp => b.mass s * (T a s).mass sp)) =
        Finset.univ.sum (fun s => b.mass s * Finset.univ.sum (fun sp => (T a s).mass sp)) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.mul_sum]
    _ = Finset.univ.sum (fun s => b.mass s * 1) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [(T a s).total_one]
    _ = 1 := by simpa using b.total_one

/-- The predicted next-state distribution is itself a finite exact law. -/
def predictLaw {S A : Type*} [Fintype S]
    (T : A → S → FiniteLaw S) (b : FiniteLaw S) (a : A) : FiniteLaw S where
  mass := predictMass T b a
  nonneg := predictMass_nonneg T b a
  total_one := predictMass_total_one T b a

/-- Unnormalized Bayesian posterior weight after receiving observation `o`. -/
def posteriorWeight {S A O : Type*} [Fintype S] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (b : FiniteLaw S) (a : A) (o : O) (sp : S) : ℚ :=
  (predictLaw T b a).mass sp * (Z a sp).mass o

/-- Posterior weights are nonnegative. -/
theorem posteriorWeight_nonneg
    {S A O : Type*} [Fintype S] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (b : FiniteLaw S) (a : A) (o : O) (sp : S) :
    0 ≤ posteriorWeight T Z b a o sp := by
  exact mul_nonneg ((predictLaw T b a).nonneg sp) ((Z a sp).nonneg o)

/-- Probability/evidence of observing `o` after action `a` from belief `b`. -/
def evidence {S A O : Type*} [Fintype S] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (b : FiniteLaw S) (a : A) (o : O) : ℚ :=
  Finset.univ.sum (posteriorWeight T Z b a o)

/-- Evidence is always nonnegative. -/
theorem evidence_nonneg
    {S A O : Type*} [Fintype S] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (b : FiniteLaw S) (a : A) (o : O) :
    0 ≤ evidence T Z b a o := by
  unfold evidence
  exact Finset.sum_nonneg (fun sp _ => posteriorWeight_nonneg T Z b a o sp)

/-- Predictive observation law induced by the current belief. -/
def observationLaw {S A O : Type*} [Fintype S] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (b : FiniteLaw S) (a : A) : FiniteLaw O where
  mass := evidence T Z b a
  nonneg := evidence_nonneg T Z b a
  total_one := by
    classical
    unfold evidence posteriorWeight
    rw [Finset.sum_comm]
    calc
      Finset.univ.sum
          (fun sp => Finset.univ.sum
            (fun o => (predictLaw T b a).mass sp * (Z a sp).mass o)) =
          Finset.univ.sum
            (fun sp => (predictLaw T b a).mass sp *
              Finset.univ.sum (fun o => (Z a sp).mass o)) := by
            apply Finset.sum_congr rfl
            intro sp hsp
            rw [Finset.mul_sum]
      _ = Finset.univ.sum (fun sp => (predictLaw T b a).mass sp * 1) := by
            apply Finset.sum_congr rfl
            intro sp hsp
            rw [(Z a sp).total_one]
      _ = 1 := by simpa using (predictLaw T b a).total_one

/-- Positive-evidence exact Bayesian posterior. Zero-evidence observations are
intentionally excluded from this constructor. -/
def bayesUpdate {S A O : Type*} [Fintype S] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (b : FiniteLaw S) (a : A) (o : O)
    (hpos : 0 < evidence T Z b a o) : FiniteLaw S where
  mass := fun sp => posteriorWeight T Z b a o sp / evidence T Z b a o
  nonneg := by
    intro sp
    exact div_nonneg (posteriorWeight_nonneg T Z b a o sp) (le_of_lt hpos)
  total_one := by
    classical
    rw [← Finset.sum_div]
    unfold evidence
    exact div_self (ne_of_gt hpos)

/-- Bayesian update is extensional in the current belief. -/
theorem bayesUpdate_eq_of_belief_eq
    {S A O : Type*} [Fintype S] [Fintype O]
    {T : A → S → FiniteLaw S}
    {Z : A → S → FiniteLaw O}
    {b1 b2 : FiniteLaw S} {a : A} {o : O}
    (hb : b1 = b2)
    (h1 : 0 < evidence T Z b1 a o)
    (h2 : 0 < evidence T Z b2 a o) :
    bayesUpdate T Z b1 a o h1 = bayesUpdate T Z b2 a o h2 := by
  subst b2
  rfl

/-- Any history contract defined solely through a belief map is contract-sufficient. -/
def HistoryGoodViaBelief {History Belief A : Type*}
    (beta : History → Belief) (GoodBelief : Belief → A → Prop) : History → A → Prop :=
  fun h a => GoodBelief (beta h) a

/-- Definitional belief sufficiency for a history contract that depends only on
its generated belief. -/
theorem historyGoodViaBelief_sufficient
    {History Belief A : Type*}
    (beta : History → Belief) (GoodBelief : Belief → A → Prop) :
    BeliefSufficient beta (HistoryGoodViaBelief beta GoodBelief) GoodBelief := by
  intro h a
  rfl

/-- Explicit bridge to the previously verified belief-state quotient theorem. -/
theorem safeRep_historyViaBelief_iff_belief
    {History Belief A Y : Type*}
    {beta : History → Belief}
    {GoodBelief : Belief → A → Prop}
    {BH : Set History} {C : Set A} {r : Belief → Y} :
    SafeRep (HistoryGoodViaBelief beta GoodBelief) BH C (fun h => r (beta h)) ↔
      SafeRep GoodBelief (BeliefImage beta BH) C r := by
  exact safeRep_history_iff_belief (historyGoodViaBelief_sufficient beta GoodBelief)

end InsacermoActionabilityInformation
