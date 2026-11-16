/-
INSACERMO - cross-domain reuse of ONE information-barrier theorem.
Lean 4.20.0, isolated laboratory. No frozen kernel modifications.
The real Python/SQLite/Linux implementations are tested separately.
-/
import UnicodeDecisionGuard

namespace InsacermoCrossDomain
open InsacermoUnicodeDecisionGuard

theorem shared_refusal_rule {W O : Type}
    (observe : W → O) (label : W → Bool)
    (act : O → Option Bool)
    (safe : AlwaysSafe observe label act)
    (w₀ w₁ : W)
    (same : observe w₀ = observe w₁)
    (opposite : label w₀ ≠ label w₁) :
    act (observe w₀) = none := by
  exact collision_forces_refusal observe label act safe w₀ w₁ same opposite

inductive UnicodeWorld where
  | notEquals | equals
  deriving DecidableEq

def unicodeObserved : UnicodeWorld → String
  | .notEquals => "3 = 3"
  | .equals => "3 = 3"

def unicodeTruth : UnicodeWorld → Bool
  | .notEquals => false
  | .equals => true

theorem unicode_refusal (act : String → Option Bool)
    (safe : AlwaysSafe unicodeObserved unicodeTruth act) :
    act (unicodeObserved .notEquals) = none := by
  exact shared_refusal_rule unicodeObserved unicodeTruth act safe
    .notEquals .equals (by decide) (by decide)

inductive MoneyWorld where
  | below | above
  deriving DecidableEq

def cents : MoneyWorld → Nat
  | .below => 1049
  | .above => 1051

def moneyObserved (w : MoneyWorld) : Nat := cents w / 100

def moneyTruth (w : MoneyWorld) : Bool := decide (cents w ≥ 1050)

theorem money_observation_collision :
    moneyObserved .below = moneyObserved .above := by decide

theorem money_truth_opposite :
    moneyTruth .below ≠ moneyTruth .above := by decide

theorem money_refusal (act : Nat → Option Bool)
    (safe : AlwaysSafe moneyObserved moneyTruth act) :
    act (moneyObserved .below) = none := by
  exact shared_refusal_rule moneyObserved moneyTruth act safe
    .below .above money_observation_collision money_truth_opposite

inductive FileWorld where
  | public | restricted
  deriving DecidableEq

def fileObserved : FileWorld → String
  | .public => "report.txt"
  | .restricted => "report.txt"

def fileTruth : FileWorld → Bool
  | .public => true
  | .restricted => false

theorem file_refusal (act : String → Option Bool)
    (safe : AlwaysSafe fileObserved fileTruth act) :
    act (fileObserved .public) = none := by
  exact shared_refusal_rule fileObserved fileTruth act safe
    .public .restricted (by decide) (by decide)

theorem money_cannot_guess (classifier : Nat → Bool) :
    ¬ (classifier (moneyObserved .below) = moneyTruth .below ∧
       classifier (moneyObserved .above) = moneyTruth .above) := by
  exact no_two_correct moneyObserved moneyTruth classifier
    .below .above money_observation_collision money_truth_opposite

#print axioms shared_refusal_rule
#print axioms unicode_refusal
#print axioms money_refusal
#print axioms file_refusal
#print axioms money_cannot_guess

end InsacermoCrossDomain
