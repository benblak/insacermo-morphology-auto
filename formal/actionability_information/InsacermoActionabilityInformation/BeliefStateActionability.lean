import InsacermoActionabilityInformation.HypergraphActionability

namespace InsacermoActionabilityInformation

/-- A belief representation is contract-sufficient when history-level
admissibility factors exactly through the belief map. -/
def BeliefSufficient {History Belief A : Type*}
    (beta : History → Belief)
    (GoodHistory : History → A → Prop)
    (GoodBelief : Belief → A → Prop) : Prop :=
  ∀ h a, GoodHistory h a ↔ GoodBelief (beta h) a

/-- Realized belief image of an admissible history set. -/
def BeliefImage {History Belief : Type*}
    (beta : History → Belief) (BH : Set History) : Set Belief :=
  beta '' BH

/-- If the contract factors through belief, then any actionability certificate
on histories induces one on the realized belief image. -/
theorem safeRep_history_to_belief
    {History Belief A Y : Type*}
    {beta : History → Belief}
    {GoodHistory : History → A → Prop}
    {GoodBelief : Belief → A → Prop}
    {BH : Set History} {C : Set A} {r : Belief → Y}
    (hsuff : BeliefSufficient beta GoodHistory GoodBelief)
    (hsafe : SafeRep GoodHistory BH C (fun h => r (beta h))) :
    SafeRep GoodBelief (BeliefImage beta BH) C r := by
  intro y hy
  rcases hy with ⟨b, hbimg, hby⟩
  rcases hbimg with ⟨h0, hh0B, rfl⟩
  have hreal : ∃ h, h ∈ BH ∧ r (beta h) = y := ⟨h0, hh0B, hby⟩
  rcases hsafe y hreal with ⟨a, haC, hgood⟩
  refine ⟨a, haC, ?_⟩
  intro b hbimg' hby'
  rcases hbimg' with ⟨h, hhB, rfl⟩
  have gh : GoodHistory h a := hgood h hhB hby'
  exact (hsuff h a).mp gh

/-- Conversely, belief-level actionability on the realized image lifts back to
history-level actionability whenever admissibility factors through belief. -/
theorem safeRep_belief_to_history
    {History Belief A Y : Type*}
    {beta : History → Belief}
    {GoodHistory : History → A → Prop}
    {GoodBelief : Belief → A → Prop}
    {BH : Set History} {C : Set A} {r : Belief → Y}
    (hsuff : BeliefSufficient beta GoodHistory GoodBelief)
    (hsafe : SafeRep GoodBelief (BeliefImage beta BH) C r) :
    SafeRep GoodHistory BH C (fun h => r (beta h)) := by
  intro y hy
  rcases hy with ⟨h0, hh0B, hh0y⟩
  have himg : beta h0 ∈ BeliefImage beta BH := ⟨h0, hh0B, rfl⟩
  have hrealB : ∃ b, b ∈ BeliefImage beta BH ∧ r b = y :=
    ⟨beta h0, himg, hh0y⟩
  rcases hsafe y hrealB with ⟨a, haC, hgood⟩
  refine ⟨a, haC, ?_⟩
  intro h hhB hhy
  have hbimg : beta h ∈ BeliefImage beta BH := ⟨h, hhB, rfl⟩
  have gb : GoodBelief (beta h) a := hgood (beta h) hbimg hhy
  exact (hsuff h a).mpr gb

/-- Exact lossless-quotient theorem: under contract sufficiency, actionability
through a belief representation is equivalent at history and belief levels. -/
theorem safeRep_history_iff_belief
    {History Belief A Y : Type*}
    {beta : History → Belief}
    {GoodHistory : History → A → Prop}
    {GoodBelief : Belief → A → Prop}
    {BH : Set History} {C : Set A} {r : Belief → Y}
    (hsuff : BeliefSufficient beta GoodHistory GoodBelief) :
    SafeRep GoodHistory BH C (fun h => r (beta h)) ↔
      SafeRep GoodBelief (BeliefImage beta BH) C r := by
  constructor
  · exact safeRep_history_to_belief hsuff
  · exact safeRep_belief_to_history hsuff

/-- On a finite belief space, the existing hypergraph characterization applies
without modification once the belief-level contract has been established. -/
theorem beliefSafeRep_iff_hypergraphSafe
    {Belief A Y : Type*} [Fintype Belief] [DecidableEq Belief]
    {GoodBelief : Belief → A → Prop}
    {B : Set Belief} {C : Set A} {r : Belief → Y} :
    SafeRep GoodBelief B C r ↔ HypergraphSafe GoodBelief B C r := by
  exact safeRep_iff_hypergraphSafe

/-- If two histories collapse to the same belief while disagreeing on the
history-level contract for some action, no belief-level contract can factor
exactly through that belief map. -/
theorem sameBelief_contractDisagreement_blocks_sufficiency
    {History Belief A : Type*}
    {beta : History → Belief}
    {GoodHistory : History → A → Prop}
    {GoodBelief : Belief → A → Prop}
    {h1 h2 : History} {a : A}
    (halias : beta h1 = beta h2)
    (hgap : GoodHistory h1 a ↔ ¬ GoodHistory h2 a) :
    ¬ BeliefSufficient beta GoodHistory GoodBelief := by
  intro hsuff
  by_cases h1good : GoodHistory h1 a
  · have gb1 : GoodBelief (beta h1) a := (hsuff h1 a).mp h1good
    have gb2 : GoodBelief (beta h2) a := by simpa [halias] using gb1
    have h2good : GoodHistory h2 a := (hsuff h2 a).mpr gb2
    exact (hgap.mp h1good) h2good
  · have h2good : GoodHistory h2 a := by
      by_contra h2bad
      exact h1good (hgap.mpr h2bad)
    have gb2 : GoodBelief (beta h2) a := (hsuff h2 a).mp h2good
    have gb1 : GoodBelief (beta h1) a := by simpa [halias] using gb2
    exact h1good ((hsuff h1 a).mpr gb1)

end InsacermoActionabilityInformation
