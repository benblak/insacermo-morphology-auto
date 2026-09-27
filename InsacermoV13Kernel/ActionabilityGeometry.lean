import InsacermoV13Kernel.InformationCapabilityCover

namespace InsacermoV13Kernel

universe u v w z

/-- Simultaneous monotonicity of the INSACERMO feasible region:
    more information, more capability, and a weaker contract preserve safety. -/
theorem globalSafe_three_axis_monotonicity
    {World : Type u}
    {Coarse : Type v} {Fine : Type w} {Action : Type z}
    {coarse : World → Coarse} {fine : World → Fine}
    {available₁ available₂ : Action → Prop}
    {strong weak : World → Action → Prop}
    (href : Refines coarse fine)
    (hcap : ∀ ⦃a : Action⦄, available₁ a → available₂ a)
    (hcontract : ∀ ⦃s : World⦄ ⦃a : Action⦄, strong s a → weak s a)
    (hsafe : GlobalSafe coarse available₁ strong) :
    GlobalSafe fine available₂ weak := by
  have h1 : GlobalSafe fine available₁ strong :=
    globalSafe_of_refinement href hsafe
  have h2 : GlobalSafe fine available₂ strong :=
    globalSafe_of_capability_expansion hcap h1
  exact globalSafe_of_contract_weakening hcontract h2

/-- The finite feasible-information budget is monotone under simultaneous
    capability expansion and contract weakening. -/
theorem safeEncoding_three_axis_monotonicity
    {World : Type u} {Action : Type v}
    {available₁ available₂ : Action → Prop}
    {strong weak : World → Action → Prop}
    {n : Nat}
    (hcap : ∀ ⦃a : Action⦄, available₁ a → available₂ a)
    (hcontract : ∀ ⦃s : World⦄ ⦃a : Action⦄, strong s a → weak s a)
    (henc : SafeEncoding available₁ strong n) :
    SafeEncoding available₂ weak n := by
  have h1 : SafeEncoding available₂ strong n :=
    safeEncoding_of_capability_expansion hcap henc
  exact safeEncoding_of_contract_weakening hcontract h1

/-- An abstract dominance relation between two information/capability states.
    The left state dominates the right when it has at least as fine information
    and at least as many currently available capabilities. -/
def InfoCapDominates
    {World : Type u} {Obs₁ : Type v} {Obs₂ : Type w} {Action : Type z}
    (obs₁ : World → Obs₁) (available₁ : Action → Prop)
    (obs₂ : World → Obs₂) (available₂ : Action → Prop) : Prop :=
  Refines obs₂ obs₁ ∧
    ∀ ⦃a : Action⦄, available₂ a → available₁ a

/-- Feasibility is upward closed under information-capability dominance. -/
theorem feasible_of_dominance
    {World : Type u} {Obs₁ : Type v} {Obs₂ : Type w} {Action : Type z}
    {obs₁ : World → Obs₁} {available₁ : Action → Prop}
    {obs₂ : World → Obs₂} {available₂ : Action → Prop}
    {admissible : World → Action → Prop}
    (hdom : InfoCapDominates obs₁ available₁ obs₂ available₂)
    (hsafe : GlobalSafe obs₂ available₂ admissible) :
    GlobalSafe obs₁ available₁ admissible := by
  have h1 : GlobalSafe obs₁ available₂ admissible :=
    globalSafe_of_refinement hdom.1 hsafe
  exact globalSafe_of_capability_expansion hdom.2 h1

/-- Natural-number right-to-forget dividend in symbol units. -/
def ForgetDividend (before after : Nat) : Nat :=
  before - after

namespace StrictSynergyWitness

inductive World
  | left | right

inductive Action
  | leftOnly | rightOnly | uLocal | vLocal | joint

def admissible : World → Action → Prop
  | .left, .leftOnly => True
  | .right, .rightOnly => True
  | .left, .uLocal => True
  | .right, .vLocal => True
  | _, .joint => True
  | _, _ => False

def availableBase : Action → Prop
  | .leftOnly | .rightOnly => True
  | _ => False

def availableU : Action → Prop
  | .leftOnly | .rightOnly | .uLocal => True
  | _ => False

def availableV : Action → Prop
  | .leftOnly | .rightOnly | .vLocal => True
  | _ => False

def availableBoth : Action → Prop
  | _ => True

def fine : World → Fin 2
  | .left => 0
  | .right => 1

def coarse : World → Fin 1
  | _ => 0

theorem fine_safe
    (available : Action → Prop)
    (hleft : available Action.leftOnly)
    (hright : available Action.rightOnly) :
    GlobalSafe fine available admissible := by
  intro x
  cases x with
  | left =>
      refine ⟨Action.leftOnly, hleft, ?_⟩
      intro y hy
      cases y with
      | left => exact True.intro
      | right => cases hy
  | right =>
      refine ⟨Action.rightOnly, hright, ?_⟩
      intro y hy
      cases y with
      | left => cases hy
      | right => exact True.intro

theorem safeEncoding_two_base :
    SafeEncoding availableBase admissible 2 :=
  ⟨fine, fine_safe availableBase True.intro True.intro⟩

theorem safeEncoding_two_U :
    SafeEncoding availableU admissible 2 :=
  ⟨fine, fine_safe availableU True.intro True.intro⟩

theorem safeEncoding_two_V :
    SafeEncoding availableV admissible 2 :=
  ⟨fine, fine_safe availableV True.intro True.intro⟩

theorem coarse_not_safe
    (available : Action → Prop)
    (hjoint : ¬ available Action.joint)
    (huRight : ¬ available Action.uLocal ∨
      ¬ admissible World.right Action.uLocal)
    (hvLeft : ¬ available Action.vLocal ∨
      ¬ admissible World.left Action.vLocal) :
    ¬ GlobalSafe coarse available admissible := by
  intro h
  have hs := h World.left
  rcases hs with ⟨a, ha, hall⟩
  have hleft : admissible World.left a := hall (y := World.left) rfl
  have hright : admissible World.right a := hall (y := World.right) rfl
  cases a with
  | leftOnly => exact hright
  | rightOnly => exact hleft
  | uLocal =>
      rcases huRight with hna | hbad
      · exact hna ha
      · exact hbad hright
  | vLocal =>
      rcases hvLeft with hna | hbad
      · exact hna ha
      · exact hbad hleft
  | joint => exact hjoint ha

theorem coarse_not_safe_base :
    ¬ GlobalSafe coarse availableBase admissible := by
  apply coarse_not_safe availableBase
  · exact id
  · exact Or.inl id
  · exact Or.inl id

theorem coarse_not_safe_U :
    ¬ GlobalSafe coarse availableU admissible := by
  apply coarse_not_safe availableU
  · exact id
  · exact Or.inr id
  · exact Or.inl id

theorem coarse_not_safe_V :
    ¬ GlobalSafe coarse availableV admissible := by
  apply coarse_not_safe availableV
  · exact id
  · exact Or.inl id
  · exact Or.inr id

theorem coarse_safe_both :
    GlobalSafe coarse availableBoth admissible := by
  intro x
  refine ⟨Action.joint, True.intro, ?_⟩
  intro y hy
  cases y <;> exact True.intro

theorem safeEncoding_one_both :
    SafeEncoding availableBoth admissible 1 :=
  ⟨coarse, coarse_safe_both⟩

theorem no_safeEncoding_zero
    (available : Action → Prop) :
    ¬ SafeEncoding available admissible 0 := by
  intro h
  rcases h with ⟨obs, hsafe⟩
  exact Fin.elim0 (obs World.left)

theorem one_symbol_forces_coarse_unsafe
    {available : Action → Prop}
    (hcoarse : ¬ GlobalSafe coarse available admissible) :
    ¬ SafeEncoding available admissible 1 := by
  intro h
  rcases h with ⟨obs, hsafe⟩
  have halias : obs World.right = obs World.left :=
    Subsingleton.elim _ _
  have hleft := hsafe World.left
  rcases hleft with ⟨a, ha, hall⟩
  apply hcoarse
  intro x
  refine ⟨a, ha, ?_⟩
  intro y hy
  cases x with
  | left =>
      exact hall (Subsingleton.elim _ _)
  | right =>
      exact hall (Subsingleton.elim _ _)

theorem min_two_of_two_safe_one_unsafe
    {available : Action → Prop}
    (htwo : SafeEncoding available admissible 2)
    (hone : ¬ SafeEncoding available admissible 1) :
    IsMinSafeSymbols available admissible 2 := by
  refine ⟨htwo, ?_⟩
  intro n hn
  cases n with
  | zero =>
      exact False.elim ((no_safeEncoding_zero available) hn)
  | succ n =>
      cases n with
      | zero =>
          exact False.elim (hone hn)
      | succ k =>
          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))

theorem min_one_of_one_safe
    {available : Action → Prop}
    (hone : SafeEncoding available admissible 1) :
    IsMinSafeSymbols available admissible 1 := by
  refine ⟨hone, ?_⟩
  intro n hn
  cases n with
  | zero =>
      exact False.elim ((no_safeEncoding_zero available) hn)
  | succ k =>
      exact Nat.succ_le_succ (Nat.zero_le k)

theorem min_base_two :
    IsMinSafeSymbols availableBase admissible 2 :=
  min_two_of_two_safe_one_unsafe
    safeEncoding_two_base
    (one_symbol_forces_coarse_unsafe coarse_not_safe_base)

theorem min_U_two :
    IsMinSafeSymbols availableU admissible 2 :=
  min_two_of_two_safe_one_unsafe
    safeEncoding_two_U
    (one_symbol_forces_coarse_unsafe coarse_not_safe_U)

theorem min_V_two :
    IsMinSafeSymbols availableV admissible 2 :=
  min_two_of_two_safe_one_unsafe
    safeEncoding_two_V
    (one_symbol_forces_coarse_unsafe coarse_not_safe_V)

theorem min_both_one :
    IsMinSafeSymbols availableBoth admissible 1 :=
  min_one_of_one_safe safeEncoding_one_both

/-- Strict non-additive synergy:
    neither U nor V alone buys any information reduction, but together they
    reduce the exact minimum symbol budget from 2 to 1. -/
theorem strict_nonadditive_right_to_forget :
    IsMinSafeSymbols availableBase admissible 2 ∧
    IsMinSafeSymbols availableU admissible 2 ∧
    IsMinSafeSymbols availableV admissible 2 ∧
    IsMinSafeSymbols availableBoth admissible 1 ∧
    ForgetDividend 2 2 = 0 ∧
    ForgetDividend 2 1 = 1 := by
  exact ⟨min_base_two, min_U_two, min_V_two, min_both_one, rfl, rfl⟩

end StrictSynergyWitness

namespace FrontierBranchWitness

inductive World
  | w00 | w01 | w10 | w11

inductive Bit
  | zero | one

inductive Action
  | row0 | row1 | col0 | col1

def rowObs : World → Bit
  | .w00 | .w01 => .zero
  | .w10 | .w11 => .one

def colObs : World → Bit
  | .w00 | .w10 => .zero
  | .w01 | .w11 => .one

def rowAvailable : Action → Prop
  | .row0 | .row1 => True
  | _ => False

def colAvailable : Action → Prop
  | .col0 | .col1 => True
  | _ => False

def admissible : World → Action → Prop
  | .w00, .row0 => True
  | .w01, .row0 => True
  | .w10, .row1 => True
  | .w11, .row1 => True
  | .w00, .col0 => True
  | .w10, .col0 => True
  | .w01, .col1 => True
  | .w11, .col1 => True
  | _, _ => False

theorem row_safe : GlobalSafe rowObs rowAvailable admissible := by
  intro x
  cases x with
  | w00 =>
      refine ⟨Action.row0, True.intro, ?_⟩
      intro y hy
      cases y <;> cases hy <;> trivial
  | w01 =>
      refine ⟨Action.row0, True.intro, ?_⟩
      intro y hy
      cases y <;> cases hy <;> trivial
  | w10 =>
      refine ⟨Action.row1, True.intro, ?_⟩
      intro y hy
      cases y <;> cases hy <;> trivial
  | w11 =>
      refine ⟨Action.row1, True.intro, ?_⟩
      intro y hy
      cases y <;> cases hy <;> trivial

theorem col_safe : GlobalSafe colObs colAvailable admissible := by
  intro x
  cases x with
  | w00 =>
      refine ⟨Action.col0, True.intro, ?_⟩
      intro y hy
      cases y <;> cases hy <;> trivial
  | w01 =>
      refine ⟨Action.col1, True.intro, ?_⟩
      intro y hy
      cases y <;> cases hy <;> trivial
  | w10 =>
      refine ⟨Action.col0, True.intro, ?_⟩
      intro y hy
      cases y <;> cases hy <;> trivial
  | w11 =>
      refine ⟨Action.col1, True.intro, ?_⟩
      intro y hy
      cases y <;> cases hy <;> trivial

theorem not_row_refines_col : ¬ Refines colObs rowObs := by
  intro h
  have := h (x := World.w00) (y := World.w01) rfl
  cases this

theorem not_col_refines_row : ¬ Refines rowObs colObs := by
  intro h
  have := h (x := World.w00) (y := World.w10) rfl
  cases this

theorem not_row_cap_contains_col :
    ¬ (∀ ⦃a : Action⦄, colAvailable a → rowAvailable a) := by
  intro h
  exact h (a := Action.col0) True.intro

theorem not_col_cap_contains_row :
    ¬ (∀ ⦃a : Action⦄, rowAvailable a → colAvailable a) := by
  intro h
  exact h (a := Action.row0) True.intro

/-- Two safe information-capability designs can be mutually incomparable.
    Thus the feasible frontier need not collapse to a single chain. -/
theorem incomparable_safe_branches :
    GlobalSafe rowObs rowAvailable admissible ∧
    GlobalSafe colObs colAvailable admissible ∧
    (¬ InfoCapDominates rowObs rowAvailable colObs colAvailable) ∧
    (¬ InfoCapDominates colObs colAvailable rowObs rowAvailable) := by
  refine ⟨row_safe, col_safe, ?_, ?_⟩
  · intro h
    exact not_row_refines_col h.1
  · intro h
    exact not_col_refines_row h.1

end FrontierBranchWitness

end InsacermoV13Kernel
