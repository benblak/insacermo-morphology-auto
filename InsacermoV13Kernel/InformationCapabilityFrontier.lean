import InsacermoV13Kernel.RawActionabilityBridge

namespace InsacermoV13Kernel

universe u v w z

/-- Every world is certified at the given observation level. -/
def GlobalSafe {World : Type u} {Obs : Type v} {Action : Type w}
    (obs : World → Obs) (available : Action → Prop)
    (admissible : World → Action → Prop) : Prop :=
  ∀ x, FiberSafe obs available admissible x

/-- Information refinement preserves global safety. -/
theorem globalSafe_of_refinement
    {World : Type u} {Coarse : Type v} {Fine : Type w} {Action : Type z}
    {coarse : World → Coarse} {fine : World → Fine}
    {available : Action → Prop} {admissible : World → Action → Prop}
    (href : Refines coarse fine)
    (hsafe : GlobalSafe coarse available admissible) :
    GlobalSafe fine available admissible := by
  intro x
  exact fiberSafe_of_refinement href (hsafe x)

/-- Capability expansion preserves global safety. -/
theorem globalSafe_of_capability_expansion
    {World : Type u} {Obs : Type v} {Action : Type w}
    {obs : World → Obs} {available₁ available₂ : Action → Prop}
    {admissible : World → Action → Prop}
    (hcap : ∀ ⦃a : Action⦄, available₁ a → available₂ a)
    (hsafe : GlobalSafe obs available₁ admissible) :
    GlobalSafe obs available₂ admissible := by
  intro x
  exact fiberSafe_of_capability_expansion hcap (hsafe x)

/-- Weakening a future contract cannot destroy an existing certificate. -/
theorem fiberSafe_of_contract_weakening
    {World : Type u} {Obs : Type v} {Action : Type w}
    {obs : World → Obs} {available : Action → Prop}
    {strong weak : World → Action → Prop} {x : World}
    (hweak : ∀ ⦃s : World⦄ ⦃a : Action⦄, strong s a → weak s a)
    (hsafe : FiberSafe obs available strong x) :
    FiberSafe obs available weak x := by
  rcases hsafe with ⟨a, haAvail, ha⟩
  refine ⟨a, haAvail, ?_⟩
  intro y hy
  exact hweak (ha hy)

/-- Contract weakening preserves global safety. -/
theorem globalSafe_of_contract_weakening
    {World : Type u} {Obs : Type v} {Action : Type w}
    {obs : World → Obs} {available : Action → Prop}
    {strong weak : World → Action → Prop}
    (hweak : ∀ ⦃s : World⦄ ⦃a : Action⦄, strong s a → weak s a)
    (hsafe : GlobalSafe obs available strong) :
    GlobalSafe obs available weak := by
  intro x
  exact fiberSafe_of_contract_weakening hweak (hsafe x)

/-- A safe encoding using the declared finite symbol budget n. -/
def SafeEncoding {World : Type u} {Action : Type v}
    (available : Action → Prop) (admissible : World → Action → Prop)
    (n : Nat) : Prop :=
  ∃ obs : World → Fin n, GlobalSafe obs available admissible

/-- Capability expansion preserves every already feasible information budget. -/
theorem safeEncoding_of_capability_expansion
    {World : Type u} {Action : Type v}
    {available₁ available₂ : Action → Prop}
    {admissible : World → Action → Prop} {n : Nat}
    (hcap : ∀ ⦃a : Action⦄, available₁ a → available₂ a)
    (henc : SafeEncoding available₁ admissible n) :
    SafeEncoding available₂ admissible n := by
  rcases henc with ⟨obs, hsafe⟩
  exact ⟨obs, globalSafe_of_capability_expansion hcap hsafe⟩

/-- Contract weakening preserves every already feasible information budget. -/
theorem safeEncoding_of_contract_weakening
    {World : Type u} {Action : Type v}
    {available : Action → Prop}
    {strong weak : World → Action → Prop} {n : Nat}
    (hweak : ∀ ⦃s : World⦄ ⦃a : Action⦄, strong s a → weak s a)
    (henc : SafeEncoding available strong n) :
    SafeEncoding available weak n := by
  rcases henc with ⟨obs, hsafe⟩
  exact ⟨obs, globalSafe_of_contract_weakening hweak hsafe⟩

/-- m is a genuine minimum number of observation symbols sufficient
    for global contract safety. This avoids assuming existence globally. -/
def IsMinSafeSymbols {World : Type u} {Action : Type v}
    (available : Action → Prop) (admissible : World → Action → Prop)
    (m : Nat) : Prop :=
  SafeEncoding available admissible m ∧
    ∀ n, SafeEncoding available admissible n → m ≤ n

/-- Capability can buy the right to forget, weak law:
    whenever minima exist before and after capability expansion, the minimum
    sufficient symbol budget cannot increase. -/
theorem minSafeSymbols_antitone_capability
    {World : Type u} {Action : Type v}
    {available₁ available₂ : Action → Prop}
    {admissible : World → Action → Prop}
    {m₁ m₂ : Nat}
    (hcap : ∀ ⦃a : Action⦄, available₁ a → available₂ a)
    (hmin₁ : IsMinSafeSymbols available₁ admissible m₁)
    (hmin₂ : IsMinSafeSymbols available₂ admissible m₂) :
    m₂ ≤ m₁ := by
  apply hmin₂.2 m₁
  exact safeEncoding_of_capability_expansion hcap hmin₁.1

/-- A stronger future contract cannot require fewer observation symbols,
    whenever the corresponding minima exist. -/
theorem minSafeSymbols_monotone_contract
    {World : Type u} {Action : Type v}
    {available : Action → Prop}
    {strong weak : World → Action → Prop}
    {mStrong mWeak : Nat}
    (hweak : ∀ ⦃s : World⦄ ⦃a : Action⦄, strong s a → weak s a)
    (hminStrong : IsMinSafeSymbols available strong mStrong)
    (hminWeak : IsMinSafeSymbols available weak mWeak) :
    mWeak ≤ mStrong := by
  apply hminWeak.2 mStrong
  exact safeEncoding_of_contract_weakening hweak hminStrong.1

/-- A common action for every world in a subset. -/
def CommonAction {World : Type u} {Action : Type v}
    (B : World → Prop) (available : Action → Prop)
    (admissible : World → Action → Prop) : Prop :=
  ∃ a, available a ∧ ∀ ⦃x : World⦄, B x → admissible x a

/-- A subset is obstructed when it has no common currently available action. -/
def Obstructed {World : Type u} {Action : Type v}
    (B : World → Prop) (available : Action → Prop)
    (admissible : World → Action → Prop) : Prop :=
  ¬ CommonAction B available admissible

/-- Fiber safety is exactly common-action feasibility of the observation fiber. -/
theorem fiberSafe_iff_commonAction_fiber
    {World : Type u} {Obs : Type v} {Action : Type w}
    {obs : World → Obs} {available : Action → Prop}
    {admissible : World → Action → Prop} {x : World} :
    FiberSafe obs available admissible x ↔
      CommonAction (fun y => obs y = obs x) available admissible := by
  rfl

/-- A failed fiber certificate is exactly an obstruction on that fiber. -/
theorem not_fiberSafe_iff_obstructed_fiber
    {World : Type u} {Obs : Type v} {Action : Type w}
    {obs : World → Obs} {available : Action → Prop}
    {admissible : World → Action → Prop} {x : World} :
    (¬ FiberSafe obs available admissible x) ↔
      Obstructed (fun y => obs y = obs x) available admissible := by
  rfl

/-- Feasibility of an information/capability pair. -/
def FeasiblePair {World : Type u} {Obs : Type v} {Action : Type w}
    (obs : World → Obs) (available : Action → Prop)
    (admissible : World → Action → Prop) : Prop :=
  GlobalSafe obs available admissible

/-- Moving upward in information refinement stays inside the feasible region. -/
theorem feasiblePair_upward_information
    {World : Type u} {Coarse : Type v} {Fine : Type w} {Action : Type z}
    {coarse : World → Coarse} {fine : World → Fine}
    {available : Action → Prop} {admissible : World → Action → Prop}
    (href : Refines coarse fine)
    (h : FeasiblePair coarse available admissible) :
    FeasiblePair fine available admissible :=
  globalSafe_of_refinement href h

/-- Moving upward in capability stays inside the feasible region. -/
theorem feasiblePair_upward_capability
    {World : Type u} {Obs : Type v} {Action : Type w}
    {obs : World → Obs} {available₁ available₂ : Action → Prop}
    {admissible : World → Action → Prop}
    (hcap : ∀ ⦃a : Action⦄, available₁ a → available₂ a)
    (h : FeasiblePair obs available₁ admissible) :
    FeasiblePair obs available₂ admissible :=
  globalSafe_of_capability_expansion hcap h

namespace RightToForgetWitness

inductive World
  | a | b

inductive FineObs
  | a | b

inductive CoarseObs
  | one

inductive Action
  | aOnly | bOnly | universal

def fine : World → FineObs
  | .a => .a
  | .b => .b

def coarse : World → CoarseObs
  | _ => .one

def admissible : World → Action → Prop
  | .a, .aOnly => True
  | .b, .bOnly => True
  | _, .universal => True
  | _, _ => False

def availableBase : Action → Prop
  | .aOnly => True
  | .bOnly => True
  | .universal => False

def availableExpanded : Action → Prop
  | _ => True

theorem fine_refines_coarse : Refines coarse fine := by
  intro x y h
  rfl

theorem fine_safe_base : GlobalSafe fine availableBase admissible := by
  intro x
  cases x with
  | a =>
      refine ⟨Action.aOnly, True.intro, ?_⟩
      intro y hy
      cases y with
      | a => exact True.intro
      | b => cases hy
  | b =>
      refine ⟨Action.bOnly, True.intro, ?_⟩
      intro y hy
      cases y with
      | a => cases hy
      | b => exact True.intro

theorem coarse_not_safe_base :
    ¬ GlobalSafe coarse availableBase admissible := by
  intro h
  have hs := h World.a
  rcases hs with ⟨act, hAvail, hall⟩
  cases act with
  | aOnly =>
      have hbad : admissible World.b Action.aOnly :=
        hall (y := World.b) rfl
      exact hbad
  | bOnly =>
      have hbad : admissible World.a Action.bOnly :=
        hall (y := World.a) rfl
      exact hbad
  | universal =>
      exact hAvail

theorem coarse_safe_expanded :
    GlobalSafe coarse availableExpanded admissible := by
  intro x
  refine ⟨Action.universal, True.intro, ?_⟩
  intro y hy
  cases y <;> exact True.intro

/-- Strict finite witness: adding one universal capability makes a constant
    one-symbol representation safe although it was unsafe before. -/
theorem strict_right_to_forget_witness :
    Refines coarse fine ∧
    GlobalSafe fine availableBase admissible ∧
    (¬ GlobalSafe coarse availableBase admissible) ∧
    GlobalSafe coarse availableExpanded admissible := by
  exact ⟨fine_refines_coarse, fine_safe_base,
    coarse_not_safe_base, coarse_safe_expanded⟩

end RightToForgetWitness

namespace CapabilityComplementarityWitness

inductive World
  | l0 | l1 | r0 | r1

inductive Obs
  | left | right

inductive Action
  | u | v

def obs : World → Obs
  | .l0 | .l1 => .left
  | .r0 | .r1 => .right

def admissible : World → Action → Prop
  | .l0, .u => True
  | .l1, .u => True
  | .r0, .v => True
  | .r1, .v => True
  | _, _ => False

def availableU : Action → Prop
  | .u => True
  | .v => False

def availableV : Action → Prop
  | .u => False
  | .v => True

def availableBoth : Action → Prop
  | _ => True

theorem globalSafe_both :
    GlobalSafe obs availableBoth admissible := by
  intro x
  cases x with
  | l0 =>
      refine ⟨Action.u, True.intro, ?_⟩
      intro y hy
      cases y with
      | l0 => exact True.intro
      | l1 => exact True.intro
      | r0 => cases hy
      | r1 => cases hy
  | l1 =>
      refine ⟨Action.u, True.intro, ?_⟩
      intro y hy
      cases y with
      | l0 => exact True.intro
      | l1 => exact True.intro
      | r0 => cases hy
      | r1 => cases hy
  | r0 =>
      refine ⟨Action.v, True.intro, ?_⟩
      intro y hy
      cases y with
      | l0 => cases hy
      | l1 => cases hy
      | r0 => exact True.intro
      | r1 => exact True.intro
  | r1 =>
      refine ⟨Action.v, True.intro, ?_⟩
      intro y hy
      cases y with
      | l0 => cases hy
      | l1 => cases hy
      | r0 => exact True.intro
      | r1 => exact True.intro

theorem not_globalSafe_U :
    ¬ GlobalSafe obs availableU admissible := by
  intro h
  have hs := h World.r0
  rcases hs with ⟨act, hAvail, hall⟩
  cases act with
  | u =>
      have hbad : admissible World.r0 Action.u :=
        hall (y := World.r0) rfl
      exact hbad
  | v =>
      exact hAvail

theorem not_globalSafe_V :
    ¬ GlobalSafe obs availableV admissible := by
  intro h
  have hs := h World.l0
  rcases hs with ⟨act, hAvail, hall⟩
  cases act with
  | u =>
      exact hAvail
  | v =>
      have hbad : admissible World.l0 Action.v :=
        hall (y := World.l0) rfl
      exact hbad

/-- Capability complementarity exists: neither capability alone certifies the
    fixed coarse representation, while the pair does. -/
theorem capability_complementarity_exists :
    (¬ GlobalSafe obs availableU admissible) ∧
    (¬ GlobalSafe obs availableV admissible) ∧
    GlobalSafe obs availableBoth admissible := by
  exact ⟨not_globalSafe_U, not_globalSafe_V, globalSafe_both⟩

end CapabilityComplementarityWitness

end InsacermoV13Kernel
