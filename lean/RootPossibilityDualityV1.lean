import Std

/-!
INSACERMO ROOT V1 — THE TWO SIDES OF POSSIBILITY.
A finite or infinite set of worlds W, candidate actions A, and a declared
success relation Good : W → A → Prop.

No observation, ML, or cost optimization is assumed by this nucleus.
It proves the structural relation among information (candidate worlds),
capability (available actions), preservation (additional contracts), and
robust actionability. An entirely separate theorem shows why immediate
action-set compression cannot in general preserve dynamic planning.

The Galois connection is CLASSICAL formal concept analysis,
not a claim of a new mathematical structure.
-/

namespace INSACERMO.Root

universe u v

def Common {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop) : A → Prop :=
  fun a => ∀ w, X w → Good w a

def Worlds {W : Type u} {A : Type v}
    (Good : W → A → Prop) (C : A → Prop) : W → Prop :=
  fun w => ∀ a, C a → Good w a

def Closure {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop) : W → Prop :=
  Worlds Good (Common Good X)

/-- Contravariant Galois duality: common actions versus common worlds. -/
theorem galois_iff {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop) (C : A → Prop) :
    (∀ a, C a → Common Good X a) ↔
    (∀ w, X w → Worlds Good C w) := by
  constructor
  · intro h w hw a ha
    exact h a ha w hw
  · intro h a ha w hw
    exact h w hw a ha

theorem antitone_information {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X Y : W → Prop)
    (h : ∀ w, X w → Y w) :
    ∀ a, Common Good Y a → Common Good X a := by
  intro a ha w hw
  exact ha w (h w hw)

theorem antitone_requirements {W : Type u} {A : Type v}
    (G H : W → A → Prop) (X : W → Prop) :
    ∀ a, Common (fun w a => G w a ∧ H w a) X a →
      Common G X a := by
  intro a ha w hw
  exact (ha w hw).1

def Robust {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop) : Prop :=
  ∃ a, Common Good X a

def AllowedRobust {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop)
    (Allowed : A → Prop) : Prop :=
  ∃ a, Allowed a ∧ Common Good X a

theorem enlarging_capability_preserves_act {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop)
    (C D : A → Prop)
    (h : ∀ a, C a → D a) :
    AllowedRobust Good X C → AllowedRobust Good X D := by
  rintro ⟨a, hc, ha⟩
  exact ⟨a, h a hc, ha⟩

theorem closure_contains_input {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop) :
    ∀ w, X w → Closure Good X w := by
  intro w hw a ha
  exact ha w hw

theorem closure_preserves_all_current_actions {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop) :
    ∀ a, Common Good (Closure Good X) a ↔ Common Good X a := by
  intro a
  constructor
  · intro h w hw
    exact h w (closure_contains_input Good X w hw)
  · intro h w hw
    exact hw a h

theorem closure_idempotent {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop) :
    ∀ w, Closure Good (Closure Good X) w ↔ Closure Good X w := by
  intro w
  constructor
  · intro h a ha
    have ha' : Common Good (Closure Good X) a :=
      (closure_preserves_all_current_actions Good X a).2 ha
    exact h a ha'
  · intro h a ha
    have ha' : Common Good X a :=
      (closure_preserves_all_current_actions Good X a).1 ha
    exact h a ha'

theorem closure_preserves_robust_act {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop) :
    Robust Good (Closure Good X) ↔ Robust Good X := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (closure_preserves_all_current_actions Good X a).1 ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (closure_preserves_all_current_actions Good X a).2 ha⟩

def LocalCapable {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop) : Prop :=
  ∀ w, X w → ∃ a, Good w a

theorem robust_implies_local {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop) :
    Robust Good X → LocalCapable Good X := by
  rintro ⟨a, ha⟩ w hw
  exact ⟨a, ha w hw⟩

/- Pure observations can choose among actions but cannot change Good. -/
inductive ReadOnlyPlan (W : Type u) (A : Type v) : Type (max u v) where
  | act : A → ReadOnlyPlan W A
  | observe : (W → Bool) → ReadOnlyPlan W A →
      ReadOnlyPlan W A → ReadOnlyPlan W A

def executeReadOnly {W : Type u} {A : Type v}
    (t : ReadOnlyPlan W A) (w : W) : A :=
  match t with
  | .act a => a
  | .observe q yes no =>
      if q w then executeReadOnly yes w else executeReadOnly no w

def ReadOnlySafe {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop)
    (t : ReadOnlyPlan W A) : Prop :=
  ∀ w, X w → Good w (executeReadOnly t w)

/-- A guarantee from read-only observations requires per-world capability. -/
theorem observations_cannot_create_capability
    {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop)
    (t : ReadOnlyPlan W A) :
    ReadOnlySafe Good X t → LocalCapable Good X := by
  intro h w hw
  exact ⟨executeReadOnly t w, h w hw⟩

/-- Strong impossibility: even unlimited perfect read-only observations
    cannot solve a world for which no declared action succeeds. -/
theorem no_pure_information_can_repair_absent_capability
    {W : Type u} {A : Type v}
    (Good : W → A → Prop) (X : W → Prop)
    (w₀ : W) (hw : X w₀)
    (hbad : ∀ a, ¬ Good w₀ a)
    (t : ReadOnlyPlan W A) :
    ¬ ReadOnlySafe Good X t := by
  intro hs
  have hc := observations_cannot_create_capability Good X t hs
  obtain ⟨a, ha⟩ := hc w₀ hw
  exact hbad a ha

/- Two worlds, two exclusive actions: knowledge changes the verdict. -/
def CoinGood (w a : Bool) : Prop := w = a

theorem ambiguous_worlds_not_robust :
    ¬ Robust CoinGood (fun _ : Bool => True) := by
  intro ⟨a, ha⟩
  cases a with
  | false =>
      exact Bool.noConfusion (ha true trivial)
  | true =>
      exact Bool.noConfusion (ha false trivial)

def CoinPlan : ReadOnlyPlan Bool Bool :=
  .observe (fun w => w) (.act true) (.act false)

theorem information_resolves_ambiguity :
    ReadOnlySafe CoinGood (fun _ : Bool => True) CoinPlan := by
  intro w _
  cases w <;> rfl

/-- A single new universal repair action removes the obstruction. -/
inductive FixedAction where
  | original : Bool → FixedAction
  | repaired : FixedAction

def CoinRepairedGood (w : Bool) : FixedAction → Prop
  | .original a => CoinGood w a
  | .repaired => True

theorem one_new_capability_removes_obstruction :
    Robust CoinRepairedGood (fun _ : Bool => True) := by
  exact ⟨.repaired, fun _ _ => trivial⟩

/- Important warning for planning: identical immediate available actions
   DOES NOT imply equivalence under subsequent observations. -/
def TripleGood (w : Fin 3) (a : Bool) : Prop :=
  w.val = (if a then 1 else 0)

def Xpair (w : Fin 3) : Prop := w.val < 2
def Ypair (w : Fin 3) : Prop := w.val ≠ 1

def TriplePlan : ReadOnlyPlan (Fin 3) Bool :=
  .observe (fun w => w.val == 1) (.act true) (.act false)

theorem same_immediate_actions_but_different_futures :
    (∀ a : Bool, Common TripleGood Xpair a ↔
      Common TripleGood Ypair a) ∧
    ReadOnlySafe TripleGood Xpair TriplePlan ∧
    ¬ ReadOnlySafe TripleGood Ypair TriplePlan := by
  decide

end INSACERMO.Root
