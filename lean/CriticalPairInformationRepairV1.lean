import Std

/-!
INSACERMO TOTAL: Critical pair cost under nondeterministic observations.
Model-relative rational/integer-scaled interval constraints.
Does NOT certify physical measurement reliability or general laws.
-/
namespace InsacermoCriticalPair

universe u v

def Guaranteed {World : Type u} {Output : Type v}
    (lower upper : World → Nat)
    (possible : World → Output → Prop) (r : Nat) : Prop :=
  ∃ control : Output → Nat,
    ∀ w y, possible w y →
      lower w ≤ control y + r ∧ control y ≤ upper w + r

/-- Direct branchwise policy selection is equivalent to local synthesis,
without enumerating policies explicitly. -/
theorem guaranteed_iff_each_branch
    {World : Type u} {Output : Type v}
    (lower upper : World → Nat)
    (possible : World → Output → Prop) (r : Nat) :
    Guaranteed lower upper possible r ↔
      ∀ y : Output, ∃ control : Nat,
        ∀ w, possible w y →
          lower w ≤ control + r ∧ control ≤ upper w + r := by
  classical
  constructor
  · rintro ⟨control, h⟩ y
    exact ⟨control y, fun w hw => h w y hw⟩
  · intro h
    let control : Output → Nat := fun y => Classical.choose (h y)
    refine ⟨control, ?_⟩
    intro w y hw
    exact Classical.choose_spec (h y) w hw

/-- A shared possible observation keeps a lower-bound dual pair active. -/
theorem common_observation_certificate
    {World : Type u} {Output : Type v}
    (lower upper : World → Nat)
    (possible : World → Output → Prop)
    (r : Nat) (a b : World) (y : Output)
    (h : Guaranteed lower upper possible r)
    (ha : possible a y)
    (hb : possible b y) :
    lower a ≤ upper b + 2*r := by
  obtain ⟨control, hw⟩ := h
  have h1 := (hw a y ha).1
  have h2 := (hw b y hb).2
  omega

/-- If the critical pair still shares a possible reading, no policy can
guarantee a smaller repair, independently of its choices on other readings. -/
theorem irreducible_critical_pair
    {World : Type u} {Output : Type v}
    (lower upper : World → Nat)
    (possible : World → Output → Prop)
    (r : Nat) (a b : World) (y : Output)
    (ha : possible a y) (hb : possible b y)
    (hgap : upper b + 2*r < lower a) :
    ¬ Guaranteed lower upper possible r := by
  intro h
  have hc := common_observation_certificate lower upper possible r a b y h ha hb
  omega

/-- A more informative observation cannot invalidate an existing guaranteed
decision, if it only removes possible world/output pairs. -/
theorem safe_information_refinement
    {World : Type u} {Output : Type v}
    (lower upper : World → Nat)
    (oldPossible newPossible : World → Output → Prop)
    (r : Nat)
    (hrefine : ∀ w y, newPossible w y → oldPossible w y)
    (h : Guaranteed lower upper oldPossible r) :
    Guaranteed lower upper newPossible r := by
  obtain ⟨control, hw⟩ := h
  exact ⟨control, fun w y hnew => hw w y (hrefine w y hnew)⟩

inductive World
  | A | B
deriving DecidableEq

inductive Outcome
  | left | right | shared
deriving DecidableEq

def lower : World → Nat
  | .A => 0
  | .B => 4

def upper : World → Nat
  | .A => 2
  | .B => 6

def reliable : World → Outcome → Prop
  | .A, .left => True
  | .B, .right => True
  | _, _ => False

def noisy : World → Outcome → Prop
  | .A, .left => True
  | .B, .right => True
  | _, .shared => True
  | _, _ => False

/-- Reliability permits an un-repaired, branch-dependent transformation. -/
theorem reliable_zero_repair :
    Guaranteed lower upper reliable 0 := by
  refine ⟨fun y => match y with
    | .left => 1
    | .right => 5
    | .shared => 0, ?_⟩
  intro w y hp
  cases w <;> cases y <;> simp [lower, upper, reliable] at * <;> omega

/-- The noisy instrument may report shared for both laws, so zero repair is
mathematically impossible regardless of what its controller does. -/
theorem noisy_zero_repair_impossible :
    ¬ Guaranteed lower upper noisy 0 := by
  apply irreducible_critical_pair lower upper noisy 0 World.B World.A Outcome.shared
  · exact True.intro
  · exact True.intro
  · decide

/-- A single unit of capacity repair can cover both unknown laws with
one control, even if the observation is uninformative. -/
theorem noisy_one_repair_sufficient :
    Guaranteed lower upper noisy 1 := by
  refine ⟨fun _ => 3, ?_⟩
  intro w y hp
  cases w <;> simp [lower, upper] <;> omega

end InsacermoCriticalPair
