import InsacermoV13Kernel.InformationCapabilityFrontier

namespace InsacermoV13Kernel

universe u v w

/-- An n-region contractual action cover: n currently available actions suffice
    so that every possible world is covered by at least one admissible action. -/
def ActionCover {World : Type u} {Action : Type v}
    (available : Action → Prop) (admissible : World → Action → Prop)
    (n : Nat) : Prop :=
  ∃ actions : Fin n → Action,
    (∀ i, available (actions i)) ∧
    ∀ x, ∃ i, admissible x (actions i)

/-- Any safe n-symbol encoding induces an n-action cover.
    Nonemptiness supplies a harmless action for unused symbols. -/
theorem actionCover_of_safeEncoding
    {World : Type u} {Action : Type v} [Nonempty World]
    {available : Action → Prop} {admissible : World → Action → Prop}
    {n : Nat}
    (henc : SafeEncoding available admissible n) :
    ActionCover available admissible n := by
  classical
  rcases henc with ⟨obs, hsafe⟩
  let x0 : World := Classical.choice (inferInstance : Nonempty World)
  rcases hsafe x0 with ⟨a0, ha0, h0⟩
  have hper :
      ∀ i : Fin n, ∃ a, available a ∧
        ∀ ⦃x : World⦄, obs x = i → admissible x a := by
    intro i
    by_cases hi : ∃ x : World, obs x = i
    · rcases hi with ⟨x, hxi⟩
      rcases hsafe x with ⟨a, ha, hall⟩
      refine ⟨a, ha, ?_⟩
      intro y hyi
      exact hall (hyi.trans hxi.symm)
    · refine ⟨a0, ha0, ?_⟩
      intro y hyi
      exact False.elim (hi ⟨y, hyi⟩)
  let actions : Fin n → Action := fun i => Classical.choose (hper i)
  refine ⟨actions, ?_, ?_⟩
  · intro i
    exact (Classical.choose_spec (hper i)).1
  · intro x
    refine ⟨obs x, ?_⟩
    exact (Classical.choose_spec (hper (obs x))).2 rfl

/-- Any n-action cover induces a safe n-symbol encoding by assigning each world
    to one covering action region. -/
theorem safeEncoding_of_actionCover
    {World : Type u} {Action : Type v}
    {available : Action → Prop} {admissible : World → Action → Prop}
    {n : Nat}
    (hcover : ActionCover available admissible n) :
    SafeEncoding available admissible n := by
  classical
  rcases hcover with ⟨actions, havail, hcover⟩
  let obs : World → Fin n := fun x => Classical.choose (hcover x)
  have hchosen : ∀ x : World, admissible x (actions (obs x)) := by
    intro x
    dsimp [obs]
    exact Classical.choose_spec (hcover x)
  refine ⟨obs, ?_⟩
  intro x
  refine ⟨actions (obs x), havail (obs x), ?_⟩
  intro y hy
  simpa [hy] using hchosen y

/-- Exact finite bridge: for nonempty world spaces, n safe information symbols
    are equivalent to n contractual action regions covering all worlds. -/
theorem safeEncoding_iff_actionCover
    {World : Type u} {Action : Type v} [Nonempty World]
    {available : Action → Prop} {admissible : World → Action → Prop}
    {n : Nat} :
    SafeEncoding available admissible n ↔
      ActionCover available admissible n := by
  constructor
  · exact actionCover_of_safeEncoding
  · exact safeEncoding_of_actionCover

/-- m is a minimum contractual action-cover size. -/
def IsMinActionCover {World : Type u} {Action : Type v}
    (available : Action → Prop) (admissible : World → Action → Prop)
    (m : Nat) : Prop :=
  ActionCover available admissible m ∧
    ∀ n, ActionCover available admissible n → m ≤ n

/-- The minimum safe symbol count and minimum action-cover count coincide. -/
theorem isMinSafeSymbols_iff_isMinActionCover
    {World : Type u} {Action : Type v} [Nonempty World]
    {available : Action → Prop} {admissible : World → Action → Prop}
    {m : Nat} :
    IsMinSafeSymbols available admissible m ↔
      IsMinActionCover available admissible m := by
  constructor
  · intro h
    refine ⟨actionCover_of_safeEncoding h.1, ?_⟩
    intro n hn
    exact h.2 n (safeEncoding_of_actionCover hn)
  · intro h
    refine ⟨safeEncoding_of_actionCover h.1, ?_⟩
    intro n hn
    exact h.2 n (actionCover_of_safeEncoding hn)

/-- An n-color obstruction coloring: every realized color fiber avoids being
    contractually obstructed. -/
def ObstructionColoring {World : Type u} {Action : Type v}
    (available : Action → Prop) (admissible : World → Action → Prop)
    (n : Nat) : Prop :=
  ∃ color : World → Fin n,
    ∀ x, ¬ Obstructed (fun y => color y = color x) available admissible

/-- Global safety is exactly avoidance of obstructed observation fibers. -/
theorem globalSafe_iff_avoidsObstructedFibers
    {World : Type u} {Obs : Type v} {Action : Type w}
    {obs : World → Obs} {available : Action → Prop}
    {admissible : World → Action → Prop} :
    GlobalSafe obs available admissible ↔
      ∀ x, ¬ Obstructed (fun y => obs y = obs x) available admissible := by
  classical
  constructor
  · intro h x hob
    apply hob
    exact (fiberSafe_iff_commonAction_fiber).mp (h x)
  · intro h x
    apply (fiberSafe_iff_commonAction_fiber).mpr
    exact Classical.byContradiction (fun hcommon => h x hcommon)

/-- Exact obstruction bridge: safe n-symbol encodings are exactly n-colorings
    whose realized color classes contain no contractual obstruction. -/
theorem safeEncoding_iff_obstructionColoring
    {World : Type u} {Action : Type v}
    {available : Action → Prop} {admissible : World → Action → Prop}
    {n : Nat} :
    SafeEncoding available admissible n ↔
      ObstructionColoring available admissible n := by
  constructor
  · rintro ⟨obs, hsafe⟩
    exact ⟨obs, (globalSafe_iff_avoidsObstructedFibers.mp hsafe)⟩
  · rintro ⟨color, hcolor⟩
    exact ⟨color, (globalSafe_iff_avoidsObstructedFibers.mpr hcolor)⟩

/-- m is a minimum obstruction-color count. -/
def IsMinObstructionColors {World : Type u} {Action : Type v}
    (available : Action → Prop) (admissible : World → Action → Prop)
    (m : Nat) : Prop :=
  ObstructionColoring available admissible m ∧
    ∀ n, ObstructionColoring available admissible n → m ≤ n

/-- Minimum safe information equals minimum obstruction colors. -/
theorem isMinSafeSymbols_iff_isMinObstructionColors
    {World : Type u} {Action : Type v}
    {available : Action → Prop} {admissible : World → Action → Prop}
    {m : Nat} :
    IsMinSafeSymbols available admissible m ↔
      IsMinObstructionColors available admissible m := by
  constructor
  · intro h
    refine ⟨safeEncoding_iff_obstructionColoring.mp h.1, ?_⟩
    intro n hn
    exact h.2 n (safeEncoding_iff_obstructionColoring.mpr hn)
  · intro h
    refine ⟨safeEncoding_iff_obstructionColoring.mpr h.1, ?_⟩
    intro n hn
    exact h.2 n (safeEncoding_iff_obstructionColoring.mp hn)

/-- Exact combinatorial identity at the minimum level:
    action-cover number equals obstruction-color number. -/
theorem isMinActionCover_iff_isMinObstructionColors
    {World : Type u} {Action : Type v} [Nonempty World]
    {available : Action → Prop} {admissible : World → Action → Prop}
    {m : Nat} :
    IsMinActionCover available admissible m ↔
      IsMinObstructionColors available admissible m := by
  rw [← isMinSafeSymbols_iff_isMinActionCover,
      isMinSafeSymbols_iff_isMinObstructionColors]

end InsacermoV13Kernel
