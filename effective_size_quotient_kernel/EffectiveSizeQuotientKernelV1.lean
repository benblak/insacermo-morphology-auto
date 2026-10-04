import Std

/-!
INSACERMO — Effective Size / Exact Quotient Kernel V1

Motivation:
raw world count is not, by itself, the semantic size of a finite deterministic
adaptive decision problem.

If a quotient map preserves:
1. every feasible-action fact, and
2. every outcome of every available probe,

then the quotient preserves:
- common-action / ACT semantics,
- occurrence of observation branches,
- refinement by probes,
- solvability at every exact planning depth,
- bounded worst-case probe cost at every depth.

Hence duplicate or otherwise semantically indistinguishable worlds can be merged
without changing exact adaptive planning semantics in this model.

Important boundary:
multiplicity-sensitive aggregate statistics (for example an unnormalised total
empirical path cost over all rows) are not claimed invariant unless multiplicity
weights are preserved separately.
-/

namespace InsacermoEffectiveSize

abbrev Belief (W : Type) := W → Prop

/-- A belief admits one action feasible in every world still possible. -/
def CommonAction {W A : Type}
    (feasible : W → A → Prop)
    (B : Belief W) : Prop :=
  ∃ a : A, ∀ w : W, B w → feasible w a

/-- Restrict a belief to one observation branch of one probe. -/
def Refine {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (p : P)
    (o : O) : Belief W :=
  fun w => B w ∧ observe p w = o

/-- An observation branch actually occurs in the current belief. -/
def Occurs {W P O : Type}
    (observe : P → W → O)
    (B : Belief W)
    (p : P)
    (o : O) : Prop :=
  ∃ w : W, B w ∧ observe p w = o

/-- Image of a belief through an abstraction/quotient map. -/
def LiftBelief {W Q : Type}
    (q : W → Q)
    (B : Belief W) : Belief Q :=
  fun z => ∃ w : W, B w ∧ q w = z

/--
An exact semantic quotient preserves all action-feasibility facts and all probe
outcomes. No cardinality or finiteness assumption is required for the theorem.
-/
structure ExactQuotient {W Q A P O : Type}
    (q : W → Q)
    (feasibleW : W → A → Prop)
    (feasibleQ : Q → A → Prop)
    (observeW : P → W → O)
    (observeQ : P → Q → O) : Prop where
  feasible_iff : ∀ w : W, ∀ a : A,
    feasibleW w a ↔ feasibleQ (q w) a
  observe_eq : ∀ p : P, ∀ w : W,
    observeW p w = observeQ p (q w)

/--
Exact adaptive solvability with at most d probes.

At depth 0, the current belief must already share a common action.
At successor depth, either ACT is already possible, or one probe is chosen and
every observation branch that can actually occur must be solvable recursively.
-/
def CanSolveAtDepth {W A P O : Type}
    (feasible : W → A → Prop)
    (observe : P → W → O) : Nat → Belief W → Prop
  | 0, B => CommonAction feasible B
  | Nat.succ d, B =>
      CommonAction feasible B ∨
      ∃ p : P, ∀ o : O, Occurs observe B p o →
        CanSolveAtDepth feasible observe d (Refine observe B p o)

/--
Adaptive solvability with both a depth bound and a worst-case accumulated probe
budget. Probe costs are nonnegative natural numbers and are shared by original
and quotient problems.
-/
def CanSolveWithin {W A P O : Type}
    (feasible : W → A → Prop)
    (observe : P → W → O)
    (cost : P → Nat) : Nat → Nat → Belief W → Prop
  | 0, _, B => CommonAction feasible B
  | Nat.succ d, budget, B =>
      CommonAction feasible B ∨
      ∃ p : P, cost p ≤ budget ∧
        ∀ o : O, Occurs observe B p o →
          CanSolveWithin feasible observe cost d (budget - cost p)
            (Refine observe B p o)

/-- Exact first depth at which the belief is solvable. -/
def ExactDepth {W A P O : Type}
    (feasible : W → A → Prop)
    (observe : P → W → O)
    (d : Nat)
    (B : Belief W) : Prop :=
  CanSolveAtDepth feasible observe d B ∧
  ∀ k : Nat, k < d → ¬ CanSolveAtDepth feasible observe k B

/-- Exact least worst-case budget, at a fixed depth bound. -/
def ExactBudget {W A P O : Type}
    (feasible : W → A → Prop)
    (observe : P → W → O)
    (cost : P → Nat)
    (depth budget : Nat)
    (B : Belief W) : Prop :=
  CanSolveWithin feasible observe cost depth budget B ∧
  ∀ b : Nat, b < budget →
    ¬ CanSolveWithin feasible observe cost depth b B

theorem commonAction_iff_lift
    {W Q A P O : Type}
    {q : W → Q}
    {feasibleW : W → A → Prop}
    {feasibleQ : Q → A → Prop}
    {observeW : P → W → O}
    {observeQ : P → Q → O}
    (hq : ExactQuotient q feasibleW feasibleQ observeW observeQ)
    (B : Belief W) :
    CommonAction feasibleW B ↔
      CommonAction feasibleQ (LiftBelief q B) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro z hz
    rcases hz with ⟨w, hB, rfl⟩
    exact (hq.feasible_iff w a).mp (ha w hB)
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro w hB
    have hz : LiftBelief q B (q w) := ⟨w, hB, rfl⟩
    exact (hq.feasible_iff w a).mpr (ha (q w) hz)

theorem occurs_iff_lift
    {W Q A P O : Type}
    {q : W → Q}
    {feasibleW : W → A → Prop}
    {feasibleQ : Q → A → Prop}
    {observeW : P → W → O}
    {observeQ : P → Q → O}
    (hq : ExactQuotient q feasibleW feasibleQ observeW observeQ)
    (B : Belief W)
    (p : P)
    (o : O) :
    Occurs observeW B p o ↔
      Occurs observeQ (LiftBelief q B) p o := by
  constructor
  · rintro ⟨w, hB, hO⟩
    refine ⟨q w, ⟨w, hB, rfl⟩, ?_⟩
    calc
      observeQ p (q w) = observeW p w := (hq.observe_eq p w).symm
      _ = o := hO
  · rintro ⟨z, ⟨w, hB, hqz⟩, hO⟩
    refine ⟨w, hB, ?_⟩
    calc
      observeW p w = observeQ p (q w) := hq.observe_eq p w
      _ = observeQ p z := by rw [hqz]
      _ = o := hO

theorem lift_refine_eq
    {W Q A P O : Type}
    {q : W → Q}
    {feasibleW : W → A → Prop}
    {feasibleQ : Q → A → Prop}
    {observeW : P → W → O}
    {observeQ : P → Q → O}
    (hq : ExactQuotient q feasibleW feasibleQ observeW observeQ)
    (B : Belief W)
    (p : P)
    (o : O) :
    LiftBelief q (Refine observeW B p o) =
      Refine observeQ (LiftBelief q B) p o := by
  funext z
  apply propext
  constructor
  · rintro ⟨w, ⟨hB, hO⟩, hqz⟩
    constructor
    · exact ⟨w, hB, hqz⟩
    · calc
        observeQ p z = observeQ p (q w) := by rw [hqz]
        _ = observeW p w := (hq.observe_eq p w).symm
        _ = o := hO
  · rintro ⟨hz, hO⟩
    rcases hz with ⟨w, hB, hqz⟩
    refine ⟨w, ?_, hqz⟩
    constructor
    · exact hB
    · calc
        observeW p w = observeQ p (q w) := hq.observe_eq p w
        _ = observeQ p z := by rw [hqz]
        _ = o := hO

/--
Main exact-depth quotient theorem.

For every depth bound d, exact adaptive solvability is invariant under any
quotient preserving all feasible-action facts and every available probe outcome.
-/
theorem canSolveAtDepth_iff_lift
    {W Q A P O : Type}
    {q : W → Q}
    {feasibleW : W → A → Prop}
    {feasibleQ : Q → A → Prop}
    {observeW : P → W → O}
    {observeQ : P → Q → O}
    (hq : ExactQuotient q feasibleW feasibleQ observeW observeQ) :
    ∀ d : Nat, ∀ B : Belief W,
      CanSolveAtDepth feasibleW observeW d B ↔
        CanSolveAtDepth feasibleQ observeQ d (LiftBelief q B) := by
  intro d
  induction d with
  | zero =>
      intro B
      simpa [CanSolveAtDepth] using (commonAction_iff_lift hq B)
  | succ d ih =>
      intro B
      simp only [CanSolveAtDepth]
      constructor
      · intro h
        rcases h with hcommon | hprobe
        · exact Or.inl ((commonAction_iff_lift hq B).mp hcommon)
        · rcases hprobe with ⟨p, hp⟩
          right
          refine ⟨p, ?_⟩
          intro o hoccQ
          have hoccW : Occurs observeW B p o :=
            (occurs_iff_lift hq B p o).mpr hoccQ
          have hsubW := hp o hoccW
          have hsubQ :=
            (ih (Refine observeW B p o)).mp hsubW
          rw [lift_refine_eq hq B p o] at hsubQ
          exact hsubQ
      · intro h
        rcases h with hcommon | hprobe
        · exact Or.inl ((commonAction_iff_lift hq B).mpr hcommon)
        · rcases hprobe with ⟨p, hp⟩
          right
          refine ⟨p, ?_⟩
          intro o hoccW
          have hoccQ : Occurs observeQ (LiftBelief q B) p o :=
            (occurs_iff_lift hq B p o).mp hoccW
          have hsubQ := hp o hoccQ
          have hsubLift :
              CanSolveAtDepth feasibleQ observeQ d
                (LiftBelief q (Refine observeW B p o)) := by
            rw [lift_refine_eq hq B p o]
            exact hsubQ
          exact (ih (Refine observeW B p o)).mpr hsubLift

/--
Worst-case probe-budget invariance.

The quotient has exactly the same solvability threshold for every shared probe
cost function, at every depth and budget.
-/
theorem canSolveWithin_iff_lift
    {W Q A P O : Type}
    {q : W → Q}
    {feasibleW : W → A → Prop}
    {feasibleQ : Q → A → Prop}
    {observeW : P → W → O}
    {observeQ : P → Q → O}
    (hq : ExactQuotient q feasibleW feasibleQ observeW observeQ)
    (cost : P → Nat) :
    ∀ d budget : Nat, ∀ B : Belief W,
      CanSolveWithin feasibleW observeW cost d budget B ↔
        CanSolveWithin feasibleQ observeQ cost d budget (LiftBelief q B) := by
  intro d
  induction d with
  | zero =>
      intro budget B
      simpa [CanSolveWithin] using (commonAction_iff_lift hq B)
  | succ d ih =>
      intro budget B
      simp only [CanSolveWithin]
      constructor
      · intro h
        rcases h with hcommon | hprobe
        · exact Or.inl ((commonAction_iff_lift hq B).mp hcommon)
        · rcases hprobe with ⟨p, hcost, hp⟩
          right
          refine ⟨p, hcost, ?_⟩
          intro o hoccQ
          have hoccW : Occurs observeW B p o :=
            (occurs_iff_lift hq B p o).mpr hoccQ
          have hsubW := hp o hoccW
          have hsubQ :=
            (ih (budget - cost p) (Refine observeW B p o)).mp hsubW
          rw [lift_refine_eq hq B p o] at hsubQ
          exact hsubQ
      · intro h
        rcases h with hcommon | hprobe
        · exact Or.inl ((commonAction_iff_lift hq B).mpr hcommon)
        · rcases hprobe with ⟨p, hcost, hp⟩
          right
          refine ⟨p, hcost, ?_⟩
          intro o hoccW
          have hoccQ : Occurs observeQ (LiftBelief q B) p o :=
            (occurs_iff_lift hq B p o).mp hoccW
          have hsubQ := hp o hoccQ
          have hsubLift :
              CanSolveWithin feasibleQ observeQ cost d (budget - cost p)
                (LiftBelief q (Refine observeW B p o)) := by
            rw [lift_refine_eq hq B p o]
            exact hsubQ
          exact
            (ih (budget - cost p) (Refine observeW B p o)).mpr hsubLift

theorem exactDepth_iff_lift
    {W Q A P O : Type}
    {q : W → Q}
    {feasibleW : W → A → Prop}
    {feasibleQ : Q → A → Prop}
    {observeW : P → W → O}
    {observeQ : P → Q → O}
    (hq : ExactQuotient q feasibleW feasibleQ observeW observeQ)
    (d : Nat)
    (B : Belief W) :
    ExactDepth feasibleW observeW d B ↔
      ExactDepth feasibleQ observeQ d (LiftBelief q B) := by
  constructor
  · rintro ⟨hd, hmin⟩
    constructor
    · exact (canSolveAtDepth_iff_lift hq d B).mp hd
    · intro k hk hkQ
      exact hmin k hk ((canSolveAtDepth_iff_lift hq k B).mpr hkQ)
  · rintro ⟨hd, hmin⟩
    constructor
    · exact (canSolveAtDepth_iff_lift hq d B).mpr hd
    · intro k hk hkW
      exact hmin k hk ((canSolveAtDepth_iff_lift hq k B).mp hkW)

theorem exactBudget_iff_lift
    {W Q A P O : Type}
    {q : W → Q}
    {feasibleW : W → A → Prop}
    {feasibleQ : Q → A → Prop}
    {observeW : P → W → O}
    {observeQ : P → Q → O}
    (hq : ExactQuotient q feasibleW feasibleQ observeW observeQ)
    (cost : P → Nat)
    (depth budget : Nat)
    (B : Belief W) :
    ExactBudget feasibleW observeW cost depth budget B ↔
      ExactBudget feasibleQ observeQ cost depth budget (LiftBelief q B) := by
  constructor
  · rintro ⟨hb, hmin⟩
    constructor
    · exact (canSolveWithin_iff_lift hq cost depth budget B).mp hb
    · intro b hbLt hbQ
      exact hmin b hbLt ((canSolveWithin_iff_lift hq cost depth b B).mpr hbQ)
  · rintro ⟨hb, hmin⟩
    constructor
    · exact (canSolveWithin_iff_lift hq cost depth budget B).mpr hb
    · intro b hbLt hbW
      exact hmin b hbLt ((canSolveWithin_iff_lift hq cost depth b B).mp hbW)

/--
Concrete duplication corollary: multiplying every world by an arbitrary nonempty
index type changes raw cardinality but not exact adaptive planning depth.
-/
theorem duplicate_worlds_preserve_exact_depth
    {W I A P O : Type} [Nonempty I]
    (feasible : W → A → Prop)
    (observe : P → W → O)
    (d : Nat)
    (B : Belief W) :
    ExactDepth
        (fun wi : W × I => feasible wi.1)
        (fun p wi : W × I => observe p wi.1)
        d
        (fun wi : W × I => B wi.1)
      ↔
    ExactDepth feasible observe d B := by
  let q : W × I → W := fun wi => wi.1
  let hq : ExactQuotient q
      (fun wi : W × I => feasible wi.1)
      feasible
      (fun p wi : W × I => observe p wi.1)
      observe := by
    refine ⟨?_, ?_⟩
    · intro wi a
      rfl
    · intro p wi
      rfl
  have h :=
    exactDepth_iff_lift hq d (fun wi : W × I => B wi.1)
  have hlift :
      LiftBelief q (fun wi : W × I => B wi.1) = B := by
    funext w
    apply propext
    constructor
    · rintro ⟨wi, hB, hqw⟩
      simpa [q] using hB
    · intro hB
      let i0 : I := Classical.choice (inferInstance : Nonempty I)
      exact ⟨(w, i0), hB, rfl⟩
  rw [hlift] at h
  exact h

#print axioms commonAction_iff_lift
#print axioms occurs_iff_lift
#print axioms lift_refine_eq
#print axioms canSolveAtDepth_iff_lift
#print axioms canSolveWithin_iff_lift
#print axioms exactDepth_iff_lift
#print axioms exactBudget_iff_lift
#print axioms duplicate_worlds_preserve_exact_depth

end InsacermoEffectiveSize
