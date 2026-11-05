import Lean

/-!
INSACERMO external laboratory. The finite-world MAX TOTAL and C3 code is
untouched. A state is either dead, or a stack of pending opening brackets.
-/
namespace InsacermoLab

inductive Sym where
  | openA | openB | closeA | closeB
  deriving DecidableEq, Repr, Inhabited

def step : Option (List Bool) → Sym → Option (List Bool)
  | none, _ => none
  | some s, .openA => some (false :: s)
  | some s, .openB => some (true :: s)
  | some (false :: s), .closeA => some s
  | some _, .closeA => none
  | some (true :: s), .closeB => some s
  | some _, .closeB => none

def process (q : Option (List Bool)) (w : List Sym) : Option (List Bool) :=
  w.foldl step q

def residual (w : List Sym) : Option (List Bool) := process (some []) w
def accepts (w : List Sym) : Prop := residual w = some []
def futureEq (u v : List Sym) : Prop :=
  ∀ z : List Sym, accepts (u ++ z) ↔ accepts (v ++ z)

@[simp] theorem process_nil (q : Option (List Bool)) : process q [] = q := rfl
@[simp] theorem process_cons (q : Option (List Bool)) (a : Sym) (w : List Sym) :
    process q (a :: w) = process (step q a) w := rfl

theorem process_append (q : Option (List Bool)) (u v : List Sym) :
    process q (u ++ v) = process (process q u) v := by
  simp [process, List.foldl_append]

@[simp] theorem process_none (w : List Sym) : process none w = none := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [process_cons, step] using ih

def opener (b : Bool) : Sym := if b then .openB else .openA
def closer (b : Bool) : Sym := if b then .closeB else .closeA
def closeHistory (s : List Bool) : List Sym := s.map closer

def openHistory : List Bool → List Sym
  | [] => []
  | b :: bs => openHistory bs ++ [opener b]

theorem process_openHistory (s base : List Bool) :
    process (some base) (openHistory s) = some (s ++ base) := by
  induction s generalizing base with
  | nil => simp [openHistory]
  | cons b bs ih =>
    simp only [openHistory, process_append]
    rw [ih]
    cases b <;> simp [opener, process_cons, process_nil, step]

@[simp] theorem residual_openHistory (s : List Bool) :
    residual (openHistory s) = some s := by
  simpa [residual] using process_openHistory s []

theorem close_exact (s t : List Bool) :
    process (some t) (closeHistory s) = some [] ↔ t = s := by
  induction s generalizing t with
  | nil =>
    cases t <;> simp [closeHistory]
  | cons b bs ih =>
    cases t with
    | nil =>
      cases b <;> simp [closeHistory, closer, process_cons, step]
    | cons c cs =>
      cases b <;> cases c <;>
        simp [closeHistory, closer, process_cons, step, process_none] <;>
        exact ih cs

theorem states_separated (a b : Option (List Bool))
    (h : ∀ z : List Sym, process a z = some [] ↔ process b z = some []) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some t =>
      have yes : process (some t) (closeHistory t) = some [] :=
        (close_exact t t).2 rfl
      have no := (h (closeHistory t)).2 yes
      simp at no
  | some s =>
    cases b with
    | none =>
      have yes : process (some s) (closeHistory s) = some [] :=
        (close_exact s s).2 rfl
      have no := (h (closeHistory s)).1 yes
      simp at no
    | some t =>
      have yes : process (some s) (closeHistory s) = some [] :=
        (close_exact s s).2 rfl
      have t_eq_s := (close_exact s t).1 ((h (closeHistory s)).1 yes)
      simp [t_eq_s]

theorem residual_append (u z : List Sym) :
    residual (u ++ z) = process (residual u) z := by
  exact process_append (some []) u z

theorem future_eq_iff_residual_eq (u v : List Sym) :
    futureEq u v ↔ residual u = residual v := by
  constructor
  · intro h
    apply states_separated
    intro z
    simpa [futureEq, accepts, residual_append] using h z
  · intro h z
    simpa [accepts, residual_append, h]

theorem all_pending_stacks_distinguishable (s t : List Bool) (hne : s ≠ t) :
    ¬ futureEq (openHistory s) (openHistory t) := by
  intro heq
  have h := (future_eq_iff_residual_eq (openHistory s) (openHistory t)).1 heq
  apply hne
  simpa using h

@[simp] theorem residual_single_closeA : residual [.closeA] = none := rfl
@[simp] theorem residual_single_closeB : residual [.closeB] = none := rfl

theorem dead_histories_same_future : futureEq [.closeA] [.closeB] := by
  exact (future_eq_iff_residual_eq _ _).2 rfl

theorem dead_histories_not_contextually_equivalent :
    accepts [.openA, .closeA] ∧ ¬ accepts [.openA, .closeB] := by
  simp [accepts, residual, process, step]

@[simp] theorem process_matchedA (q : Option (List Bool)) :
    process q [.openA, .closeA] = q := by
  cases q <;> simp [process, step]

@[simp] theorem process_matchedB (q : Option (List Bool)) :
    process q [.openB, .closeB] = q := by
  cases q <;> simp [process, step]

inductive Rewrite : List Sym → List Sym → Prop where
  | A (u v : List Sym) : Rewrite (u ++ [.openA, .closeA] ++ v) (u ++ v)
  | B (u v : List Sym) : Rewrite (u ++ [.openB, .closeB] ++ v) (u ++ v)

theorem rewrite_preserves_process {u v : List Sym} (h : Rewrite u v)
    (q : Option (List Bool)) : process q u = process q v := by
  cases h with
  | A x y =>
    simp only [process_append]
    change process (process (process q x) [.openA, .closeA]) y = process (process q x) y
    rw [process_matchedA]
  | B x y =>
    simp only [process_append]
    change process (process (process q x) [.openB, .closeB]) y = process (process q x) y
    rw [process_matchedB]

theorem rewrite_preserves_acceptance {u v : List Sym} (h : Rewrite u v) :
    accepts u ↔ accepts v := by
  unfold accepts residual
  rw [rewrite_preserves_process h (some [])]

end InsacermoLab
