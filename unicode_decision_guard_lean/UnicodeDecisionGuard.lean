/-
INSACERMO - Unicode Decision Guard, isolated Lean laboratory.
This is NOT the frozen MAX TOTAL / C3 kernel.
The Unicode/Python/SQLite behavior is independently tested, not proved here.
-/
import Init

namespace InsacermoUnicodeDecisionGuard

universe u v
variable {W : Type u} {O : Type v}

def AlwaysSafe (observe : W → O) (truth : W → Bool)
    (act : O → Option Bool) : Prop :=
  ∀ w : W, ∀ b : Bool, act (observe w) = some b → b = truth w

theorem identical_view_same_prediction (observe : W → O)
    (classifier : O → Bool) (x y : W)
    (h : observe x = observe y) :
    classifier (observe x) = classifier (observe y) := by
  rw [h]

theorem collision_forces_refusal (observe : W → O) (truth : W → Bool)
    (act : O → Option Bool) (hSafe : AlwaysSafe observe truth act)
    (x y : W) (hObs : observe x = observe y)
    (hDifferent : truth x ≠ truth y) :
    act (observe x) = none := by
  cases h : act (observe x) with
  | none => rfl
  | some b =>
      have hx : b = truth x := hSafe x b h
      have hy : b = truth y := hSafe y b (by rw [← hObs]; exact h)
      exact False.elim (hDifferent (hx.symm.trans hy))

inductive Family where
  | eq | lt | gt | le | ge
  deriving DecidableEq, Repr

structure Expression where
  family : Family
  negated : Bool
  lhs : Int
  rhs : Int
  deriving DecidableEq, Repr

def baseTruth (f : Family) (a b : Int) : Bool :=
  match f with
  | .eq => decide (a = b)
  | .lt => decide (a < b)
  | .gt => decide (a > b)
  | .le => decide (a ≤ b)
  | .ge => decide (a ≥ b)

def truth (s : Expression) : Bool :=
  if s.negated then !(baseTruth s.family s.lhs s.rhs)
  else baseTruth s.family s.lhs s.rhs

/-- Semantic abstraction of NFD followed by removal of combining marks,
only for the five specified relation/negation pairs. -/
def eraseNegation (s : Expression) : Expression :=
  {s with negated := false}

def src (f : Family) (neg : Bool) (a b : Int) : Expression :=
  ⟨f, neg, a, b⟩

theorem five_families_collide (f : Family) (a b : Int) :
    eraseNegation (src f true a b) =
    eraseNegation (src f false a b) := rfl

theorem five_families_opposite_truth (f : Family) (a b : Int) :
    truth (src f true a b) ≠ truth (src f false a b) := by
  cases h : baseTruth f a b <;> simp [truth, src, h]

theorem five_families_must_refuse
    (act : Expression → Option Bool)
    (hSafe : AlwaysSafe eraseNegation truth act)
    (f : Family) (a b : Int) :
    act (eraseNegation (src f true a b)) = none := by
  exact collision_forces_refusal eraseNegation truth act hSafe
    (src f true a b) (src f false a b)
    (five_families_collide f a b)
    (five_families_opposite_truth f a b)

/-- Ten distinct operator identifiers, exported as ASCII hexadecimal tokens. -/
def encodeOp (f : Family) (neg : Bool) : Nat :=
  match f, neg with
  | .eq, false => 0x003D
  | .eq, true  => 0x2260
  | .lt, false => 0x003C
  | .lt, true  => 0x226E
  | .gt, false => 0x003E
  | .gt, true  => 0x226F
  | .le, false => 0x2264
  | .le, true  => 0x2270
  | .ge, false => 0x2265
  | .ge, true  => 0x2271

def decodeOp : Nat → Option (Family × Bool)
  | 0x003D => some (.eq, false)
  | 0x2260 => some (.eq, true)
  | 0x003C => some (.lt, false)
  | 0x226E => some (.lt, true)
  | 0x003E => some (.gt, false)
  | 0x226F => some (.gt, true)
  | 0x2264 => some (.le, false)
  | 0x2270 => some (.le, true)
  | 0x2265 => some (.ge, false)
  | 0x2271 => some (.ge, true)
  | _ => none

theorem code_roundtrip (f : Family) (neg : Bool) :
    decodeOp (encodeOp f neg) = some (f, neg) := by
  cases f <;> cases neg <;> rfl

theorem code_injective (f g : Family) (n m : Bool)
    (h : encodeOp f n = encodeOp g m) :
    (f, n) = (g, m) := by
  have hDec := congrArg decodeOp h
  simpa [code_roundtrip] using hDec

/-- Identity here states an explicit contract for the selected ASCII tokens.
The runtime checks that the actual Unicode cleanup preserves these tokens. -/
def cleanProtectedCode (n : Nat) : Nat := n

theorem clean_protected_roundtrip (f : Family) (neg : Bool) :
    decodeOp (cleanProtectedCode (encodeOp f neg)) = some (f, neg) := by
  exact code_roundtrip f neg

/-- Provenance is a separate assumption, not inferred from token appearance. -/
def trustedDecision (trusted : Bool) (opCode : Nat)
    (a b : Int) : Option Bool :=
  if trusted then
    (decodeOp opCode).map (fun p => truth (src p.1 p.2 a b))
  else none

theorem forged_code_refused (code : Nat) (a b : Int) :
    trustedDecision false code a b = none := rfl

theorem trusted_code_correct (f : Family) (neg : Bool) (a b : Int) :
    trustedDecision true (encodeOp f neg) a b =
      some (truth (src f neg a b)) := by
  cases f <;> cases neg <;> rfl

#print axioms collision_forces_refusal
#print axioms five_families_opposite_truth
#print axioms five_families_must_refuse
#print axioms code_roundtrip
#print axioms code_injective
#print axioms clean_protected_roundtrip
#print axioms forged_code_refused
#print axioms trusted_code_correct

end InsacermoUnicodeDecisionGuard
