/-!
INSACERMO core lab, 2026-11-17.
Generic mathematical reversibility of bijective coordinate renaming and output flips;
finite 32-point orbit witness and 64/128-point quotient-model checks.
All numerical constants are sealed synthetic-oracle observations, not independent physics.
-/
namespace InsacermoOrbit

set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def twist {α : Type} (f : α → Bool) (recode : α ≃ α) (flip : Bool) : α → Bool :=
  fun x => (f (recode x)) != flip

theorem twist_is_reversible {α : Type} (f : α → Bool) (recode : α ≃ α) (flip : Bool) :
    ∀ x, twist (twist f recode flip) recode.symm flip x = f x := by
  intro x
  change ((f (recode (recode.symm x)) != flip) != flip) = f x
  rw [recode.apply_symm_apply]
  cases flip <;> cases hx : f x <;> decide

def bit (x i : Nat) : Nat := (x / (2 ^ i)) % 2

def project (x : Nat) (positions : Array Nat) : Nat :=
  (List.range positions.size).foldl
    (fun acc k => acc + bit x (positions.getD k 0) * 2 ^ k) 0

def lift (i : Nat) (positions : Array Nat) : Nat :=
  (List.range positions.size).foldl
    (fun acc k => acc + bit i k * 2 ^ (positions.getD k 0)) 0

def canonToLocal (perm : Array Nat) (polarity i : Nat) : Nat :=
  (List.range 5).foldl
    (fun acc k => acc + ((bit i k + bit polarity k) % 2) * 2 ^ (perm.getD k 0)) 0

def localToCanon (perm : Array Nat) (polarity i : Nat) : Nat :=
  (List.range 5).foldl
    (fun acc k => acc + ((bit i (perm.getD k 0) + bit polarity k) % 2) * 2 ^ k) 0

def tableBit (table idx : Nat) : Bool := bit table idx == 1

def verifyOrbit (local canon : Nat) (perm : Array Nat) (polarity : Nat) (flip : Bool) : Bool :=
  (List.range 32).all (fun j =>
    ((tableBit local (canonToLocal perm polarity j)) != flip) == tableBit canon j)

def modelEval (canon : Nat) (support perm extras : Array Nat)
    (polarity connector x : Nat) : Bool :=
  let local := project x support
  let coordinate := localToCanon perm polarity local
  let hv := bit canon coordinate
  let other := project x extras
  tableBit connector (hv * 2 ^ extras.size + other)

def verifyQuotient (canon : Nat) (support perm extras bits : Array Nat)
    (polarity connector actual : Nat) : Bool :=
  (List.range (2 ^ bits.size)).all (fun i =>
    modelEval canon support perm extras polarity connector (lift i bits) ==
      tableBit actual i)

theorem source_0_witness :
  verifyOrbit 909560118 56032425 #[0,3,4,2,1] 2 false = true := by decide

theorem source_1_witness :
  verifyOrbit 300818145 56032425 #[0,2,4,1,3] 0 false = true := by decide

theorem source_2_witness :
  verifyOrbit 2573847612 56032425 #[0,2,3,4,1] 26 false = true := by decide

theorem target_0_projected :
  verifyQuotient 56032425 #[1,8,10,14,18] #[0,1,2,3,4] #[17] #[1,8,10,14,17,18]
    6 6 4569676521334456170 = true := by decide

theorem target_1_projected :
  verifyQuotient 56032425 #[6,15,16,17,21] #[0,2,3,1,4] #[11] #[6,11,15,16,17,21]
    1 14 14902075807298878926 = true := by decide

theorem target_2_projected :
  verifyQuotient 56032425 #[6,11,20,21,22] #[0,3,4,2,1] #[5,19] #[5,6,11,19,20,21,22]
    31 210 259744967675747196240661836020296642650 = true := by decide

theorem target_3_projected :
  verifyQuotient 56032425 #[1,5,8,14,18] #[0,1,3,2,4] #[2] #[1,2,5,8,14,18]
    26 6 7364395582523992380 = true := by decide

end InsacermoOrbit
