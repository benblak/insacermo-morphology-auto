/-!
INSACERMO core lab, 2026-11-17.
Generic mathematical reversibility of bijective coordinate renaming and output flips;
finite 32-point orbit witness and 64/128-point quotient-model checks.
All numerical constants are sealed synthetic-oracle observations, not independent physics.
-/
namespace InsacermoOrbit

set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def twist (f : Nat → Bool) (encode : Nat → Nat) (flip : Bool) : Nat → Bool :=
  fun x => (f (encode x)) != flip

theorem twist_is_reversible (f : Nat → Bool) (encode decode : Nat → Nat) (flip : Bool)
    (h : ∀ x, encode (decode x) = x) :
    ∀ x, twist (twist f encode flip) decode flip x = f x := by
  intro x
  change ((f (encode (decode x)) != flip) != flip) = f x
  rw [h x]
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

def verifyOrbit (observed canon : Nat) (perm : Array Nat) (polarity : Nat) (flip : Bool) : Bool :=
  (List.range 32).all (fun j =>
    ((tableBit observed (canonToLocal perm polarity j)) != flip) == tableBit canon j)

def modelEval (canon : Nat) (support perm extras : Array Nat)
    (polarity connector x : Nat) : Bool :=
  let observed := project x support
  let coordinate := localToCanon perm polarity observed
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

/-- An exact same five-input law admits distinct coordinate descriptions.
    Even a COMPLETE truth table cannot identify an orientation uniquely. -/
theorem multiple_exact_coordinate_descriptions :
    verifyOrbit 56032425 56032425 #[0,1,2,3,4] 0 false = true ∧
    verifyOrbit 56032425 56032425 #[0,2,1,3,4] 0 false = true ∧
    verifyOrbit 56032425 56032425 #[0,1,2,3,4] 16 true = true ∧
    (#[0,1,2,3,4] : Array Nat) ≠ #[0,2,1,3,4] := by
  decide

/-- A genuinely shared abstraction yields a semantic relationship between
    two differently encoded representations, whenever a true inverse exists. -/
theorem common_abstraction_transfers (left right shared : Nat → Bool)
    (encodeL encodeR decodeL : Nat → Nat)
    (hleft : ∀ x, left (encodeL x) = shared x)
    (hright : ∀ x, right (encodeR x) = shared x)
    (hinv : ∀ x, encodeL (decodeL x) = x) :
    ∀ x, left x = right (encodeR (decodeL x)) := by
  intro x
  have a := hleft (decodeL x)
  have b := hright (decodeL x)
  simpa [hinv x] using a.trans b.symm

/-- No decoder can be uniformly right about a privileged latent parameter
    when two different parameter descriptions generate EXACTLY the same
    observations, even if the entire observation function is available. -/
theorem no_uniform_unique_parameter_decoder
    (representation : Nat → Nat → Bool) (decoder : (Nat → Bool) → Nat)
    (p q : Nat) (distinct : p ≠ q)
    (indistinguishable : ∀ x, representation p x = representation q x) :
    decoder (representation p) ≠ p ∨ decoder (representation q) ≠ q := by
  classical
  by_cases hp : decoder (representation p) = p
  · right
    intro hq
    have equal_observation_functions : representation p = representation q :=
      funext indistinguishable
    apply distinct
    calc
      p = decoder (representation p) := hp.symm
      _ = decoder (representation q) := by rw [equal_observation_functions]
      _ = q := hq
  · exact Or.inl hp

end InsacermoOrbit
