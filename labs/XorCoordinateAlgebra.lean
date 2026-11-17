namespace InsacermoXorAlgebra

def latent (a b c d e : Bool) : Bool :=
  (((((a != b) != c) != d) != e) != (a && b)) != (c && d)

theorem polar_pair (a b u v : Bool) :
    (((((a != u) && (b != v)) != (a && b)) != (u && v))) =
    ((a && v) != (u && b)) := by
  cases a <;> cases b <;> cases u <;> cases v <;> decide

theorem shifted_pair (a b s t : Bool) :
    ((a != s) && (b != t)) =
    ((((a && b) != (s && b)) != (a && t)) != (s && t)) := by
  cases a <;> cases b <;> cases s <;> cases t <;> decide

theorem latent_decomposition (a b c d e : Bool) :
    latent a b c d e =
    (((((a != b) != (a && b)) != (c != d)) != (c && d)) != e) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem same_features_same_law
    (A B C D E : Nat → Bool)
    (x y : Nat)
    (ha : A x = A y) (hb : B x = B y)
    (hc : C x = C y) (hd : D x = D y)
    (he : E x = E y) :
    latent (A x) (B x) (C x) (D x) (E x) =
    latent (A y) (B y) (C y) (D y) (E y) := by
  simp [ha, hb, hc, hd, he]

def flipAt (f : Nat → Bool) (exception : Nat) (x : Nat) : Bool :=
  if x = exception then !(f x) else f x

theorem transcript_preserved_with_hidden_exception
    (observed : List Nat) (exception : Nat)
    (notSeen : exception ∉ observed) (f : Nat → Bool) :
    (∀ x ∈ observed, flipAt f exception x = f x) ∧
    flipAt f exception exception ≠ f exception := by
  constructor
  · intro x hx
    have neq : x ≠ exception := by
      intro h
      apply notSeen
      simpa [h] using hx
    simp [flipAt, neq]
  · cases h : f exception <;> simp [flipAt, h]

end InsacermoXorAlgebra
