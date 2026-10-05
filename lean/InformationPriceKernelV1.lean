import Std

namespace Insacermo

universe u v w z

variable {World : Type u} {Probe : Type v} {Obs : Type w} {Action : Type z}

def SameOn
    (observe : Probe → World → Obs)
    (S : List Probe) (x y : World) : Prop :=
  ∀ p, p ∈ S → observe p x = observe p y

def CertifiesAt
    (observe : Probe → World → Obs)
    (act : World → Action)
    (S : List Probe) (x : World) : Prop :=
  ∀ y, SameOn observe S x y → act y = act x

def HitsConflictsAt
    (observe : Probe → World → Obs)
    (act : World → Action)
    (S : List Probe) (x : World) : Prop :=
  ∀ y, act y ≠ act x →
    ∃ p, p ∈ S ∧ observe p y ≠ observe p x

/--
For a fixed world x, a finite probe certificate is valid exactly when it hits
every world whose required action differs from the action at x.
-/
theorem certifiesAt_iff_hitsConflictsAt
    (observe : Probe → World → Obs)
    (act : World → Action)
    (S : List Probe) (x : World) :
    CertifiesAt observe act S x ↔ HitsConflictsAt observe act S x := by
  constructor
  · intro hcert y hdiff
    apply Classical.byContradiction
    intro hnone
    have hsame : SameOn observe S x y := by
      intro p hp
      apply Classical.byContradiction
      intro hsep
      exact hnone ⟨p, hp, fun hyx => hsep hyx.symm⟩
    exact hdiff (hcert y hsame)
  · intro hhit y hsame
    apply Classical.byContradiction
    intro hdiff
    obtain ⟨p, hp, hsep⟩ := hhit y hdiff
    exact hsep (hsame p hp).symm

/-- Adding probes cannot destroy an already valid certificate. -/
theorem certifiesAt_mono
    (observe : Probe → World → Obs)
    (act : World → Action)
    {S T : List Probe} {x : World}
    (hsub : ∀ p, p ∈ S → p ∈ T)
    (hcert : CertifiesAt observe act S x) :
    CertifiesAt observe act T x := by
  intro y hsameT
  apply hcert y
  intro p hp
  exact hsameT p (hsub p hp)

def ProofPriceLe
    (observe : Probe → World → Obs)
    (act : World → Action)
    (k : Nat) (x : World) : Prop :=
  ∃ S : List Probe, S.length ≤ k ∧ CertifiesAt observe act S x

theorem certificate_gives_price_bound
    (observe : Probe → World → Obs)
    (act : World → Action)
    (S : List Probe) (x : World)
    (hcert : CertifiesAt observe act S x) :
    ProofPriceLe observe act S.length x := by
  exact ⟨S, Nat.le_refl _, hcert⟩

theorem proofPriceLe_mono
    (observe : Probe → World → Obs)
    (act : World → Action)
    {k m : Nat} {x : World}
    (hkm : k ≤ m)
    (hk : ProofPriceLe observe act k x) :
    ProofPriceLe observe act m x := by
  obtain ⟨S, hSk, hcert⟩ := hk
  exact ⟨S, Nat.le_trans hSk hkm, hcert⟩

def ProofPriceWithinLe
    (observe : Probe → World → Obs)
    (act : World → Action)
    (library : List Probe)
    (k : Nat) (x : World) : Prop :=
  ∃ S : List Probe,
    (∀ p, p ∈ S → p ∈ library) ∧
    S.length ≤ k ∧
    CertifiesAt observe act S x

/--
If the full declared probe library cannot distinguish x from one conflicting
world y, then no sub-library certificate can authorize the action at x.
-/
theorem undistinguished_conflict_forces_refusal
    (observe : Probe → World → Obs)
    (act : World → Action)
    (library : List Probe)
    (x y : World)
    (hdiff : act y ≠ act x)
    (hsame : SameOn observe library x y) :
    ∀ k, ¬ ProofPriceWithinLe observe act library k x := by
  intro k hprice
  obtain ⟨S, hsub, _, hcert⟩ := hprice
  have hsameS : SameOn observe S x y := by
    intro p hp
    exact hsame p (hsub p hp)
  exact hdiff (hcert y hsameS)

/--
If the whole library certifies x, then a finite price bound exists: at worst,
read the whole library.
-/
theorem full_library_gives_finite_price
    (observe : Probe → World → Obs)
    (act : World → Action)
    (library : List Probe)
    (x : World)
    (hcert : CertifiesAt observe act library x) :
    ProofPriceWithinLe observe act library library.length x := by
  refine ⟨library, ?_, Nat.le_refl _, hcert⟩
  intro p hp
  exact hp

/--
A strict action conflict left inside an evidence fiber is a direct witness that
the evidence cannot certify the action.
-/
theorem conflict_in_fiber_refutes_certificate
    (observe : Probe → World → Obs)
    (act : World → Action)
    (S : List Probe)
    (x y : World)
    (hsame : SameOn observe S x y)
    (hdiff : act y ≠ act x) :
    ¬ CertifiesAt observe act S x := by
  intro hcert
  exact hdiff (hcert y hsame)

end Insacermo
