import Std

namespace InsacermoDynamic

universe u v w

abbrev WSet (World : Type u) := World → Prop

def Subset {World : Type u} (A B : WSet World) : Prop :=
  ∀ x, A x → B x

def Image {World : Type u} (f : World → World) (B : WSet World) : WSet World :=
  fun y => ∃ x, B x ∧ f x = y

def TransformOp {World : Type u}
    (dom : WSet World) (f : World → World)
    (K : WSet World → Prop) (B : WSet World) : Prop :=
  Subset B dom ∧ K (Image f B)

def BranchImage {World : Type u} {Outcome : Type w}
    (observe : World → Outcome)
    (f : Outcome → World → World)
    (B : WSet World) (result : Outcome) : WSet World :=
  fun y => ∃ x, B x ∧ observe x = result ∧ f result x = y

def ProbeOp {World : Type u} {Outcome : Type w}
    (dom : WSet World)
    (observe : World → Outcome)
    (f : Outcome → World → World)
    (K : WSet World → Prop) (B : WSet World) : Prop :=
  Subset B dom ∧ ∀ result, K (BranchImage observe f B result)

theorem transformOp_iff_witness
    {World : Type u} {Policy : Type v}
    (dom : WSet World) (f : World → World)
    (win : Policy → WSet World)
    (K : WSet World → Prop)
    (hK : ∀ B, K B ↔ ∃ p, Subset B (win p))
    (B : WSet World) :
    TransformOp dom f K B ↔
      Subset B dom ∧ ∃ p, ∀ x, B x → win p (f x) := by
  constructor
  · rintro ⟨hd, hk⟩
    obtain ⟨p, hp⟩ := (hK (Image f B)).mp hk
    refine ⟨hd, p, ?_⟩
    intro x hx
    exact hp (f x) ⟨x, hx, rfl⟩
  · rintro ⟨hd, p, hp⟩
    refine ⟨hd, (hK (Image f B)).mpr ?_⟩
    refine ⟨p, ?_⟩
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [← hxy]
    exact hp x hx

theorem probeOp_iff_branch_witness
    {World : Type u} {Outcome : Type w} {Policy : Type v}
    (dom : WSet World)
    (observe : World → Outcome)
    (f : Outcome → World → World)
    (win : Policy → WSet World)
    (K : WSet World → Prop)
    (hK : ∀ B, K B ↔ ∃ p, Subset B (win p))
    (B : WSet World) :
    ProbeOp dom observe f K B ↔
      Subset B dom ∧
        ∃ choose : Outcome → Policy,
          ∀ x, B x → win (choose (observe x)) (f (observe x) x) := by
  classical
  constructor
  · rintro ⟨hd, hb⟩
    have hpolicy : ∀ result : Outcome,
        ∃ p : Policy, Subset (BranchImage observe f B result) (win p) := by
      intro result
      exact (hK _).mp (hb result)
    let choose : Outcome → Policy := fun result => Classical.choose (hpolicy result)
    refine ⟨hd, choose, ?_⟩
    intro x hx
    have hc := Classical.choose_spec (hpolicy (observe x))
    exact hc (f (observe x) x) ⟨x, hx, rfl, rfl⟩
  · rintro ⟨hd, choose, hwin⟩
    refine ⟨hd, ?_⟩
    intro result
    apply (hK _).mpr
    refine ⟨choose result, ?_⟩
    intro y hy
    obtain ⟨x, hx, hobs, hxy⟩ := hy
    subst y
    simpa [hobs] using hwin x hx

theorem probe_failure_iff
    {World : Type u} {Outcome : Type w}
    (dom : WSet World) (observe : World → Outcome)
    (f : Outcome → World → World)
    (K : WSet World → Prop) (B : WSet World) :
    ¬ ProbeOp dom observe f K B ↔
      ¬ Subset B dom ∨
        ∃ result, ¬ K (BranchImage observe f B result) := by
  classical
  constructor
  · intro hn
    by_cases hd : Subset B dom
    · right
      by_cases he : ∃ result, ¬ K (BranchImage observe f B result)
      · exact he
      · have hall : ∀ result, K (BranchImage observe f B result) := by
          intro result
          by_cases hr : K (BranchImage observe f B result)
          · exact hr
          · exact False.elim (he ⟨result, hr⟩)
        exact False.elim (hn ⟨hd, hall⟩)
    · exact Or.inl hd
  · intro h hp
    rcases h with hd | ⟨result, hbad⟩
    · exact hd hp.1
    · exact hbad (hp.2 result)

end InsacermoDynamic
