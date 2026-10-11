import C3.PortableFiniteVerifierV1

/- Soundness / completeness of the generic Boolean certificate checker with
   respect to an explicit recursive PROP specification (for any model data,
   budget, initial scenario list and policy tree, even before well-formedness).
   The finite input well-formedness check is a separate required gate. -/
namespace PortableC3

theorem checkTree_iff_safe (m : Model)
    (depth budget : Nat) (X : List Nat) (t : Tree) :
    checkTree m depth budget X t = true ↔ Safe m depth budget X t := by
  induction t generalizing depth budget X with
  | act a =>
      simp [checkTree, Safe, List.all_eq_true]
  | probe q no yes ihNo ihYes =>
      simp [checkTree, Safe, sensorTotal, List.all_eq_true, ihNo, ihYes]

theorem accepted_certificate_sound (m : Model)
    (depth budget : Nat) (X : List Nat) (t : Tree)
    (h : checkTree m depth budget X t = true) :
    Safe m depth budget X t :=
  (checkTree_iff_safe m depth budget X t).mp h

theorem safe_certificate_accepted (m : Model)
    (depth budget : Nat) (X : List Nat) (t : Tree)
    (h : Safe m depth budget X t) :
    checkTree m depth budget X t = true :=
  (checkTree_iff_safe m depth budget X t).mpr h

end PortableC3
