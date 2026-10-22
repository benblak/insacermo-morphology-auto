import C3.PortableExactSearchV1
/-!
80-instance finite proof for the *declared* INSACERMO MemGuard/C3 audit models.
Inputs are re-constructed deterministically from the frozen experiment:
  EXIT_200..239 (exceptions EXIT_222, EXIT_225), NO_ENTRY_200..239.
The external replay binds these cases to SHA-256 commitments. No theorem
in this file computes SHA-256 of external files or validates physical sensors.
-/
namespace MemGuardC3All80
open PortableC3
def frozenZipSHA256 : String :=
  "4323bb753be1fcf8175f3edc010e670901ca470c55f668df6ead6ab29ed6ce4e"
def bindingManifestRootSHA256 : String :=
  "597b83a38dd496a08172ecd45e6134b132d7f2e34426697fbd4642367adac697"

def specialSeed (seed : Nat) : Bool := seed == 222 || seed == 225
def goodFor (isExit : Bool) (seed : Nat) : List (List Bool) :=
  if !isExit then
    [[true,true],[true,true],[true,true],[true,true]]
  else if specialSeed seed then
    [[true,false],[true,false],[true,true],[false,true]]
  else
    [[true,false],[true,false],[true,false],[false,true]]

def modelFor (isExit : Bool) (seed : Nat) : Model := {
  worldCount := 4
  actionCount := 2
  probeCount := 3
  good := goodFor isExit seed
  sense := [[2,1,1,1],[1,2,1,1],[1,1,1,2]]
  nextFalse := [[0,1,2,3],[0,1,2,3],[0,1,2,3]]
  nextTrue := [[0,1,2,3],[0,1,2,3],[0,1,2,3]]
  actionCost := [0,0]
  probeCost := [1,1,1]
}
def treeFor (isExit : Bool) (seed : Nat) : Tree :=
  if !isExit then Tree.act 0
  else if specialSeed seed then
    Tree.probe 0 (Tree.probe 0 (Tree.probe 1 (Tree.act 1) (Tree.act 0)) (Tree.act 0)) (Tree.act 0)
  else
    Tree.probe 0 (Tree.probe 0 (Tree.probe 2 (Tree.act 0) (Tree.act 1)) (Tree.act 0)) (Tree.act 0)

def upper : List Nat := [0,1,2,3]
def runCases : List (Bool × Nat) :=
  (List.range 40).flatMap (fun i => [(true, 200+i), (false, 200+i)])

def instanceOK (p : Bool × Nat) : Bool :=
  let m := modelFor p.1 p.2
  wellFormed m upper &&
  checkTree m 3 3 upper (treeFor p.1 p.2)

set_option maxRecDepth 16384
set_option maxHeartbeats 100000000

theorem eighty_distinct_declared_instances : runCases.length = 80 := by
  decide +kernel

theorem all_eighty_plans_accepted :
    runCases.all instanceOK = true := by
  decide +kernel

theorem no_extra_instances :
    runCases.all (fun p => decide (200 ≤ p.2 ∧ p.2 ≤ 239)) = true := by
  decide +kernel

theorem declared_archive_commitment_format :
    frozenZipSHA256.length = 64 ∧ bindingManifestRootSHA256.length = 64 := by
  decide +kernel

theorem eighty_models_safe (p : Bool × Nat)
    (hp : p ∈ runCases) :
    Safe (modelFor p.1 p.2) 3 3 upper (treeFor p.1 p.2) := by
  have h : instanceOK p = true := (List.all_eq_true.mp all_eighty_plans_accepted) p hp
  have hc : checkTree (modelFor p.1 p.2) 3 3 upper (treeFor p.1 p.2) = true := by
    simp only [instanceOK, Bool.and_eq_true] at h
    exact h.2
  exact accepted_certificate_sound _ _ _ _ _ hc
end MemGuardC3All80
