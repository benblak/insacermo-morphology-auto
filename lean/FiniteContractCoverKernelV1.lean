import Std

/-!
Independent INSACERMO finite contract-cover certificate checker.
A clause lists informative atoms; a chosen mask satisfies a clause if
it selects at least one listed atom. A contract is satisfied if every
clause is satisfied. CertifiedMin means no feasible mask with fewer
selected atoms exists. This checker DOES NOT depend on Python's search.
No ML, no custom axioms, no sorry/admit.
-/
namespace INSACERMO.FiniteContractCover

def covers (clauses : List (List Nat)) (chosen : Nat) : Bool :=
  clauses.all fun clause => clause.any fun atom => chosen.testBit atom

def count (n chosen : Nat) : Nat :=
  ((List.range n).filter fun atom => chosen.testBit atom).length

def certifyMinimum (n : Nat) (clauses : List (List Nat)) (chosen : Nat) : Bool :=
  decide (chosen < 2^n) && covers clauses chosen &&
  (List.range (2^n)).all (fun candidate =>
    if covers clauses candidate
    then decide (count n chosen <= count n candidate)
    else true)

def certifyImpossible (n : Nat) (clauses : List (List Nat)) : Bool :=
  (List.range (2^n)).all fun candidate => !(covers clauses candidate)

def certifyCapacityImpossible (n cap : Nat) (clauses : List (List Nat)) : Bool :=
  (List.range (2^n)).all fun candidate =>
    !(covers clauses candidate) || decide (cap < count n candidate)

/-- A verified minimum certificate necessarily preserves every clause. -/
theorem certificate_guarantees_coverage (n : Nat) (clauses : List (List Nat))
    (choice : Nat) (h : certifyMinimum n clauses choice = true) :
    covers clauses choice = true := by
  simp [certifyMinimum] at h
  exact h.2.1

/-- A true certificate implies no smaller subset can satisfy the finite
    contract. This theorem is independent of any particular data set. -/
theorem certificate_guarantees_minimum (n : Nat)
    (clauses : List (List Nat)) (choice : Nat)
    (h : certifyMinimum n clauses choice = true) (candidate : Nat)
    (hRange : candidate < 2^n)
    (hCandidate : covers clauses candidate = true) :
    count n choice <= count n candidate := by
  simp only [certifyMinimum, Bool.and_eq_true] at h
  have hAll := h.2.2
  have hm : candidate ∈ List.range (2^n) := List.mem_range.mpr hRange
  have hc : (if covers clauses candidate
    then decide (count n choice <= count n candidate) else true) = true := by
    exact (List.all_eq_true.mp hAll) candidate hm
  simp [hCandidate] at hc
  exact hc

end INSACERMO.FiniteContractCover
