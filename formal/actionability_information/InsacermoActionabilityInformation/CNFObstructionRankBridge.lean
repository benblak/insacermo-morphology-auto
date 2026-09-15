import InsacermoActionabilityInformation.ObstructionRankLocalAudit

namespace InsacermoActionabilityInformation

namespace CNFContract

/-- A Boolean literal is a variable paired with the value that makes it true.
`(v, true)` is the positive literal and `(v, false)` the negative literal. -/
abbrev Literal (V : Type*) := V × Bool

/-- A finite disjunction of literals. -/
abbrev Clause (V : Type*) := Finset (Literal V)

/-- A finite conjunction of clauses. -/
abbrev Formula (V : Type*) := Finset (Clause V)

variable {V : Type*} [DecidableEq V]

/-- A literal is true under an assignment exactly when the assignment gives
its variable the literal's designated Boolean value. -/
def LiteralSatisfied (x : V → Bool) (l : Literal V) : Prop :=
  x l.1 = l.2

/-- A clause is satisfied when at least one of its literals is true. -/
def ClauseSatisfied (x : V → Bool) (C : Clause V) : Prop :=
  ∃ l ∈ C, LiteralSatisfied x l

/-- A CNF formula is satisfiable when one assignment satisfies every selected
clause. -/
def Sat (F : Formula V) : Prop :=
  ∃ x : V → Bool, ∀ C ∈ F, ClauseSatisfied x C

/-- A MUS is an inclusion-minimal unsatisfiable CNF subformula. -/
def IsMUS (F : Formula V) : Prop :=
  (¬ Sat F) ∧
    ∀ G : Formula V, G ⊂ F → Sat G

/-- The standard CNF-MUS notion is literally the abstract finite-contract
minimal obstruction instantiated by CNF satisfiability. -/
theorem isMUS_iff_abstract {F : Formula V} :
    IsMUS F ↔
      FiniteContractAudit.IsMinimalUnsat (Sat : Formula V → Prop) F := by
  rfl

/-- Every unsatisfiable finite CNF contains an inclusion-minimal
unsatisfiable subformula. -/
theorem exists_MUS_subset {F : Formula V} (hF : ¬ Sat F) :
    ∃ M : Formula V, M ⊆ F ∧ IsMUS M := by
  classical
  rcases FiniteContractAudit.exists_minimalUnsat_subset
      (Sat : Formula V → Prop) hF with ⟨M, hMF, hM⟩
  exact ⟨M, hMF, (isMUS_iff_abstract).mpr hM⟩

/-- All CNF MUSes have at most `k` clauses. -/
def MUSRankAtMost (k : ℕ) : Prop :=
  ∀ F : Formula V, IsMUS F → F.card ≤ k

/-- CNF local audit through depth `k`: every selected subformula of at most
`k` clauses is satisfiable. -/
def PassesLocalAudit (k : ℕ) (F : Formula V) : Prop :=
  FiniteContractAudit.PassesLocalAudit (Sat : Formula V → Prop) k F

/-- Completeness of `k`-clause local auditing for CNF satisfiability. -/
def LocalAuditComplete (k : ℕ) : Prop :=
  FiniteContractAudit.LocalAuditComplete (Sat : Formula V → Prop) k

/-- Exact CNF specialization of the abstract obstruction theorem:
checking all subformulas through `k` clauses decides global satisfiability
iff every MUS has at most `k` clauses. -/
theorem musRankAtMost_iff_localAuditComplete (k : ℕ) :
    MUSRankAtMost (V := V) k ↔ LocalAuditComplete (V := V) k := by
  classical
  change FiniteContractAudit.ObstructionRankAtMost
      (Sat : Formula V → Prop) k ↔
    FiniteContractAudit.LocalAuditComplete (Sat : Formula V → Prop) k
  exact FiniteContractAudit.obstructionRankAtMost_iff_localAuditComplete
    (Sat : Formula V → Prop) k

/-- Exact No-Local-Auditor witness for CNF: a MUS larger than `k` is globally
UNSAT while every subformula of size at most `k` is SAT. -/
theorem large_MUS_is_localAudit_blindSpot
    {k : ℕ} {M : Formula V}
    (hMUS : IsMUS M) (hk : k < M.card) :
    PassesLocalAudit (V := V) k M ∧ ¬ Sat M := by
  classical
  have hAbstract :
      FiniteContractAudit.IsMinimalUnsat (Sat : Formula V → Prop) M :=
    (isMUS_iff_abstract).mp hMUS
  exact FiniteContractAudit.minimalUnsat_large_is_localAudit_blindSpot
    (Sat : Formula V → Prop) hAbstract hk

/-- If CNF MUS size is unbounded, no fixed clause depth can make local
satisfiability auditing complete. -/
theorem unbounded_MUS_implies_no_fixed_localAudit
    (hUnbounded : ∀ k : ℕ, ∃ M : Formula V, IsMUS M ∧ k < M.card) :
    ∀ k : ℕ, ¬ LocalAuditComplete (V := V) k := by
  classical
  intro k hComplete
  rcases hUnbounded k with ⟨M, hMUS, hk⟩
  have hBlind := large_MUS_is_localAudit_blindSpot (V := V) hMUS hk
  have hSat : Sat M := hComplete M hBlind.1
  exact hBlind.2 hSat

end CNFContract

end InsacermoActionabilityInformation
