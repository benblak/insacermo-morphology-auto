# Erdős 302 — f(736) Lean/BV kernel experiment

This branch tests a direct finite upper-bound proof for n=736.

- A subset of {1,...,736} is represented as a BitVec 736.
- All reciprocal forbidden triples a<b<c satisfying a(b+c)=bc are embedded as Boolean clauses.
- The target claim is that every admissible bit-vector has population count < 610.
- Lean `bv_decide` bit-blasts the proposition and checks the generated LRAT UNSAT proof.

This proof path does not trust the Python/MIP result. The MIP run motivated the target;
Lean independently checks the finite Boolean theorem.

Status is only LEAN KERNEL VERIFIED after the GitHub workflow succeeds.
