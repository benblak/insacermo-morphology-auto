# INSACERMO Temporal Validity — Lean Kernel V1

Purpose: formalize the minimal mathematical spine of the Temporal Validity V1 result without importing the application runtime.

This branch proves only the encoded statements below:

1. **Reserve/debt safety** — a directed debt bound smaller than the declared reserve excludes current badness.
2. **Safe-region filtration** — increasing debt shrinks the safe region.
3. **Observer fracture** — identical observation with incompatible required actions defeats every deterministic observation-only policy.
4. **Temporal indistinguishability** — identical observation traces cannot support two incompatible required actions for an observation-only monitor.
5. **Finite witness** — a two-world concrete instance of the observer-fracture theorem.

It does **not** claim that Lean verifies the Python application, the Occupancy dataset, the numerical estimation of drift, or a statistical generalization theorem.

The CI checks:
- Lean compilation;
- no `sorry`, `admit`, or custom `axiom` declaration;
- `#print axioms` output for every theorem.

Target toolchain: `leanprover/lean4:v4.19.0`.
