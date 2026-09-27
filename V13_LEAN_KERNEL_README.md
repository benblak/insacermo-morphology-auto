# INSACERMO Lean V1.3 Raw-Data Bridge

This branch adds a small formal bridge for the V1.3 raw/actionability adapter.

Kernel targets:
- observation refinement preserves an existing common-action certificate;
- refinement is transitive;
- capability expansion preserves an existing certificate;
- an aliased pair with no common admissible available action forbids ACT;
- a probe/refinement cannot turn a certified-safe fiber into an unsafe one.

Scientific boundary: this bridge does not infer domain semantics from an anonymous CSV.
The observation map, currently available actions, and admissibility relation remain declared/modelled inputs.

Pinned toolchain: Lean 4.33.1.

Gate:

```bash
lake build
lake env lean scripts/CheckAxioms.lean
```

The branch must not be described as kernel-checked until the CI gate succeeds.
