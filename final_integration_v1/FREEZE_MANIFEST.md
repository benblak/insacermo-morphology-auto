# INSACERMO FINAL INTEGRATION V1 — FREEZE CANDIDATE

Date: 2026-10-02

## Executed chain in this freeze

1. Minimum Proof Acquisition V1 selects an admissible proof source.
2. Certified Online Debt V1 recomputes and verifies the source claim.
3. The integration adapter accepts only a VerifiedDebtBound on the canonical path.
4. Proof-Carrying Temporal Runtime V1 checks reserve, expiry, scope, monotone debt and fracture obligations.
5. The final integration certificate is hash-bound to the base decision receipt.

## Source checkpoints

- Temporal runtime source branch: insacermo-temporal-validity-kernel-v1, source commit 7b8cde01c0224fb8a30c67916f069181fbdf860d.
- Certified Online Debt branch: insacermo-certified-online-debt-v1, checkpoint commit 779caf3919312d23315ddf6208c1430db9789408.
- Minimum Proof Acquisition V1: commit 47c480312e6c573aa3059d6be48dafb9e9d7d96a.
- Adaptive Proof Acquisition V2: commit c49f013b5f47a308339fde8759ae97b444f167d1.
- Occupancy real adaptive audit: commit 6defff2cc30a6dc961a80d92169781d13b66a7ce.
- Occupancy temporal-authority audit: commit 7f381dd46aa15f2f8c255a28415b3a5f31bd5913.

## Scope boundary

This branch executes the post-core proof path end to end. The originating ACT/PROBE/REPAIR/REFUSE core is represented by a hash-bound base receipt at the integration boundary; this branch does not independently recompute the full historical INSACERMO/MAX TOTAL core decision from raw domain inputs.

Valid statement:

The proof-acquisition -> debt-verification -> temporal-validity path is integration-tested and fail-closed at its base-receipt boundary.

Not valid from this branch alone:

- Lean verified the full Python application.
- The historical MAX TOTAL core implementation was re-executed here from raw domain inputs.

## Freeze rule

No new theory layer should be added to this chain unless a real-data or adversarial test demonstrates a specific missing obligation.
