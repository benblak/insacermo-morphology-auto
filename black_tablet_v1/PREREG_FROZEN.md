# INSACERMO BLACK TABLET V1 — frozen protocol

Date: 2026-09-27
Branch: insacermo-black-tablet-v1

## Object

Construct one finite "tablet" that contains no names, no language, and no privileged labels:
only seven anonymous marks and twelve undirected relations.

The intended contract target is not identified by a written label. It must be recoverable
from the relational structure itself under every automorphism compatible with the tablet.

## Frozen tablet

Vertices: 0..6 (labels exist only for computation; they are not part of the transmitted object).

Edges:
(0,2), (0,4), (0,5), (0,6),
(1,2), (1,3), (1,5),
(2,4), (2,6),
(3,4), (3,6),
(4,5).

Target for verification: vertex 0.

## Strong conditions checked

1. Global invariance:
   target 0 must be fixed by every graph automorphism.

2. Nontrivial ambiguity remains:
   the graph must have more than one automorphism, so full decoding is not unique.

3. Local disguise:
   target 0 must share its simple local signature
   (degree + multiset of neighbor degrees)
   with at least two other vertices. Thus the target is not recoverable
   by the simplest local cue.

4. Contract-relevant fragility:
   deleting at least one single relation must preserve connectedness
   while making the target non-invariant under the resulting automorphism group.

5. INSACERMO agreement:
   the unmodified actionability engine must return ACT on the intact tablet
   and REFUSE on a frozen damaged tablet whose surviving decoder-worlds move the target.

## Frozen damage test

Delete edge (0,2).

No rule or graph edge may be changed after seeing the run.

## Meaning of the experiment

This is not a universal language and does not prove an alien or future civilization
would infer our intended semantics. It is an exact demonstration of a narrower claim:

a contract-relevant referent can be recoverable from global relational structure even when:
- labels are absent,
- multiple whole-message decodings remain possible,
- simple local features do not uniquely identify it.

And one missing relation can destroy that guarantee.
