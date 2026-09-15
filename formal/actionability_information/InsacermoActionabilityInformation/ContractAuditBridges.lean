import InsacermoActionabilityInformation.SignedObstructionRankBridge
import InsacermoActionabilityInformation.HypergraphObstructionRankBridge
import InsacermoActionabilityInformation.CNFObstructionRankBridge

namespace InsacermoActionabilityInformation

/-!
This module deliberately contains no additional mathematics.  It is the
kernel-check target certifying that the abstract finite contract theorem and
its three instantiations compile together:

1. signed-XOR atomic contradictions = unbalanced cycles;
2. common-action atomic contradictions = minimal actionability obstructions;
3. CNF atomic contradictions = minimal unsatisfiable subformulas (MUSes);
4. bounded atomic obstruction size ↔ bounded complete local auditing.
-/

end InsacermoActionabilityInformation
