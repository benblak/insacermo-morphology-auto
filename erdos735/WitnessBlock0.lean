import WitnessBase

namespace Erdos302Witness735
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
theorem checked_0 :
  ∀ b : Fin 50, ∀ c : Fin 735,
    ¬ forbiddenPair (b.val + 0) c.val := by
  decide +kernel
#print axioms checked_0
end Erdos302Witness735
