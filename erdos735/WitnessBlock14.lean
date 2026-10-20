import WitnessBase

namespace Erdos302Witness735
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
theorem checked_14 :
  ∀ b : Fin 35, ∀ c : Fin 735,
    ¬ forbiddenPair (b.val + 700) c.val := by
  unfold forbiddenPair
  decide +kernel
#print axioms checked_14
end Erdos302Witness735
