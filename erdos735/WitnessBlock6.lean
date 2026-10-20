import WitnessBase

namespace Erdos302Witness735
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
theorem checked_6 :
  ∀ b : Fin 50, ∀ c : Fin 735,
    ¬ forbiddenPair (b.val + 300) c.val := by
  unfold forbiddenPair
  decide +kernel
#print axioms checked_6
end Erdos302Witness735
