import InsacermoActionabilityInformation.ContractFactorization

namespace InsacermoActionabilityInformation

/-- If a candidate state is safe, then the state with at least as much
information and at least as much capability is also safe. This packages the
bi-monotone theorem as a maximal-feasibility principle. -/
theorem maximalPoint_safe_of_candidate_safe
    {S A YMax Y : Type*}
    {Good : S → A → Prop} {B : Set S}
    {C Cmax : Set A} {hmax : S → YMax} {h : S → Y}
    (hsafe : SafeRep Good B C h)
    (href : Refines hmax h)
    (hcap : C ⊆ Cmax) :
    SafeRep Good B Cmax hmax := by
  exact safeRep_of_refines_of_capabilitySubset hsafe href hcap

/-- Maximal-point obstruction. If the finest allowed observation together
with the largest allowed capability set is unsafe, then every admissible
candidate below it in the product order is unsafe. -/
theorem maximalPoint_unsafe_blocks_candidate
    {S A YMax Y : Type*}
    {Good : S → A → Prop} {B : Set S}
    {C Cmax : Set A} {hmax : S → YMax} {h : S → Y}
    (hunsafeMax : ¬ SafeRep Good B Cmax hmax)
    (href : Refines hmax h)
    (hcap : C ⊆ Cmax) :
    ¬ SafeRep Good B C h := by
  intro hsafe
  exact hunsafeMax (maximalPoint_safe_of_candidate_safe hsafe href hcap)

/-- Feasibility-before-optimization, pointwise form. Any admissible safe
candidate proves the maximal point safe; conversely, if the maximal point is
itself among the allowed states, its safety already witnesses feasibility. -/
theorem candidateSafe_implies_maximalSafe
    {S A YMax Y : Type*}
    {Good : S → A → Prop} {B : Set S}
    {C Cmax : Set A} {hmax : S → YMax} {h : S → Y}
    (href : Refines hmax h)
    (hcap : C ⊆ Cmax) :
    SafeRep Good B C h → SafeRep Good B Cmax hmax := by
  intro hsafe
  exact maximalPoint_safe_of_candidate_safe hsafe href hcap

/-- Immediate REFUSE certificate for a whole search space represented by one
candidate: once the product-order maximum is unsafe, this candidate cannot be
safe and therefore need not be explored. -/
theorem refuse_candidate_from_maximal_obstruction
    {S A YMax Y : Type*}
    {Good : S → A → Prop} {B : Set S}
    {C Cmax : Set A} {hmax : S → YMax} {h : S → Y}
    (hunsafeMax : ¬ SafeRep Good B Cmax hmax)
    (href : Refines hmax h)
    (hcap : C ⊆ Cmax) :
    ¬ SafeRep Good B C h :=
  maximalPoint_unsafe_blocks_candidate hunsafeMax href hcap

/-- Deterministic specialization: if the maximal allowed observation still
aliases two admissible worlds requiring different actions, and all required
actions are present in `Cmax`, then every lower-information/lower-capability
candidate is unsafe. -/
theorem deterministic_maximalCollision_blocks_candidate
    {S A YMax Y : Type*}
    {B : Set S} {C Cmax : Set A}
    {hmax : S → YMax} {h : S → Y} {label : S → A}
    (hcapMax : ∀ s, s ∈ B → label s ∈ Cmax)
    {s t : S} (hsB : s ∈ B) (htB : t ∈ B)
    (halias : hmax s = hmax t) (hdiff : label s ≠ label t)
    (href : Refines hmax h) (hcap : C ⊆ Cmax) :
    ¬ SafeRep (DeterministicGood label) B C h := by
  have hunsafeMax : ¬ SafeRep (DeterministicGood label) B Cmax hmax :=
    deterministic_crossLabel_alias_blocks_safeRep hcapMax hsB htB halias hdiff
  exact maximalPoint_unsafe_blocks_candidate hunsafeMax href hcap

end InsacermoActionabilityInformation
