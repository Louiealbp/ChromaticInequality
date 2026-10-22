module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]

theorem ginibreLocalRegularity_local_compact_test_integrable
    (U : Set E) (u q : E → ℝ) (hu : LocallyIntegrableOn u U (volume : Measure E))
    (hq : Continuous q) (hc : HasCompactSupport q) (hs : tsupport q ⊆ U) :
    Integrable (fun x => u x*q x) volume := by
  have hi : Integrable (tsupport q |>.indicator u) volume := by
    rw [integrable_indicator_iff (isClosed_tsupport q).measurableSet]
    exact hu.integrableOn_compact_subset hs hc
  have hm := hi.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hq hc
  apply hm.congr
  exact ae_of_all volume fun x => by
    dsimp only
    by_cases hx : x ∈ tsupport q
    · simp only [Set.indicator_of_mem hx, smul_eq_mul]
    · simp only [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, smul_eq_mul, mul_zero]

#print axioms ginibreLocalRegularity_local_compact_test_integrable
end
end GinibrePoincare
