module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityRealTests
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]

theorem ginibreLocalRegularity_indicator_real_equation
    {ι : Type*} [Fintype ι] (v : ι → E) (U : Set E)
    (u h : E → ℝ) (F : ι → E → ℝ)
    (heq : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i))) =
        (∫ x, h x*θ x)-∑ i, ∫ x, F i x*fderiv ℝ θ x (v i)) :
    ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, U.indicator u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i))) =
        (∫ x, U.indicator h x*θ x)-∑ i, ∫ x, U.indicator (F i) x*fderiv ℝ θ x (v i) := by
  classical
  intro θ hθ hc hs
  have hd (x) (hx : x ∉ U) (i) : fderiv ℝ θ x (v i) = 0 := by
    exact congrArg (fun L => L (v i)) (fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun ht => hx (hs ht)))
  have hl (x) (hx : x ∉ U) : (∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact congrArg (fun L => L (v i)) (fderiv_of_notMem_tsupport (𝕜 := ℝ)
      (fun ht => hx (hs ((tsupport_fderiv_apply_subset ℝ (v i)) ht))))
  have hz (x) (hx : x ∉ U) : θ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
  have hi (f q : E → ℝ) (hq : ∀ x, x ∉ U → q x = 0) :
      (∫ x, U.indicator f x*q x) = ∫ x, f x*q x := by
    apply integral_congr_ae
    exact ae_of_all volume fun x => by
      dsimp only
      by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem hx]
      · simp only [Set.indicator_of_notMem hx, hq x hx, mul_zero]
  rw [hi u _ hl, hi h _ hz]
  simp_rw [hi (F _) _ (fun x hx => hd x hx _)]
  exact heq θ hθ hc hs

#print axioms ginibreLocalRegularity_indicator_real_equation
end
end GinibrePoincare
