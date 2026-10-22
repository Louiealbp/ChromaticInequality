module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityLocalizedData

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual localized L² derivative represents the original unknown on every
compact test lying in the region where the cutoff equals one. -/
theorem ginibreLocalRegularity_cutoff_weak_derivative_interior
    (u η : E → ℂ) (g : Lp ℂ 2 (volume : Measure E)) (v : E)
    (hg : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x v*(η x*u x)))
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hone : ∀ x ∈ tsupport θ, η x = 1) :
    (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x v*u x) := by
  rw [hg θ hθ hc]
  congr 1
  apply integral_congr_ae
  exact ae_of_all volume fun x => by
    dsimp only
    by_cases hx : x ∈ tsupport θ
    · rw [hone x hx, one_mul]
    · have hzero : fderiv ℝ θ x v = 0 := by
        have he : θ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
        have hd := he.fderiv_eq (𝕜 := ℝ)
        simpa using congrArg (fun L => L v) hd
      simp [hzero]

#print axioms ginibreLocalRegularity_cutoff_weak_derivative_interior
end
end GinibrePoincare
