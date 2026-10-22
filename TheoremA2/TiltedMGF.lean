import Mathlib.Probability.Moments.SubGaussian

/-!
# Integrating the actual tilted variance bound

The cumulant derivatives and scalar Taylor theorem are supplied by mathlib.
Every exponential moment and every tilted variance in the statement refers to
the same given measure; no moment-generating-function estimate is assumed.
-/

namespace TheoremA2

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrating a uniform tilted-variance bound gives the centered MGF bound
at source one. Applying this to each linear projection gives the matrix form. -/
theorem exp_integral_le_of_tilted_variance {X : Ω → ℝ} {v : ℝ}
    (hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hmean : (∫ ω, X ω ∂μ) = 0)
    (hvariance : ∀ t : ℝ, Var[X; μ.tilted (fun ω => t * X ω)] ≤ v) :
    (∫ ω, Real.exp (X ω) ∂μ) ≤ Real.exp (v / 2) := by
  have hs : Set.Icc (0 : ℝ) 1 ⊆ interior (integrableExpSet X μ) := by
    simp [integrableExpSet, hint]
  obtain ⟨u, hu, hTaylor⟩ := exists_cgf_eq_iteratedDeriv_two_cgf_mul
    (by norm_num : (0 : ℝ) < 1) hmean hs
  have hvar : iteratedDeriv 2 (cgf X μ) u ≤ v := by
    rw [← variance_tilted_mul (hs (Set.mem_Icc_of_Ioo hu))]
    exact hvariance u
  have he : cgf X μ 1 ≤ v / 2 := by
    rw [hTaylor]
    simpa using div_le_div_of_nonneg_right hvar (by norm_num : (0 : ℝ) ≤ 2)
  have h := Real.exp_le_exp.2 he
  rw [exp_cgf (hint 1)] at h
  simpa [mgf] using h

end
end TheoremA2
