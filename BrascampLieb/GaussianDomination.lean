import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Gaussian majorants for the unnormalized joint moments

These estimates concern ordinary Lebesgue integrability. A quadratic or
linear observable times a Gaussian and any fixed real linear tilt is
integrable. They are used to justify actual moment limits, rather than
allowing a totalized integral to conceal nonintegrability.
-/

namespace TheoremA2.BrascampLieb

open MeasureTheory Measure Filter
open scoped Topology RealInnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

theorem integrable_gaussian_linear {a : ℝ} (ha : 0 < a) (w : E) :
    Integrable (fun x : E => Real.exp (-a * ‖x‖ ^ 2 + ⟪w, x⟫)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (a : ℂ)) (by simpa using ha) (1 : ℂ) w).norm
  convert h using 1
  ext x
  simp [Complex.norm_exp, ← Complex.ofReal_pow]

theorem quadratic_gaussian_linear_bound {a : ℝ} (ha : 0 < a) (w x : E) :
    ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2 + ⟪w, x⟫) ≤
      (2 / a) * Real.exp (-(a / 2) * ‖x‖ ^ 2 + ⟪w, x⟫) := by
  have hu : (a / 2) * ‖x‖ ^ 2 ≤ Real.exp ((a / 2) * ‖x‖ ^ 2) :=
    by linarith [Real.add_one_le_exp ((a / 2) * ‖x‖ ^ 2)]
  have hs : ‖x‖ ^ 2 ≤ (2 / a) * Real.exp ((a / 2) * ‖x‖ ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 2 / a by positivity)
    have heq : (2 / a) * ((a / 2) * ‖x‖ ^ 2) = ‖x‖ ^ 2 := by
      field_simp [ne_of_gt ha]
    simpa only [heq] using hh
  calc
    _ ≤ ((2 / a) * Real.exp ((a / 2) * ‖x‖ ^ 2)) *
        Real.exp (-a * ‖x‖ ^ 2 + ⟪w, x⟫) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem integrable_quadratic_gaussian_linear {a : ℝ} (ha : 0 < a) (w : E) :
    Integrable (fun x : E => ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2 + ⟪w, x⟫)) := by
  apply ((integrable_gaussian_linear (div_pos ha (by norm_num : (0 : ℝ) < 2)) w).const_mul
    (2 / a)).mono'
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      exact quadratic_gaussian_linear_bound ha w x)

theorem integrable_one_add_quadratic_gaussian_linear {a : ℝ} (ha : 0 < a) (w : E) :
    Integrable (fun x : E => (1 + ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2 + ⟪w, x⟫)) := by
  simp only [add_mul, one_mul]
  exact (integrable_gaussian_linear ha w).add (integrable_quadratic_gaussian_linear ha w)

/-- A measurable observable with a concrete quadratic Gaussian bound is integrable. -/
theorem integrable_of_quadratic_gaussian_bound {a C : ℝ} (ha : 0 < a) (w : E)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ 2) *
      Real.exp (-a * ‖x‖ ^ 2 + ⟪w, x⟫)) : Integrable f := by
  apply ((integrable_one_add_quadratic_gaussian_linear ha w).const_mul C).mono' hf
  exact Eventually.of_forall (fun x => by simpa only [mul_assoc] using hbound x)

end
end TheoremA2.BrascampLieb
