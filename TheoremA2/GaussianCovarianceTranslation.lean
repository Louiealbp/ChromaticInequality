import TheoremA2.GaussianCovarianceDensity

/-!
# Exact Gaussian cell translations

The density ratio is derived from the actual square-root density, retaining
both the linear and quadratic source terms. No relative tail estimate is
assumed here.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem standardDensity_shift (z x : ι → ℝ) :
    standardDensity (z + x) =
      standardDensity x * Real.exp (-(z ⬝ᵥ x) - normSq z / 2) := by
  have hs (z x : ℝ) : gaussianPDFReal 0 1 (z + x) =
      gaussianPDFReal 0 1 x * Real.exp (-z * x - z ^ 2 / 2) := by
    simpa [GaussianShift.variance, div_eq_mul_inv, mul_comm] using GaussianShift.scalar_density_shift
      (beta := (1 : ℝ)) (by norm_num) z x
  unfold standardDensity
  simp only [Pi.add_apply, hs, Finset.prod_mul_distrib]
  rw [← Real.exp_sum]
  congr 2
  simp only [dotProduct, normSq, Finset.sum_sub_distrib, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_div]

theorem sqrt_inv_mul_self {T : Matrix ι ι ℝ} (hT : T.PosSemidef) :
    (CFC.sqrt T)⁻¹ * (CFC.sqrt T)⁻¹ = T⁻¹ := by
  rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self T hT.nonneg]

/-- The inverse-square-root dot product is exactly the inverse-covariance form. -/
theorem sqrt_inv_dot {T : Matrix ι ι ℝ} (hT : T.PosDef) (z x : ι → ℝ) :
    ((CFC.sqrt T)⁻¹ *ᵥ z) ⬝ᵥ ((CFC.sqrt T)⁻¹ *ᵥ x) = z ⬝ᵥ (T⁻¹ *ᵥ x) := by
  have hC : (CFC.sqrt T)⁻¹ |>.IsHermitian := (covariance_sqrt_posDef hT).inv.isHermitian
  rw [dotProduct_comm, symmetric_bilinear hC, Matrix.mulVec_mulVec,
    sqrt_inv_mul_self hT.posSemidef, dotProduct_comm]

theorem normSq_sqrt_inv {T : Matrix ι ι ℝ} (hT : T.PosDef) (z : ι → ℝ) :
    normSq ((CFC.sqrt T)⁻¹ *ᵥ z) = quadratic T⁻¹ z := by
  have hh := sqrt_inv_dot hT z z
  simpa only [dotProduct, normSq, pow_two, quadratic] using hh

/-- The literal Gaussian density translation formula for arbitrary vectors. -/
theorem covarianceDensity_shift {T : Matrix ι ι ℝ} (hT : T.PosDef) (z x : ι → ℝ) :
    covarianceDensity T (z + x) = covarianceDensity T x *
      Real.exp (-(z ⬝ᵥ (T⁻¹ *ᵥ x)) - quadratic T⁻¹ z / 2) := by
  unfold covarianceDensity
  rw [Matrix.mulVec_add, standardDensity_shift, sqrt_inv_dot hT, normSq_sqrt_inv hT]
  ring

theorem covarianceDensity_eq_exp {T : Matrix ι ι ℝ} (hT : T.PosDef) (x : ι → ℝ) :
    covarianceDensity T x = covarianceDensity T 0 * Real.exp (-quadratic T⁻¹ x / 2) := by
  simpa [neg_div] using covarianceDensity_shift hT x 0

/-- Exact translation identity for every integrand (integrability is handled
separately when this equality is used in inequalities). -/
theorem integral_covariance_shift {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (z : ι → ℝ) (f : (ι → ℝ) → ℝ) :
    (∫ x, f (z + x) * Real.exp (-(z ⬝ᵥ (T⁻¹ *ᵥ x)) - quadratic T⁻¹ z / 2)
      ∂covarianceGaussian T) = ∫ x, f x ∂covarianceGaussian T := by
  rw [integral_covarianceGaussian_eq hT, integral_covarianceGaussian_eq hT]
  calc
    _ = ∫ x, covarianceDensity T (z + x) * f (z + x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [covarianceDensity_shift hT]
      ring
    _ = _ := integral_add_left_eq_self (fun x => covarianceDensity T x * f x) z

theorem integrable_covariance_shift {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (z : ι → ℝ) {f : (ι → ℝ) → ℝ} (hf : Integrable f (covarianceGaussian T)) :
    Integrable (fun x => f (z + x) *
      Real.exp (-(z ⬝ᵥ (T⁻¹ *ᵥ x)) - quadratic T⁻¹ z / 2)) (covarianceGaussian T) := by
  rw [integrable_covarianceGaussian_iff hT] at hf ⊢
  convert hf.comp_add_left z using 1
  funext x
  rw [covarianceDensity_shift hT]
  ring

end

end TheoremA2.GaussianCovariance
