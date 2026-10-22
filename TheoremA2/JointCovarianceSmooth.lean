import TheoremA2.JointMarginalIntegrability
import TheoremA2.FiniteContinuousMixture
import BrascampLieb.WeightedLimit

/-!
# The joint covariance estimate for actual smooth Gibbs potentials

This is the Brascamp–Lieb and total-variance step of A.33. The only spin
estimate used is explicitly identified as the all-field covariance bound;
the continuous marginal, its derivatives, all integrability requirements,
and the inverse-Hessian energy comparison are proved from the actual weights.
-/

namespace TheoremA2.JointMarginal

open MeasureTheory ProbabilityTheory GinibrePoincare
open TheoremA2.JointReference TheoremA2.ConvexSupport TheoremA2.PrincipalInverse
open TheoremA2.SpinCovariance
open scoped BigOperators Matrix MatrixOrder
noncomputable section

theorem jointWeight_conditional {r s : ℕ} (U : ℝ → ℝ)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ)
    (k : Fin s → ℝ) (t : Auxiliary s) :
    FiniteContinuousMixture.conditional (jointWeight U B lam h k)
      (jointWeight_pos U B lam h k) t = conditional B lam h t := by
  unfold FiniteContinuousMixture.conditional conditional FiniteExponential.law
  congr 1
  funext σ
  simp only [FiniteContinuousMixture.partition, jointWeight_factorization,
    ← Finset.sum_mul, FiniteExponential.partition]
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero _)]

theorem conditionalMean_jointWeight {r s : ℕ} (U : ℝ → ℝ)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h u : Fin r → ℝ)
    (k v : Fin s → ℝ) (t : Auxiliary s) :
    FiniteContinuousMixture.conditionalMean (jointWeight U B lam h k)
      (jointWeight_pos U B lam h k) (linear u v) t =
        conditionalLinearMean B lam h u v t := by
  rw [FiniteContinuousMixture.conditionalMean, jointWeight_conditional]
  have he (σ : Spin r) : linear u v (σ, t) = u ⬝ᵥ spinVector σ + fieldLinear v t := by
    rw [fieldLinear_apply]
    rfl
  simp_rw [he, expectation_add, expectation_const]
  rfl

theorem conditionalVariance_jointWeight {r s : ℕ} (U : ℝ → ℝ)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h u : Fin r → ℝ)
    (k v : Fin s → ℝ) (t : Auxiliary s) :
    FiniteContinuousMixture.conditionalVariance (jointWeight U B lam h k)
      (jointWeight_pos U B lam h k) (linear u v) t =
        quadratic (covariance B lam h t) u := by
  rw [FiniteContinuousMixture.conditionalVariance, jointWeight_conditional,
    conditionalMean_jointWeight, conditionalLinearMean]
  have he (σ : Spin r) : linear u v (σ, t) -
      ((conditional B lam h t).expectation (fun σ => u ⬝ᵥ spinVector σ) + fieldLinear v t) =
      u ⬝ᵥ spinVector σ - (conditional B lam h t).expectation (fun σ => u ⬝ᵥ spinVector σ) := by
    rw [fieldLinear_apply]
    unfold linear spinVector dotProduct
    ring
  simp_rw [he]
  rw [FiniteContinuousMixture.finite_centered_sq, covariance,
    quadratic_covariance_moments, expectation_dot]

theorem marginal_mass_pos {r s : ℕ} {U : ℝ → ℝ} (hUc : Continuous U)
    {H : ℝ} (hH : 0 < H) (hU : ∀ x, H / 2 * x ^ 2 ≤ U x)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ) :
    0 < ∫ t, Real.exp (-potential U B lam h k t) :=
  integral_exp_pos (integrable_marginalWeight hUc hH hU B lam h k)

theorem continuous_comparisonSchur {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam H : ℝ) (h : Fin r → ℝ) :
    Continuous (fun t => JointPrecision.conditionalSchur B H (covariance B lam h t)) := by
  exact continuous_const.sub
    ((continuous_const.matrix_mul (continuous_covariance B lam h)).matrix_mul continuous_const)

theorem actual_BL_hessian {s : ℕ} (W : Auxiliary s → ℝ) (t : Auxiliary s) :
    correspondenceBrascampLiebHessian W (EuclideanSpace.basisFun (Fin s) ℝ) t =
      hessian W t := rfl

theorem actual_BL_gradient {s : ℕ} (g : Auxiliary s → ℝ) (t : Auxiliary s) :
    correspondenceBrascampLiebGradient g (EuclideanSpace.basisFun (Fin s) ℝ) t =
      gradient g t := rfl

/-- The unnormalized covariance bound for every genuine smooth approximating
joint law. All fields and both test-vector components are arbitrary. -/
theorem smooth_joint_variance_bound {r s : ℕ} {U : ℝ → ℝ}
    (hU : ContDiff ℝ 2 U) {lam c H : ℝ}
    (hlam : 0 < lam) (hc : 0 < c) (hH : 0 < H)
    (hH' : 1 / (2 * lam) < H) (hkappa : 0 ≤ 2 * lam - 1 / H)
    (hcurv : ∀ x, H ≤ deriv (deriv U) x)
    (hquad : ∀ x, H / 2 * x ^ 2 ≤ U x)
    (B : Matrix (Fin r) (Fin s) ℝ) (hspin : SpinCovarianceBound B lam c)
    (h u : Fin r → ℝ) (k v : Fin s → ℝ) :
    (∑ σ : Spin r, ∫ t : Auxiliary s, jointWeight U B lam h k σ t * linear u v (σ, t) ^ 2) -
        (∑ σ : Spin r, ∫ t : Auxiliary s, jointWeight U B lam h k σ t * linear u v (σ, t)) ^ 2 /
          (∫ t, Real.exp (-potential U B lam h k t)) ≤
      quadratic (JointPrecision.precision B lam c H)⁻¹ (Sum.elim u v) *
        (∫ t, Real.exp (-potential U B lam h k t)) := by
  have hZ := marginal_mass_pos hU.continuous hH hquad B lam h k
  have hv := BrascampLieb.wholeSpace_totalVariance_bound
    (potential U B lam h k) (conditionalLinearMean B lam h u v)
    (fun t => quadratic (covariance B lam h t) u)
    (EuclideanSpace.basisFun (Fin s) ℝ)
    (fun t => JointPrecision.conditionalSchur B H (covariance B lam h t))
    (quadratic (JointPrecision.precision B lam c H)⁻¹ (Sum.elim u v))
    (contDiff_potential hU B lam h k)
    (integrable_marginalWeight hU.continuous hH hquad B lam h k)
    (continuous_comparisonSchur B lam H h)
    (comparisonSchur_posDef B hlam hc hH' hspin h)
    (by simpa only [actual_BL_hessian] using hessian_difference_posSemidef hU hcurv B lam h k)
    ((contDiff_conditionalLinearMean B lam h u v).of_le (by norm_num))
    (integrable_conditionalMean_square hU.continuous hH hquad B lam h u k v)
    (continuous_conditional_variance B lam h u)
    (fun t => quadratic_nonneg (covariance_posSemidef B lam h t) u)
    (by simpa only [actual_BL_gradient, quadratic] using
      total_variance_integrand_le B hlam hc hH hH' hkappa hspin h u v)
  have hz' : 0 < FiniteContinuousMixture.total volume (jointWeight U B lam h k) := by
    simpa only [FiniteContinuousMixture.total, FiniteContinuousMixture.partition, sum_jointWeight]
      using hZ
  have hid := FiniteContinuousMixture.weighted_variance_decomposition volume
    (jointWeight U B lam h k)
    (fun σ => (continuous_jointWeight hU.continuous B lam h k σ).measurable)
    (jointWeight_pos U B lam h k) hz' (linear u v) (measurable_linear u v)
    (fun σ => by simpa only [mul_comm] using integrable_linear_jointWeight hU.continuous hH hquad B lam h u k v σ)
    (fun σ => by simpa only [mul_comm] using integrable_linear_square_jointWeight hU.continuous hH hquad B lam h u k v σ)
  simp only [FiniteContinuousMixture.total, FiniteContinuousMixture.partition, sum_jointWeight,
    conditionalMean_jointWeight, conditionalVariance_jointWeight] at hid
  rw [hid]
  simpa only [bakryEmeryGibbsWeight, mul_comm] using hv

end
end TheoremA2.JointMarginal
