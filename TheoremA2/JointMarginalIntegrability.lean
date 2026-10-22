import TheoremA2.JointMarginalPotential
import TheoremA2.JointMarginalBounds
import BrascampLieb.GaussianDomination

/-!
# Integrability of the actual smooth joint Gibbs approximants

All continuous marginals and their first and second moments are dominated by
explicit Gaussian functions with linear tilts. No totalized nonintegrable
integral is used as a moment.
-/

namespace TheoremA2.JointMarginal

open MeasureTheory Filter
open TheoremA2.JointReference TheoremA2.PeriodicCells TheoremA2.PrincipalInverse
open scoped BigOperators Matrix
noncomputable section

theorem continuous_jointWeight {r s : ℕ} {U : ℝ → ℝ} (hU : Continuous U)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ)
    (k : Fin s → ℝ) (σ : Spin r) : Continuous (jointWeight U B lam h k σ) := by
  unfold jointWeight
  apply Real.continuous_exp.comp
  exact ((continuous_const.add (spinLinear B σ).continuous).add (fieldLinear k).continuous).sub
    (continuous_finsetSum _ fun j _ => hU.comp (by fun_prop))

theorem integrable_jointWeight {r s : ℕ} {U : ℝ → ℝ} (hUc : Continuous U)
    {H : ℝ} (hH : 0 < H) (hU : ∀ x, H / 2 * x ^ 2 ≤ U x)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ)
    (k : Fin s → ℝ) (σ : Spin r) : Integrable (jointWeight U B lam h k σ) := by
  apply ((BrascampLieb.integrable_gaussian_linear (show 0 < H / 2 by positivity)
    (WithLp.toLp 2 (projection B σ + k))).const_mul (Real.exp (spinConstant B lam h σ))).mono'
  · exact (continuous_jointWeight hUc B lam h k σ).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_pos (jointWeight_pos U B lam h k σ t)]
      exact jointWeight_gaussian_bound hU B lam h k σ t

theorem integrable_observable_jointWeight {r s : ℕ} {U : ℝ → ℝ} (hUc : Continuous U)
    {H : ℝ} (hH : 0 < H) (hU : ∀ x, H / 2 * x ^ 2 ≤ U x)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ)
    (k : Fin s → ℝ) (σ : Spin r) {g : Auxiliary s → ℝ}
    (hg : AEStronglyMeasurable g volume) {C : ℝ} (hC : 0 ≤ C)
    (hgC : ∀ t, |g t| ≤ C * (1 + ‖t‖ ^ 2)) :
    Integrable (fun t => g t * jointWeight U B lam h k σ t) := by
  apply BrascampLieb.integrable_of_quadratic_gaussian_bound
    (show 0 < H / 2 by positivity) (WithLp.toLp 2 (projection B σ + k))
    (hg.mul (continuous_jointWeight hUc B lam h k σ).aestronglyMeasurable)
    (C := C * Real.exp (spinConstant B lam h σ))
  intro t
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (jointWeight_pos U B lam h k σ t)]
  calc
    _ ≤ (C * (1 + ‖t‖ ^ 2)) * jointWeight U B lam h k σ t :=
      mul_le_mul_of_nonneg_right (hgC t) (jointWeight_pos U B lam h k σ t).le
    _ ≤ (C * (1 + ‖t‖ ^ 2)) *
        (Real.exp (spinConstant B lam h σ) *
          Real.exp (-(H / 2) * ‖t‖ ^ 2 +
            inner ℝ (WithLp.toLp 2 (projection B σ + k)) t)) :=
      mul_le_mul_of_nonneg_left (jointWeight_gaussian_bound hU B lam h k σ t) (by positivity)
    _ = _ := by ring

theorem jointWeight_factorization {r s : ℕ} (U : ℝ → ℝ)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ)
    (k : Fin s → ℝ) (σ : Spin r) (t : Auxiliary s) :
    jointWeight U B lam h k σ t =
      FiniteExponential.weight (spinConstant B lam h) (spinLinear B) t σ *
        Real.exp (fieldLinear k t - ∑ j, U (t j)) := by
  rw [jointWeight, FiniteExponential.weight, ← Real.exp_add]
  congr 1
  ring

theorem sum_jointWeight {r s : ℕ} (U : ℝ → ℝ)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ)
    (k : Fin s → ℝ) (t : Auxiliary s) :
    (∑ σ : Spin r, jointWeight U B lam h k σ t) =
      Real.exp (-potential U B lam h k t) := by
  simp_rw [jointWeight_factorization]
  rw [← Finset.sum_mul, exp_neg_potential]
  exact mul_comm _ _

theorem integrable_marginalWeight {r s : ℕ} {U : ℝ → ℝ} (hUc : Continuous U)
    {H : ℝ} (hH : 0 < H) (hU : ∀ x, H / 2 * x ^ 2 ≤ U x)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ) :
    Integrable (fun t => Real.exp (-potential U B lam h k t)) := by
  simp_rw [← sum_jointWeight]
  exact integrable_finsetSum _ fun σ _ => integrable_jointWeight hUc hH hU B lam h k σ

theorem integrable_conditionalMean_square {r s : ℕ} {U : ℝ → ℝ} (hUc : Continuous U)
    {H : ℝ} (hH : 0 < H) (hU : ∀ x, H / 2 * x ^ 2 ≤ U x)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h u : Fin r → ℝ)
    (k v : Fin s → ℝ) :
    Integrable (fun t => conditionalLinearMean B lam h u v t ^ 2 *
      Real.exp (-potential U B lam h k t)) := by
  simp_rw [← sum_jointWeight, Finset.mul_sum]
  apply integrable_finsetSum
  intro σ _
  apply integrable_observable_jointWeight hUc hH hU B lam h k σ
    ((contDiff_conditionalLinearMean B lam h u v).continuous.pow 2).aestronglyMeasurable
    (momentBound_pos u v).le
  intro t
  rw [abs_of_nonneg (sq_nonneg _)]
  exact conditionalLinearMean_sq_bound B lam h u v t

theorem integrable_linear_jointWeight {r s : ℕ} {U : ℝ → ℝ} (hUc : Continuous U)
    {H : ℝ} (hH : 0 < H) (hU : ∀ x, H / 2 * x ^ 2 ≤ U x)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h u : Fin r → ℝ)
    (k v : Fin s → ℝ) (σ : Spin r) :
    Integrable (fun t => linear u v (σ, t) * jointWeight U B lam h k σ t) := by
  apply integrable_observable_jointWeight hUc hH hU B lam h k σ
    (by unfold linear; fun_prop) (momentBound_pos u v).le
  exact fun t => (linear_first_second_bounds u v σ t).1

theorem integrable_linear_square_jointWeight {r s : ℕ} {U : ℝ → ℝ} (hUc : Continuous U)
    {H : ℝ} (hH : 0 < H) (hU : ∀ x, H / 2 * x ^ 2 ≤ U x)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h u : Fin r → ℝ)
    (k v : Fin s → ℝ) (σ : Spin r) :
    Integrable (fun t => linear u v (σ, t) ^ 2 * jointWeight U B lam h k σ t) := by
  apply integrable_observable_jointWeight hUc hH hU B lam h k σ
    (by unfold linear; fun_prop) (momentBound_pos u v).le
  intro t
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (linear_first_second_bounds u v σ t).2

end
end TheoremA2.JointMarginal
