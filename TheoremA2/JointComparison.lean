import TheoremA2.JointCellIdentity
import TheoremA2.WeightedTail

/-!
# The relative comparison from the literal joint exponential moments

This module assembles the actual tail and periodic-cell estimates. Its joint
moment premise will be discharged by the joint covariance theorem; all finite
averages, translated-cell integrals, and lattice energies are fixed definitions.
-/

namespace TheoremA2.JointReference

open MeasureTheory
open TheoremA2.PeriodicCells TheoremA2.PrincipalInverse
open scoped BigOperators Matrix
noncomputable section

theorem weighted_projection_mgf {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam c H rho : ℝ} (hlam : 0 < lam) (hc : 0 < c) (hH : 0 < H)
    (hkappa : 0 ≤ 2 * lam - 1 / H)
    (hcol : ∀ j, (∑ i, B i j ^ 2) ≤ rho)
    (hmgf : ∀ u, (∫ ω, Real.exp (inner ℝ u (vector ω)) ∂law B lam) ≤
      Real.exp (ConvexSupport.quadratic (JointPrecision.precision B lam c H)⁻¹ u / 2))
    (t : ℝ) (j : Fin s) :
    average (fun σ : Spin r => referenceProduct lam (projection B σ) *
      Real.exp (t * projection B σ j)) ≤
    referenceNormalizer B (CosineReference.reference lam) *
      Real.exp (t ^ 2 * rho / (2 * c)) := by
  let u : Fin r → ℝ := fun i => t * B i j
  let h : JointSpace r s := WithLp.toLp 2 (Sum.elim u (0 : Fin s → ℝ))
  have hlin (σ : Spin r) : (∑ i, u i * sign (σ i)) = t * projection B σ j := by
    simp only [u, projection, mul_assoc, Finset.mul_sum]
  have hid : average (fun σ : Spin r => referenceProduct lam (projection B σ) *
      Real.exp (t * projection B σ j)) =
      normalizer B lam * ∫ ω, Real.exp (inner ℝ h (vector ω)) ∂law B lam := by
    simpa only [h, inner_vector, hlin] using weighted_spin_exponential_identity B hlam u
  have hq := JointPrecision.inverse_spin_source_bound B hlam.le hc hH hkappa u
  have hnorm : normSq u = t ^ 2 * ∑ i, B i j ^ 2 := by
    simp only [u, normSq, mul_pow, Finset.mul_sum]
  have hquad : ConvexSupport.quadratic (JointPrecision.precision B lam c H)⁻¹ h / 2 ≤
      t ^ 2 * rho / (2 * c) := by
    rw [CellEnergyComparison.quadratic_eq_coordinate]
    change quadratic (JointPrecision.precision B lam c H)⁻¹
      (Sum.elim u (0 : Fin s → ℝ)) / 2 ≤ _
    calc
      _ ≤ (normSq u / c) / 2 := div_le_div_of_nonneg_right hq (by norm_num)
      _ = (t ^ 2 * ∑ i, B i j ^ 2) / (2 * c) := by rw [hnorm]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg t)) (by positivity)
  rw [hid]
  exact mul_le_mul_of_nonneg_left ((hmgf h).trans (Real.exp_le_exp.2 hquad))
    (normalizer_pos B hlam).le

/-- Equation (76) for the actual reference law, once its exact exponential
moments have been bounded. This combines only proved tail/cell bounds. -/
theorem relative_comparison_of_joint_mgf {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam c H rho : ℝ} (hlam : 2 ≤ lam) (hc : 0 < c) (hH : 0 < H)
    (hkappa : 3 / 4 ≤ 2 * lam - 1 / H)
    (hrho : 0 < rho) (hcut : rho / (decoderBeta * c) ≤ 1 / 1000000)
    (hcol : ∀ j, (∑ i, B i j ^ 2) ≤ rho)
    (hmgf : ∀ u, (∫ ω, Real.exp (inner ℝ u (vector ω)) ∂law B lam) ≤
      Real.exp (ConvexSupport.quadratic (JointPrecision.precision B lam c H)⁻¹ u / 2)) :
    referenceNormalizer B (CosineReference.reference lam) *
      ((1 - 2 * (s : ℝ) * Real.exp (-c / (2 * rho))) *
        Real.exp (-(s : ℝ) * scalarError lam) - latticeError s (rho / c)) ≤
      average (fun σ : Spin r => ∏ j, Real.cos (projection B σ j)) := by
  have hl0 : 0 < lam := by linarith
  apply PeriodicCells.relative_comparison_of_bounds B hlam
  · apply WeightedTail.badMass_le_of_mgf B hl0 hc hrho
    exact weighted_projection_mgf B hl0 hc hH (by linarith) hcol hmgf
  · exact CellEnergyComparison.totalNoncentralMass_le (law B lam) B hl0 hc hH hkappa
      hrho hcut hcol vector (measurable_vector r s) (integrable_exponential_inner B hl0)
      hmgf (translated_cell_identity B hl0)

end
end TheoremA2.JointReference
