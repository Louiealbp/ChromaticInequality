import TheoremA2.JointCovariance
import TheoremA2.JointComparison
import TheoremA2.ConcreteReduction

/-!
# Substitution of the exact A.2 parameters in the joint comparison

All scalar cutoffs, characteristic-function identities and positive-reference
normalizations are already proved. This module performs their exact
substitution after the all-field spin estimate has been supplied.
-/

namespace TheoremA2

open TheoremA2.JointReference TheoremA2.JointMarginal TheoremA2.PeriodicCells
open scoped BigOperators
noncomputable section

theorem joint_spin_interaction_posSemidef {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ((2 * lam) • (B * B.transpose)).PosSemidef := by
  have hB : (B * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose B
  exact hB.smul (by positivity)

theorem scaled_spin_interaction_cutoff {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) (i : Fin k) :
    2 * (((2 * referenceLambda k) • (scaledMatrix S * (scaledMatrix S).transpose)) i i) ≤
      diagonalCutoff / dimensionLog k := by
  have he : (((2 * referenceLambda k) •
      (scaledMatrix S * (scaledMatrix S).transpose)) i i) =
      (2 * referenceLambda k) * rowVariance k := by
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
      ← pow_two, scaledMatrix_row_sq hk S hS]
  rw [he]
  nlinarith only [spin_diagonal_cutoff hk]

theorem projection_scaledMatrix {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (σ : Spin k) (j : Fin k) :
    projection (scaledMatrix S) σ j = theta k * ∑ i, sign (σ i) * S i j := by
  unfold projection scaledMatrix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem realCharacteristic_eq_scaled_cosine_average {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) :
    realCharacteristic S (theta k) =
      average (fun σ : Spin k => ∏ j, Real.cos (projection (scaledMatrix S) σ j)) := by
  rw [realCharacteristic_eq_cosine_product]
  simp only [projection_scaledMatrix]

theorem comparison_of_scaled_spin_covariance {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S)
    (hspin : SpinCovarianceBound (scaledMatrix S) (referenceLambda k) precisionConstant) :
    actualReferenceNormalizer S * comparisonBracket k ≤ realCharacteristic S (theta k) := by
  have hlam := referenceLambda_ge_two hk
  have hlampos : 0 < referenceLambda k := lt_of_lt_of_le (by norm_num) hlam
  have hc : 0 < precisionConstant := by norm_num [precisionConstant]
  have hh := relative_comparison_of_joint_mgf (scaledMatrix S)
    hlam hc (BrascampLieb.curvatureConstant_pos hlampos) (prior_kappa_lower hlam)
    (rowVariance_pos hk) (decoder_variance_cutoff hk)
    (fun j => (scaledMatrix_column_sq hk S hS j).le)
    (by
      intro u
      simpa only [CellEnergyComparison.quadratic_eq_coordinate] using
        actual_joint_mgf (scaledMatrix S) hlampos hc hspin u)
  rw [← realCharacteristic_eq_scaled_cosine_average S] at hh
  simpa only [actualReferenceNormalizer, comparisonBracket, referenceError, scalarError, neg_mul] using hh

theorem conclusion_of_scaled_spin_covariance {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S)
    (hspin : SpinCovarianceBound (scaledMatrix S) (referenceLambda k) precisionConstant) :
    A2Conclusion S :=
  conclusion_of_concrete_relative_comparison hk S hS
    (comparison_of_scaled_spin_covariance hk S hS hspin)

end
end TheoremA2
