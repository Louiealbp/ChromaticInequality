import TheoremA2.JointFinalReduction
import TheoremA2.SpinCovarianceTheorems

/-!
# The unrestricted uniform positivity theorem

This final assembly has no covariance, exponential-moment, lattice-tail, or
relative-comparison hypothesis. Its only data are a positive integer and an
arbitrary entrywise sign matrix, exactly as in Theorem A.2.
-/

namespace TheoremA2

open TheoremA2.JointMarginal
noncomputable section

theorem scaled_spin_covariance_bound {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) :
    SpinCovarianceBound (scaledMatrix S) (referenceLambda k) precisionConstant := by
  intro h
  apply SpinCovariance.all_field_covariance_small_diagonal
    (joint_spin_interaction_posSemidef (scaledMatrix S)
      (le_trans (by norm_num) (referenceLambda_ge_two hk)))
  intro i
  simpa only [Fintype.card_fin] using scaled_spin_interaction_cutoff hk S hS i

/-- The actual relative comparison (76), with every analytic premise discharged. -/
theorem concreteRelativeComparison : ConcreteRelativeComparisonStatement := by
  intro k hk S hS
  exact comparison_of_scaled_spin_covariance hk S hS (scaled_spin_covariance_bound hk S hS)

/-- Theorem A.2, for every positive dimension and every real sign matrix. -/
theorem theorem_A_2 {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) : A2Conclusion S :=
  conclusion_of_scaled_spin_covariance hk S hS (scaled_spin_covariance_bound hk S hS)

theorem uniformPositivity : UniformPositivityStatement := by
  intro k hk S hS
  exact theorem_A_2 hk S hS

/-- An expanded public statement, exposing the exact angle and lower bound. -/
theorem theorem_A_2_explicit {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : ∀ i j, S i j = 1 ∨ S i j = -1) :
    let a : ℝ := 1 / 10000000
    let t := a / (Real.sqrt (k : ℝ) * Real.log (4 * (k : ℝ)))
    let b := (1 / 4 : ℝ) * Real.exp (-(64 * a ^ 2 * (k : ℝ)) / Real.log (4 * (k : ℝ)))
    (characteristic S t).im = 0 ∧ b ≤ (characteristic S t).re ∧ 0 < b := by
  simpa only [A2Conclusion, theta, lowerBound, amplitude, dimensionLog] using
    theorem_A_2 hk S hS

end
end TheoremA2
