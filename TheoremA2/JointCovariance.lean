import TheoremA2.JointCovarianceSmooth
import TheoremA2.JointPriorApproximation
import TheoremA2.TiltedMGF

/-!
# Covariance and exponential moments of the actual joint reference law

This completes the analytic passage in A.33 from genuine smooth extensions
to the original compactly supported cosine prior. The only remaining input
in these lemmas is the separately named all-field spin covariance theorem.
-/

namespace TheoremA2.JointReference

open MeasureTheory ProbabilityTheory Filter
open TheoremA2.JointMarginal TheoremA2.ConvexSupport TheoremA2.PrincipalInverse
open scoped BigOperators Topology
noncomputable section

theorem prior_curvature_gt {lam : ℝ} (hlam : 0 < lam) :
    1 / (2 * lam) < BrascampLieb.curvatureConstant lam := by
  have hl0 : lam ≠ 0 := ne_of_gt hlam
  have he : BrascampLieb.curvatureConstant lam =
      1 / (2 * lam) + 1 / (4 * lam ^ 2) := by
    unfold BrascampLieb.curvatureConstant
    field_simp
    ring
  rw [he]
  have hp : (0 : ℝ) < 1 / (4 * lam ^ 2) := by positivity
  linarith

theorem prior_kappa_eq {lam : ℝ} (hlam : 0 < lam) :
    2 * lam - 1 / BrascampLieb.curvatureConstant lam = 2 * lam / (2 * lam + 1) := by
  have h1 : 2 * lam + 1 ≠ 0 := by positivity
  have h2 : lam ≠ 0 := ne_of_gt hlam
  unfold BrascampLieb.curvatureConstant
  field_simp
  ring

theorem prior_kappa_nonneg {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ 2 * lam - 1 / BrascampLieb.curvatureConstant lam := by
  rw [prior_kappa_eq hlam]
  positivity

theorem prior_kappa_lower {lam : ℝ} (hlam : 2 ≤ lam) :
    3 / 4 ≤ 2 * lam - 1 / BrascampLieb.curvatureConstant lam := by
  rw [prior_kappa_eq (by linarith : 0 < lam)]
  apply (le_div_iff₀ (by linarith : 0 < 2 * lam + 1)).2
  linarith

/-- The covariance bound holds for every external field under the literal
exponential tilt of the joint reference probability measure. -/
theorem actual_joint_tilted_variance {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) {lam c : ℝ}
    (hlam : 0 < lam) (hc : 0 < c) (hspin : SpinCovarianceBound B lam c)
    (h u : Fin r → ℝ) (k v : Fin s → ℝ) :
    Var[linear u v; (law B lam).tilted (linear h k)] ≤
      quadratic (JointPrecision.precision B lam c (BrascampLieb.curvatureConstant lam))⁻¹
        (Sum.elim u v) := by
  have hbound (n : ℕ) :
      approximateMoment B lam h k (fun ω => linear u v ω ^ 2) n -
        (approximateMoment B lam h k (linear u v) n) ^ 2 /
          approximateMoment B lam h k (fun _ => 1) n ≤
        quadratic (JointPrecision.precision B lam c (BrascampLieb.curvatureConstant lam))⁻¹
          (Sum.elim u v) * approximateMoment B lam h k (fun _ => 1) n := by
    rw [approximateMoment_one B hlam h k n]
    simpa only [approximateMoment, mul_comm] using smooth_joint_variance_bound
      (approximatePrior_contDiff hlam n) hlam hc (BrascampLieb.curvatureConstant_pos hlam)
      (prior_curvature_gt hlam) (prior_kappa_nonneg hlam)
      (approximatePrior_curvature hlam n) (approximatePrior_quadratic hlam n)
      B hspin h u k v
  have hz : 0 < priorScale r s lam * tiltedRawMass B lam h k :=
    mul_pos (priorScale_pos r s hlam) (tiltedRawMass_pos B hlam h k)
  have hh := BrascampLieb.normalized_variance_limit
    (approximateMoment B lam h k (fun _ => 1))
    (approximateMoment B lam h k (linear u v))
    (approximateMoment B lam h k (fun ω => linear u v ω ^ 2))
    (tendsto_approximate_mass B hlam h k)
    (tendsto_approximate_linear B hlam h u k v)
    (tendsto_approximate_linear_square B hlam h u k v) hz hbound
  rw [mul_div_mul_left _ _ (ne_of_gt (priorScale_pos r s hlam)),
    mul_div_mul_left _ _ (ne_of_gt (priorScale_pos r s hlam))] at hh
  rw [tilted_variance_eq_raw B hlam h u k v]
  exact hh

/-- The genuine joint linear MGF follows by integrating its tilted variance. -/
theorem actual_joint_linear_mgf {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) (hspin : SpinCovarianceBound B lam c)
    (u : Fin r → ℝ) (v : Fin s → ℝ) :
    (∫ ω, Real.exp (linear u v ω) ∂law B lam) ≤
      Real.exp (quadratic
        (JointPrecision.precision B lam c (BrascampLieb.curvatureConstant lam))⁻¹
        (Sum.elim u v) / 2) := by
  letI := isProbabilityMeasure_law B hlam
  apply exp_integral_le_of_tilted_variance (integrable_exp_mul_linear B hlam u v)
    (integral_linear_zero B hlam u v)
  intro a
  have h := actual_joint_tilted_variance B hlam hc hspin (a • u) u (a • v) v
  have he : linear (a • u) (a • v) = fun ω => a * linear u v ω :=
    funext (linear_smul a u v)
  rw [he] at h
  exact h

theorem actual_joint_mgf {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) (hspin : SpinCovarianceBound B lam c)
    (a : JointSpace r s) :
    (∫ ω, Real.exp (inner ℝ a (vector ω)) ∂law B lam) ≤
      Real.exp (quadratic
        (JointPrecision.precision B lam c (BrascampLieb.curvatureConstant lam))⁻¹ a / 2) := by
  have he : a = WithLp.toLp 2 (Sum.elim (fun i => a (Sum.inl i))
      (fun j => a (Sum.inr j))) := by
    ext i
    cases i <;> rfl
  rw [he]
  simpa only [inner_vector, PiLp.toLp_apply] using
    actual_joint_linear_mgf B hlam hc hspin (fun i => a (Sum.inl i)) (fun j => a (Sum.inr j))

end
end TheoremA2.JointReference
