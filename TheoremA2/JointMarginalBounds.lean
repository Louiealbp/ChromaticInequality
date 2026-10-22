import TheoremA2.JointMarginalDifferential

/-!
# Explicit moment bounds for the joint finite/continuous law

These elementary bounds provide concrete dominating functions for all first
and second moments. They do not assume integrability or convergence of the
actual Gibbs observables.
-/

namespace TheoremA2.JointMarginal

open TheoremA2.JointReference TheoremA2.PeriodicCells
open TheoremA2.ConvexSupport TheoremA2.PrincipalInverse TheoremA2.SpinCovariance
open scoped BigOperators Matrix
noncomputable section

def spinBound {r : ℕ} (u : Fin r → ℝ) : ℝ := ∑ i, |u i|

theorem spinBound_nonneg {r : ℕ} (u : Fin r → ℝ) : 0 ≤ spinBound u :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_spin_linear_le {r : ℕ} (u : Fin r → ℝ) (σ : Spin r) :
    |u ⬝ᵥ spinVector σ| ≤ spinBound u := by
  calc
    _ ≤ ∑ i, |u i * sign (σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_sign, mul_one, spinBound]

theorem abs_spin_expectation_le {r : ℕ} (p : FiniteProbability (Spin r)) (u : Fin r → ℝ) :
    |p.expectation (fun σ => u ⬝ᵥ spinVector σ)| ≤ spinBound u := by
  apply abs_le.2
  constructor
  · rw [← expectation_const p (-spinBound u)]
    exact expectation_mono p (fun σ => (abs_le.1 (abs_spin_linear_le u σ)).1)
  · rw [← expectation_const p (spinBound u)]
    exact expectation_mono p (fun σ => (abs_le.1 (abs_spin_linear_le u σ)).2)

theorem abs_conditionalLinearMean_le {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h u : Fin r → ℝ)
    (v : Fin s → ℝ) (t : Auxiliary s) :
    |conditionalLinearMean B lam h u v t| ≤ spinBound u + ‖fieldLinear v‖ * ‖t‖ := by
  unfold conditionalLinearMean
  apply (abs_add_le _ _).trans
  exact add_le_add (abs_spin_expectation_le _ u) (by
    simpa only [Real.norm_eq_abs] using (fieldLinear v).le_opNorm t)

def momentBound {r s : ℕ} (u : Fin r → ℝ) (v : Fin s → ℝ) : ℝ :=
  2 * (spinBound u ^ 2 + ‖fieldLinear v‖ ^ 2) + spinBound u + ‖fieldLinear v‖ + 1

theorem momentBound_pos {r s : ℕ} (u : Fin r → ℝ) (v : Fin s → ℝ) :
    0 < momentBound u v := by
  unfold momentBound
  have hu := spinBound_nonneg u
  positivity

theorem scalar_moment_bound {A D x y : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hy : 0 ≤ y) (hx : |x| ≤ A + D * y) :
    |x| ≤ (2 * (A ^ 2 + D ^ 2) + A + D + 1) * (1 + y ^ 2) ∧
    x ^ 2 ≤ (2 * (A ^ 2 + D ^ 2) + A + D + 1) * (1 + y ^ 2) := by
  have hy' : y ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hC : 0 ≤ 2 * (A ^ 2 + D ^ 2) := by positivity
  have hnorm : x ^ 2 ≤ (A + D * y) ^ 2 := by
    nlinarith [sq_abs x, abs_nonneg x, mul_nonneg
      (sub_nonneg.2 hx) (add_nonneg (abs_nonneg x) (add_nonneg hA (mul_nonneg hD hy)))]
  have hcross : (A + D * y) ^ 2 ≤ 2 * (A ^ 2 + D ^ 2 * y ^ 2) := by
    nlinarith [sq_nonneg (A - D * y)]
  constructor
  · calc
      |x| ≤ A + D * y := hx
      _ ≤ (A + D) * (1 + y ^ 2) := by nlinarith [mul_nonneg hA (sq_nonneg y)]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · calc
      x ^ 2 ≤ 2 * (A ^ 2 + D ^ 2 * y ^ 2) := hnorm.trans hcross
      _ ≤ 2 * (A ^ 2 + D ^ 2) * (1 + y ^ 2) := by
        nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg y), sq_nonneg D]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem conditionalLinearMean_sq_bound {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h u : Fin r → ℝ)
    (v : Fin s → ℝ) (t : Auxiliary s) :
    conditionalLinearMean B lam h u v t ^ 2 ≤ momentBound u v * (1 + ‖t‖ ^ 2) :=
  (scalar_moment_bound (spinBound_nonneg u) (norm_nonneg _) (norm_nonneg _)
    (abs_conditionalLinearMean_le B lam h u v t)).2

theorem conditionalLinearMean_abs_bound {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h u : Fin r → ℝ)
    (v : Fin s → ℝ) (t : Auxiliary s) :
    |conditionalLinearMean B lam h u v t| ≤ momentBound u v * (1 + ‖t‖ ^ 2) :=
  (scalar_moment_bound (spinBound_nonneg u) (norm_nonneg _) (norm_nonneg _)
    (abs_conditionalLinearMean_le B lam h u v t)).1

theorem abs_linear_le {r s : ℕ} (u : Fin r → ℝ) (v : Fin s → ℝ)
    (σ : Spin r) (t : Auxiliary s) :
    |linear u v (σ, t)| ≤ spinBound u + ‖fieldLinear v‖ * ‖t‖ := by
  rw [show linear u v (σ, t) = u ⬝ᵥ spinVector σ + fieldLinear v t by
    rw [fieldLinear_apply]; rfl]
  exact (abs_add_le _ _).trans (add_le_add (abs_spin_linear_le u σ) (by
    simpa only [Real.norm_eq_abs] using (fieldLinear v).le_opNorm t))

theorem linear_first_second_bounds {r s : ℕ} (u : Fin r → ℝ) (v : Fin s → ℝ)
    (σ : Spin r) (t : Auxiliary s) :
    |linear u v (σ, t)| ≤ momentBound u v * (1 + ‖t‖ ^ 2) ∧
      linear u v (σ, t) ^ 2 ≤ momentBound u v * (1 + ‖t‖ ^ 2) :=
  scalar_moment_bound (spinBound_nonneg u) (norm_nonneg _) (norm_nonneg _)
    (abs_linear_le u v σ t)

theorem euclidean_norm_sq {s : ℕ} (t : Auxiliary s) :
    ‖t‖ ^ 2 = ∑ j, t j ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

theorem projected_field_inner {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (k : Fin s → ℝ) (σ : Spin r) (t : Auxiliary s) :
    inner ℝ (WithLp.toLp 2 (projection B σ + k)) t =
      spinLinear B σ t + fieldLinear k t := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [WithLp.ofLp_toLp, Pi.star_apply, star_trivial, Pi.add_apply, dotProduct,
    spinLinear, fieldLinear_apply, mul_add, Finset.sum_add_distrib]
  simp only [mul_comm]

def jointWeight {r s : ℕ} (U : ℝ → ℝ) (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ) (σ : Spin r) (t : Auxiliary s) : ℝ :=
  Real.exp (spinConstant B lam h σ + spinLinear B σ t + fieldLinear k t - ∑ j, U (t j))

theorem jointWeight_pos {r s : ℕ} (U : ℝ → ℝ) (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ) (σ : Spin r) (t : Auxiliary s) :
    0 < jointWeight U B lam h k σ t := Real.exp_pos _

theorem jointWeight_gaussian_bound {r s : ℕ} {U : ℝ → ℝ} {H : ℝ}
    (hU : ∀ x, H / 2 * x ^ 2 ≤ U x)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ)
    (k : Fin s → ℝ) (σ : Spin r) (t : Auxiliary s) :
    jointWeight U B lam h k σ t ≤ Real.exp (spinConstant B lam h σ) *
      Real.exp (-(H / 2) * ‖t‖ ^ 2 + inner ℝ (WithLp.toLp 2 (projection B σ + k)) t) := by
  unfold jointWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [projected_field_inner]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) => hU (t j))
  rw [← Finset.mul_sum, ← euclidean_norm_sq] at hsum
  linarith

end
end TheoremA2.JointMarginal
