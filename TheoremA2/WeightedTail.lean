import TheoremA2.PeriodicCells

/-!
# The actual weighted union tail in equations (72) and (76)

This is the finite Chernoff argument applied to the literal reference weights.
The coordinate projections may be arbitrarily dependent. The exponential
moment premise is explicitly the unnormalized weighted spin average, ready to
be supplied by the constructed joint reference law.
-/

namespace TheoremA2.WeightedTail

open TheoremA2.PeriodicCells
open Classical
open scoped BigOperators
noncomputable section

/-- A two-sided exponential majorant of the indicator of `|y| ≥ 1`. -/
theorem one_le_exponentialPair {t y : ℝ} (ht : 0 ≤ t) (hy : 1 ≤ |y|) :
    1 ≤ Real.exp (-t) * (Real.exp (t * y) + Real.exp (-t * y)) := by
  have hside : Real.exp (t * |y|) ≤ Real.exp (t * y) + Real.exp (-t * y) := by
    by_cases hy0 : 0 ≤ y
    · rw [abs_of_nonneg hy0]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_neg (lt_of_not_ge hy0)]
      have he : t * -y = -t * y := by ring
      rw [he]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc
    1 = Real.exp (-t) * Real.exp t := by rw [← Real.exp_add]; simp
    _ ≤ Real.exp (-t) * Real.exp (t * |y|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left hside (Real.exp_pos _).le

/-- A pointwise union bound with no independence assertion. -/
theorem bad_indicator_le {s : ℕ} {t : ℝ} (ht : 0 ≤ t) (y : Fin s → ℝ) :
    (if Small y then (0 : ℝ) else 1) ≤
      ∑ j, Real.exp (-t) * (Real.exp (t * y j) + Real.exp (-t * y j)) := by
  classical
  by_cases hy : Small y
  · simp only [hy, ite_true]
    exact Finset.sum_nonneg fun _ _ => by positivity
  · simp only [hy, ite_false]
    have hex : ∃ j, 1 < |y j| := by
      simpa only [PeriodicCells.Small, not_forall, not_le] using hy
    obtain ⟨j, hj⟩ := hex
    exact (one_le_exponentialPair ht hj.le).trans
      (Finset.single_le_sum
        (f := fun i : Fin s => Real.exp (-t) *
          (Real.exp (t * y i) + Real.exp (-t * y i)))
        (fun _ _ => by positivity) (Finset.mem_univ j))

/-- The scalar exponent at the actual Chernoff parameter `t = c / rho`. -/
theorem chernoff_exponent {c rho : ℝ} (hc : c ≠ 0) (hrho : rho ≠ 0) :
    -(c / rho) + (c / rho) ^ 2 * rho / (2 * c) = -c / (2 * rho) := by
  field_simp
  ring

/-- Equation (76) for the genuine reference-weighted average.
The moment bound is exactly the one-dimensional consequence (72) of the joint
MGF estimate; no event law, tail estimate, or independence premise is assumed. -/
theorem badMass_le_of_mgf {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam c rho : ℝ} (hlam : 0 < lam) (hc : 0 < c) (hrho : 0 < rho)
    (hmgf : ∀ (t : ℝ) (j : Fin s),
      average (fun σ : Spin r => referenceProduct lam (projection B σ) *
        Real.exp (t * projection B σ j)) ≤
      referenceNormalizer B (CosineReference.reference lam) *
        Real.exp (t ^ 2 * rho / (2 * c))) :
    badMass B lam ≤ referenceNormalizer B (CosineReference.reference lam) *
      (2 * (s : ℝ) * Real.exp (-c / (2 * rho))) := by
  classical
  let t := c / rho
  have ht : 0 ≤ t := (div_pos hc hrho).le
  have hpoint (σ : Spin r) :
      (if Small (projection B σ) then (0 : ℝ) else referenceProduct lam (projection B σ)) ≤
        ∑ j, Real.exp (-t) *
          (referenceProduct lam (projection B σ) * Real.exp (t * projection B σ j) +
            referenceProduct lam (projection B σ) * Real.exp (-t * projection B σ j)) := by
    have h := mul_le_mul_of_nonneg_left (bad_indicator_le ht (projection B σ))
      (referenceProduct_pos hlam (projection B σ)).le
    simpa only [mul_ite, mul_zero, mul_one, Finset.mul_sum, mul_add,
      mul_left_comm, mul_assoc] using h
  have hplus (j : Fin s) := hmgf t j
  have hminus (j : Fin s) := hmgf (-t) j
  simp only [neg_sq] at hminus
  calc
    badMass B lam ≤ average (fun σ : Spin r =>
        ∑ j, Real.exp (-t) *
          (referenceProduct lam (projection B σ) * Real.exp (t * projection B σ j) +
            referenceProduct lam (projection B σ) * Real.exp (-t * projection B σ j))) :=
      average_mono hpoint
    _ = ∑ j, Real.exp (-t) *
        (average (fun σ : Spin r => referenceProduct lam (projection B σ) *
          Real.exp (t * projection B σ j)) +
        average (fun σ : Spin r => referenceProduct lam (projection B σ) *
          Real.exp (-t * projection B σ j))) := by
      rw [average_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [average_const_mul, average_add]
    _ ≤ ∑ _j : Fin s, Real.exp (-t) *
        (referenceNormalizer B (CosineReference.reference lam) *
          Real.exp (t ^ 2 * rho / (2 * c)) +
        referenceNormalizer B (CosineReference.reference lam) *
          Real.exp (t ^ 2 * rho / (2 * c))) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (add_le_add (hplus j) (hminus j)) (Real.exp_pos _).le
    _ = referenceNormalizer B (CosineReference.reference lam) *
        (2 * (s : ℝ) * Real.exp (-t + t ^ 2 * rho / (2 * c))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.exp_add]
      ring
    _ = _ := by rw [show -t + t ^ 2 * rho / (2 * c) = -c / (2 * rho) from
      chernoff_exponent (ne_of_gt hc) (ne_of_gt hrho)]

end
end TheoremA2.WeightedTail
