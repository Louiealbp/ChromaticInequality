import TheoremA2.Imports
import TheoremA2.Basic

/-!
# Exact second moments of the independent signs

This module proves, by finite sums and sign-flipping bijections, that
`E[(σᵀ S τ)^2] = ∑ i j, (S i j)^2`. In particular the second moment is
`k^2` for every `k` by `k` sign matrix. This is a preliminary calculation,
not the large-dimension positivity estimate of Theorem A.2.
-/

namespace TheoremA2

open scoped BigOperators

/-- Flip one coordinate of a spin vector. -/
def flipAt {k : ℕ} (i : Fin k) (σ : Spin k) : Spin k :=
  fun j => if j = i then !(σ j) else σ j

theorem flipAt_involutive {k : ℕ} (i : Fin k) : Function.Involutive (flipAt i) := by
  intro σ
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

/-- Pairwise orthogonality of the independent, uniformly distributed signs. -/
theorem average_sign_mul {k : ℕ} (i j : Fin k) :
    average (fun σ : Spin k => sign (σ i) * sign (σ j)) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp
  · let e : Spin k ≃ Spin k :=
      { toFun := flipAt i
        invFun := flipAt i
        left_inv := flipAt_involutive i
        right_inv := flipAt_involutive i }
    have hsum :
        (∑ σ : Spin k, sign (σ i) * sign (σ j)) =
          ∑ σ : Spin k, -(sign (σ i) * sign (σ j)) := by
      apply Fintype.sum_equiv e
      intro σ
      change sign (σ i) * sign (σ j) =
        -(sign (flipAt i σ i) * sign (flipAt i σ j))
      simp [flipAt, Ne.symm hij]
    have hzero : (∑ σ : Spin k, sign (σ i) * sign (σ j)) = 0 := by
      rw [Finset.sum_neg_distrib] at hsum
      linarith
    simp [average, hzero, hij]

/-- The exact second moment of a real linear combination of uniform signs. -/
theorem average_linear_sq {k : ℕ} (x : Fin k → ℝ) :
    average (fun σ : Spin k => (∑ i, x i * sign (σ i)) ^ 2) = ∑ i, x i ^ 2 := by
  classical
  have hexpand (σ : Spin k) :
      (∑ i, x i * sign (σ i)) ^ 2 =
        ∑ i, ∑ j, (x i * x j) * (sign (σ i) * sign (σ j)) := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexpand, average_sum, average_const_mul, average_sign_mul]
  simp [mul_ite, pow_two]

/-- Reorder the bilinear sum by columns; this is `σᵀ S τ`. -/
theorem bilinear_eq_columns {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (σ τ : Spin k) :
    bilinear S σ τ = ∑ j, (∑ i, S i j * sign (σ i)) * sign (τ j) := by
  unfold bilinear
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Orthogonality gives the Frobenius norm squared for every real matrix. -/
theorem average_bilinear_sq {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) :
    average (fun σ : Spin k => average (fun τ : Spin k => (bilinear S σ τ) ^ 2)) =
      ∑ i, ∑ j, S i j ^ 2 := by
  simp_rw [bilinear_eq_columns, average_linear_sq, average_sum, average_linear_sq]
  exact Finset.sum_comm

/-- The exact second moment for an arbitrary sign matrix is `k²`. -/
theorem average_bilinear_sq_sign {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) :
    average (fun σ : Spin k => average (fun τ : Spin k => (bilinear S σ τ) ^ 2)) =
      (k : ℝ) ^ 2 := by
  have hsquare (i j : Fin k) : S i j ^ 2 = 1 := by
    rcases hS i j with h | h <;> rw [h] <;> norm_num
  rw [average_bilinear_sq]
  simp [hsquare, pow_two]

/-- The scaled second moment, with the scalar independent of both averages. -/
theorem average_scaled_bilinear_sq_sign {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) (t : ℝ) :
    average (fun σ : Spin k => average (fun τ : Spin k => (t * bilinear S σ τ) ^ 2)) =
      t ^ 2 * (k : ℝ) ^ 2 := by
  simp_rw [mul_pow, average_const_mul]
  rw [average_bilinear_sq_sign S hS]

end TheoremA2
