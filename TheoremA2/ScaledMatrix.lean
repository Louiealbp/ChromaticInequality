import TheoremA2.Parameters
import TheoremA2.Normalizer

/-!
# Row, column, and Frobenius norms of the scaled sign matrix

This module verifies the exact matrix substitution `B = theta k * S` in
Section A.10.4, including both row and column norms. No symmetry of `S` is used.
-/

namespace TheoremA2

open scoped BigOperators

noncomputable def scaledMatrix {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => theta k * S i j

theorem scaledMatrix_entry_sq {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) (i j : Fin k) :
    scaledMatrix S i j ^ 2 = theta k ^ 2 := by
  rcases hS i j with h | h <;> simp [scaledMatrix, h]

theorem scaledMatrix_row_sq {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) (i : Fin k) :
    (∑ j, scaledMatrix S i j ^ 2) = rowVariance k := by
  simp only [scaledMatrix_entry_sq S hS]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact k_mul_theta_sq hk

theorem scaledMatrix_column_sq {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) (j : Fin k) :
    (∑ i, scaledMatrix S i j ^ 2) = rowVariance k := by
  simp only [scaledMatrix_entry_sq S hS]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact k_mul_theta_sq hk

theorem frobeniusSq_scaledMatrix {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) :
    frobeniusSq (scaledMatrix S) = (k : ℝ) * rowVariance k := by
  unfold frobeniusSq
  simp [scaledMatrix_row_sq hk S hS]

/-- The normalizer estimate in exactly the parameters required by A.10.4. -/
theorem gaussianSpinNormalizer_scaled_lower_bound {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) :
    Real.exp (-(64 * amplitude ^ 2 * (k : ℝ)) / dimensionLog k) ≤
      gaussianSpinNormalizer (scaledMatrix S) (referenceLambda k) := by
  have h := gaussianSpinNormalizer_lower_bound (scaledMatrix S) (referenceLambda k)
  rw [frobeniusSq_scaledMatrix hk S hS] at h
  have hid : -referenceLambda k * ((k : ℝ) * rowVariance k) =
      -(64 * amplitude ^ 2 * (k : ℝ)) / dimensionLog k := by
    calc
      _ = -(referenceLambda k * ((k : ℝ) * rowVariance k)) := by ring
      _ = _ := normalizer_exponent_eq hk
  rwa [hid] at h

end TheoremA2
