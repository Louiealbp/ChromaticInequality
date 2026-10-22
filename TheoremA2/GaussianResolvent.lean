import TheoremA2.SpinCovarianceMoments

/-!
# The exact inverse-complement identity in Lemma A.28

The ordinary Woodbury identity is applied to the actual positive-definite
matrix and its scalar diagonal shift. No simultaneous diagonalization or
covariance comparison is assumed.
-/

namespace TheoremA2.GaussianCovariance

open TheoremA2.PrincipalInverse TheoremA2.SpinCovariance
open scoped Matrix
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_scalar_diagonal {L : ℝ} (hL : 0 < L) :
    (Matrix.diagonal (fun _ : ι => 1 / L))⁻¹ = Matrix.diagonal (fun _ => L) := by
  apply Matrix.inv_eq_left_inv
  simp [Matrix.diagonal_mul_diagonal, ne_of_gt hL]

/-- The exact matrix resolvent cancellation used after Fourier transfer. -/
theorem inverse_complement_identity {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {L : ℝ} (hL : 0 < L) :
    T⁻¹ - T⁻¹ * (T⁻¹ + Matrix.diagonal (fun _ => L))⁻¹ * T⁻¹ =
      (T + Matrix.diagonal (fun _ => 1 / L))⁻¹ := by
  have hC : (Matrix.diagonal (fun _ : ι => 1 / L)).PosDef :=
    Matrix.PosDef.diagonal (fun _ => one_div_pos.mpr hL)
  have hK : (T⁻¹ + Matrix.diagonal (fun _ => L)).PosDef :=
    hT.inv.add_posSemidef (Matrix.PosSemidef.diagonal (fun _ => hL.le))
  have hi : IsUnit ((Matrix.diagonal (fun _ : ι => 1 / L))⁻¹ +
      (1 : Matrix ι ι ℝ) * T⁻¹ * 1) := by
    rw [inverse_scalar_diagonal hL, Matrix.one_mul, Matrix.mul_one, add_comm]
    exact hK.isUnit
  have hw := Matrix.add_mul_mul_inv_eq_sub T (1 : Matrix ι ι ℝ)
    (Matrix.diagonal (fun _ => 1 / L)) (1 : Matrix ι ι ℝ) hT.isUnit hC.isUnit hi
  simp only [Matrix.one_mul, Matrix.mul_one, inverse_scalar_diagonal hL] at hw
  rw [add_comm (Matrix.diagonal (fun _ : ι => L)) T⁻¹] at hw
  exact hw.symm

theorem quadratic_inverse_vector {T : Matrix ι ι ℝ} (hT : T.PosDef) (z : ι → ℝ) :
    quadratic T (T⁻¹ *ᵥ z) = quadratic T⁻¹ z := by
  unfold quadratic
  rw [matrix_mul_inverse_vector hT, dotProduct_comm]

theorem quadratic_inverse_congruence {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (M : Matrix ι ι ℝ) (z : ι → ℝ) :
    quadratic (T⁻¹ * M * T⁻¹) z = quadratic M (T⁻¹ *ᵥ z) := by
  calc
    _ = z ⬝ᵥ (T⁻¹ *ᵥ (M *ᵥ (T⁻¹ *ᵥ z))) := by
      simp only [quadratic, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (M *ᵥ (T⁻¹ *ᵥ z)) ⬝ᵥ (T⁻¹ *ᵥ z) :=
      symmetric_bilinear hT.inv.isHermitian z (M *ᵥ (T⁻¹ *ᵥ z))
    _ = _ := dotProduct_comm _ _

/-- The literal quadratic identity requested by the A.28 covariance transfer. -/
theorem quadratic_inverse_complement {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {L : ℝ} (hL : 0 < L) (z : ι → ℝ) :
    quadratic T (T⁻¹ *ᵥ z) -
        quadratic (T⁻¹ + Matrix.diagonal (fun _ => L))⁻¹ (T⁻¹ *ᵥ z) =
      quadratic (T + Matrix.diagonal (fun _ => 1 / L))⁻¹ z := by
  rw [quadratic_inverse_vector hT,
    ← quadratic_inverse_congruence hT (T⁻¹ + Matrix.diagonal (fun _ => L))⁻¹,
    ← quadratic_sub, inverse_complement_identity hT hL]

end
end TheoremA2.GaussianCovariance
