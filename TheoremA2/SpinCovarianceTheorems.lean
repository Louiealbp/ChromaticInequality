import TheoremA2.SpinCovarianceSpectral
import TheoremA2.GaussianEnvelopeComparison

/-!
# The actual small-diagonal spin precision theorems A.29 and A.31

The Gaussian comparison is applied to a positive diagonal shift of the actual
interaction matrix. The shift leaves the normalized spin law unchanged.
Every principal disagreement mask receives its own valid logarithmic cutoff.
No covariance, MGF, or analytic estimate is an assumption of the final theorems.
-/

namespace TheoremA2.SpinCovariance

open TheoremA2.ConvexSupport TheoremA2.PrincipalInverse
open scoped BigOperators Matrix
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Proposition A.29 for the actual zero-field second moment. A positive
admissible upper bound replaces the maximum diagonal only to avoid a separate
zero-matrix branch; the full small-diagonal hypothesis is unchanged. -/
theorem zeroFieldSecondMomentBound_small_diagonal [Nonempty ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hcut : ∀ i, A i i ≤ diagonalCutoff / dimensionLog (Fintype.card ι)) :
    ZeroFieldSecondMomentBound A precisionConstant := by
  let rho := diagonalCutoff / dimensionLog (Fintype.card ι)
  have hd : 0 < Fintype.card ι := Fintype.card_pos
  have hrho : 0 < rho := div_pos (by norm_num [diagonalCutoff]) (dimensionLog_pos hd)
  have hsmall : rho ≤ diagonalCutoff / dimensionLog (Fintype.card ι) := le_rfl
  have hdiag : ∀ i, A i i ≤ rho := hcut
  apply zero_field_of_precision_error hA hrho hsmall hdiag
  intro z
  have hT : (A + Matrix.diagonal (fun _ => rho)).PosDef :=
    Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.diagonal (fun _ => hrho))
  have hTdiag : ∀ i : ι,
      (A + Matrix.diagonal (fun _ : ι => rho) : Matrix ι ι ℝ) i i ≤ 2 * rho := by
    intro i
    simp only [Matrix.add_apply, Matrix.diagonal_apply_eq]
    linarith [hdiag i]
  have hdecoder : 2 * (2 * rho) / decoderBeta ≤ 1 / 1000000 := by
    convert all_decoder_cutoffs hd hrho hsmall using 1 <;> ring
  exact GaussianCovariance.zero_field_covariance_bound hT (by positivity) hTdiag
    hdecoder (zeroFieldAlpha_lt_one hd hrho hsmall) z

/-- The zero-field matrix precision bound, including the empty coordinate type. -/
theorem zero_field_covariance_small_diagonal
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hcut : ∀ i, A i i ≤ diagonalCutoff / dimensionLog (Fintype.card ι)) :
    ((A + Matrix.diagonal (fun _ => precisionConstant))⁻¹ -
      covariance (spinLaw A 0) spinVector).PosSemidef := by
  have hc : 0 < precisionConstant := by norm_num [precisionConstant]
  have hzero : ZeroFieldSecondMomentBound A precisionConstant := by
    cases isEmpty_or_nonempty ι with
    | inl he =>
        letI := he
        exact zeroFieldSecondMomentBound_empty _ _
    | inr hn =>
        letI := hn
        exact zeroFieldSecondMomentBound_small_diagonal hA hcut
  have hp : (A + Matrix.diagonal (fun _ => precisionConstant)).PosDef :=
    Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.diagonal (fun _ => hc))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hp.inv.isHermitian.sub (covariance_isHermitian _ _))
  intro z
  change 0 ≤ quadratic
    ((A + Matrix.diagonal (fun _ => precisionConstant))⁻¹ - covariance (spinLaw A 0) spinVector) z
  rw [quadratic_sub, zero_field_quadratic_covariance]
  exact sub_nonneg.mpr (hzero z)

/-- Proposition A.31: the full actual covariance estimate at every real field. -/
theorem all_field_covariance_small_diagonal
    {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    (hcut : ∀ i, 2 * N i i ≤ diagonalCutoff / dimensionLog (Fintype.card ι))
    (h : ι → ℝ) :
    ((N + Matrix.diagonal (fun _ => precisionConstant))⁻¹ -
      covariance (spinLaw N h) spinVector).PosSemidef := by
  apply all_field_covariance_of_nonempty_principal_zero_field hN
    (by norm_num [precisionConstant])
  intro mask hmask
  letI := hmask
  exact zeroFieldSecondMomentBound_small_diagonal (doubledPrincipal_posSemidef hN mask)
    (doubledPrincipal_diagonal_cutoff hcut mask)

/-- The scalar form used in the joint spin–continuous Brascamp–Lieb argument. -/
theorem all_field_quadratic_small_diagonal
    {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    (hcut : ∀ i, 2 * N i i ≤ diagonalCutoff / dimensionLog (Fintype.card ι))
    (h z : ι → ℝ) :
    quadratic (covariance (spinLaw N h) spinVector) z ≤
      quadratic (N + Matrix.diagonal (fun _ => precisionConstant))⁻¹ z := by
  have hq := quadratic_nonneg (all_field_covariance_small_diagonal hN hcut h) z
  rw [quadratic_sub] at hq
  exact sub_nonneg.mp hq

end
end TheoremA2.SpinCovariance
