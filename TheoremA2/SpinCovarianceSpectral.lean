import TheoremA2.SpinCovarianceNumerics

set_option maxHeartbeats 800000

/-!
# Spectral absorption of the actual zero-field error

All shifted inverses below are the ordinary matrix inverse. We diagonalize the
original positive-semidefinite matrix once, prove the inverse formulas in that
same basis, and apply the uniform scalar inequality from Proposition A.29.
The diagonal shift of the actual finite Gibbs law is proved explicitly.
-/

namespace TheoremA2.SpinCovariance

open TheoremA2.ConvexSupport TheoremA2.PrincipalInverse
open scoped BigOperators Matrix
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugating a diagonal matrix by the fixed eigenbasis of `A`. -/
def spectralTransform {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (v : ι → ℝ) : Matrix ι ι ℝ :=
  (hA.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal v *
    star (hA.eigenvectorUnitary : Matrix ι ι ℝ)

theorem spectralTransform_eigenvalues {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    spectralTransform hA hA.eigenvalues = A := by
  simpa only [spectralTransform, Unitary.conjStarAlgAut_apply, Unitary.coe_star,
    Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hA.spectral_theorem.symm

theorem spectralTransform_const {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (a : ℝ) :
    spectralTransform hA (fun _ => a) = Matrix.diagonal (fun _ => a) := by
  have hd : Matrix.diagonal (fun _ : ι => a) = a • (1 : Matrix ι ι ℝ) :=
    (Matrix.smul_one_eq_diagonal a).symm
  unfold spectralTransform
  rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property]

theorem spectralTransform_add {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (v w : ι → ℝ) :
    spectralTransform hA (v + w) = spectralTransform hA v + spectralTransform hA w := by
  have hd : Matrix.diagonal (v + w) = Matrix.diagonal v + Matrix.diagonal w :=
    map_add (Matrix.diagonalAddMonoidHom ι ℝ) v w
  simp only [spectralTransform, hd, Matrix.mul_add, Matrix.add_mul]

theorem spectralTransform_sub {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (v w : ι → ℝ) :
    spectralTransform hA (v - w) = spectralTransform hA v - spectralTransform hA w := by
  have hd : Matrix.diagonal (v - w) = Matrix.diagonal v - Matrix.diagonal w :=
    map_sub (Matrix.diagonalAddMonoidHom ι ℝ) v w
  simp only [spectralTransform, hd, Matrix.mul_sub, Matrix.sub_mul]

theorem spectralTransform_smul {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (a : ℝ) (v : ι → ℝ) : spectralTransform hA (a • v) = a • spectralTransform hA v := by
  simp only [spectralTransform, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem spectralTransform_mul {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (v w : ι → ℝ) :
    spectralTransform hA v * spectralTransform hA w = spectralTransform hA (v * w) := by
  unfold spectralTransform
  calc
    _ = (hA.eigenvectorUnitary : Matrix ι ι ℝ) *
        (Matrix.diagonal v *
          (star (hA.eigenvectorUnitary : Matrix ι ι ℝ) * hA.eigenvectorUnitary) *
          Matrix.diagonal w) * star (hA.eigenvectorUnitary : Matrix ι ι ℝ) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [Unitary.coe_star_mul_self, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
      rfl

theorem spectralTransform_posSemidef {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) : (spectralTransform hA v).PosSemidef := by
  simpa only [spectralTransform, Matrix.star_eq_conjTranspose] using
    (Matrix.PosSemidef.diagonal hv).mul_mul_conjTranspose_same
      (hA.eigenvectorUnitary : Matrix ι ι ℝ)

/-- Each positive scalar shift is inverted in the very same eigenbasis. -/
theorem inverse_diagonal_shift_spectral {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (a : ℝ) (hne : ∀ i, hA.eigenvalues i + a ≠ 0) :
    (A + Matrix.diagonal (fun _ => a))⁻¹ =
      spectralTransform hA (fun i => 1 / (hA.eigenvalues i + a)) := by
  apply Matrix.inv_eq_left_inv
  have hshift : A + Matrix.diagonal (fun _ => a) =
      spectralTransform hA (hA.eigenvalues + fun _ => a) := by
    rw [spectralTransform_add, spectralTransform_eigenvalues, spectralTransform_const]
  rw [hshift, spectralTransform_mul]
  have hid : (fun i => 1 / (hA.eigenvalues i + a)) * (hA.eigenvalues + fun _ => a) =
      fun _ => (1 : ℝ) := by
    ext i
    simp only [Pi.mul_apply, Pi.add_apply]
    exact one_div_mul_cancel (hne i)
  rw [hid, spectralTransform_const]
  exact Matrix.diagonal_one

/-- No operator-norm smallness is assumed: the largest eigenvalue is bounded
by the full trace, which can be large in high dimension. -/
theorem eigenvalue_le_dimension_mul_rho {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {rho : ℝ} (hdiag : ∀ i, A i i ≤ rho) (i : ι) :
    hA.isHermitian.eigenvalues i ≤ (Fintype.card ι : ℝ) * rho := by
  have hsingle : hA.isHermitian.eigenvalues i ≤ ∑ j, hA.isHermitian.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have htrace : A.trace ≤ (Fintype.card ι : ℝ) * rho := by
    calc
      _ = ∑ j, A j j := rfl
      _ ≤ ∑ _j : ι, rho := Finset.sum_le_sum (fun j _ => hdiag j)
      _ = _ := by simp
  rw [hA.isHermitian.trace_eq_sum_eigenvalues] at htrace
  exact hsingle.trans htrace

/-- The exact matrix inequality absorbing both inverse terms of Lemma A.28. -/
theorem inverse_error_absorption [Nonempty ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {rho : ℝ} (hrho : 0 < rho)
    (hsmall : rho ≤ diagonalCutoff / dimensionLog (Fintype.card ι))
    (hdiag : ∀ i, A i i ≤ rho) :
    ((A + Matrix.diagonal (fun _ => precisionConstant))⁻¹ -
      ((A + Matrix.diagonal (fun _ => rho + 1 / CosineEnvelope.upperCurvature))⁻¹ +
        zeroFieldZeta (Fintype.card ι) (2 * rho) •
          (A + Matrix.diagonal (fun _ => rho))⁻¹)).PosSemidef := by
  have hd : 0 < Fintype.card ι := Fintype.card_pos
  have hc : 0 < precisionConstant := by norm_num [precisionConstant]
  have hL : 0 < 1 / CosineEnvelope.upperCurvature :=
    one_div_pos.mpr CosineEnvelope.upperCurvature_pos
  have he (i : ι) : 0 ≤ hA.isHermitian.eigenvalues i := hA.eigenvalues_nonneg i
  rw [inverse_diagonal_shift_spectral hA.isHermitian precisionConstant
      (fun i => ne_of_gt (add_pos_of_nonneg_of_pos (he i) hc)),
    inverse_diagonal_shift_spectral hA.isHermitian (rho + 1 / CosineEnvelope.upperCurvature)
      (fun i => ne_of_gt (add_pos_of_nonneg_of_pos (he i) (add_pos hrho hL))),
    inverse_diagonal_shift_spectral hA.isHermitian rho
      (fun i => ne_of_gt (add_pos_of_nonneg_of_pos (he i) hrho)),
    ← spectralTransform_smul, ← spectralTransform_add, ← spectralTransform_sub]
  apply spectralTransform_posSemidef
  intro i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hi := scalar_inverse_absorption hd hrho hsmall (he i)
    (eigenvalue_le_dimension_mul_rho hA hdiag i)
  simpa only [add_assoc, div_eq_mul_inv, one_mul] using sub_nonneg.mpr hi

omit [DecidableEq ι] in
/-- The Euclidean squared norm of every genuine sign vector is the dimension. -/
theorem spinVector_normSq (σ : SpinConfig ι) :
    normSq (spinVector σ) = (Fintype.card ι : ℝ) := by
  simp only [normSq, spinVector, sign_sq]
  simp

/-- A diagonal shift multiplies every unnormalized spin weight by the same constant. -/
theorem spinWeight_add_diagonal (A : Matrix ι ι ℝ) (h : ι → ℝ) (a : ℝ)
    (σ : SpinConfig ι) :
    spinWeight (A + Matrix.diagonal (fun _ => a)) h σ =
      Real.exp (-a * (Fintype.card ι : ℝ) / 2) * spinWeight A h σ := by
  unfold spinWeight
  rw [quadratic_add_diagonal, spinVector_normSq, ← Real.exp_add]
  congr 1
  ring

theorem spinPartition_add_diagonal (A : Matrix ι ι ℝ) (h : ι → ℝ) (a : ℝ) :
    spinPartition (A + Matrix.diagonal (fun _ => a)) h =
      Real.exp (-a * (Fintype.card ι : ℝ) / 2) * spinPartition A h := by
  simp only [spinPartition, spinWeight_add_diagonal, Finset.mul_sum]

/-- Diagonal shifts leave the actual normalized Gibbs probability law unchanged. -/
theorem spinLaw_add_diagonal (A : Matrix ι ι ℝ) (h : ι → ℝ) (a : ℝ) :
    spinLaw (A + Matrix.diagonal (fun _ => a)) h = spinLaw A h := by
  have hm : (spinLaw (A + Matrix.diagonal (fun _ => a)) h).mass = (spinLaw A h).mass := by
    funext σ
    change spinWeight (A + Matrix.diagonal (fun _ => a)) h σ /
      spinPartition (A + Matrix.diagonal (fun _ => a)) h = spinWeight A h σ / spinPartition A h
    rw [spinWeight_add_diagonal, spinPartition_add_diagonal]
    exact mul_div_mul_left _ _ (Real.exp_ne_zero _)
  have hext (p q : FiniteProbability (SpinConfig ι)) (hpq : p.mass = q.mass) : p = q := by
    cases p
    cases q
    cases hpq
    rfl
  exact hext _ _ hm

/-- The numerical and spectral conclusion of A.29 from the precise A.28
error estimate on the shifted, actual Gibbs law. The analytic input is
displayed explicitly and will be supplied by the preceding Gaussian argument. -/
theorem zero_field_of_precision_error [Nonempty ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {rho : ℝ} (hrho : 0 < rho)
    (hsmall : rho ≤ diagonalCutoff / dimensionLog (Fintype.card ι))
    (hdiag : ∀ i, A i i ≤ rho)
    (herror : ∀ z : ι → ℝ,
      quadratic (covariance (spinLaw (A + Matrix.diagonal (fun _ => rho)) 0) spinVector) z ≤
        quadratic ((A + Matrix.diagonal (fun _ => rho)) +
          Matrix.diagonal (fun _ => 1 / CosineEnvelope.upperCurvature))⁻¹ z +
        zeroFieldZeta (Fintype.card ι) (2 * rho) *
          quadratic (A + Matrix.diagonal (fun _ => rho))⁻¹ z) :
    ZeroFieldSecondMomentBound A precisionConstant := by
  intro z
  have hpsd := inverse_error_absorption hA hrho hsmall hdiag
  have hq := quadratic_nonneg hpsd z
  rw [quadratic_sub] at hq
  have hadd (M N : Matrix ι ι ℝ) : quadratic (M + N) z = quadratic M z + quadratic N z := by
    simp only [quadratic, Matrix.add_mulVec, dotProduct_add]
  rw [hadd, quadratic_smul] at hq
  have hshift : (A + Matrix.diagonal (fun _ => rho)) +
      Matrix.diagonal (fun _ => 1 / CosineEnvelope.upperCurvature) =
      A + Matrix.diagonal (fun _ => rho + 1 / CosineEnvelope.upperCurvature) := by
    rw [add_assoc, Matrix.diagonal_add]
  have he := herror z
  rw [hshift, spinLaw_add_diagonal, zero_field_quadratic_covariance] at he
  linarith

/-- Reducing the dimension increases the allowed logarithmic diagonal cutoff. -/
theorem dimensionCutoff_antitone {m d : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    diagonalCutoff / dimensionLog d ≤ diagonalCutoff / dimensionLog m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmdR : (m : ℝ) ≤ d := by exact_mod_cast hmd
  have hlog : dimensionLog m ≤ dimensionLog d := by
    unfold dimensionLog
    exact Real.log_le_log (by positivity) (by linarith)
  exact div_le_div_of_nonneg_left (by norm_num [diagonalCutoff])
    (dimensionLog_pos hm) hlog

omit [DecidableEq ι] in
theorem doubledPrincipal_posSemidef {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    (mask : ι → Bool) : (doubledPrincipal N mask).PosSemidef :=
  (hN.submatrix Subtype.val).smul (by norm_num : (0 : ℝ) ≤ 2)

omit [DecidableEq ι] in
/-- Every nonempty disagreement mask inherits exactly the A.29 diagonal
cutoff, including the doubling of its interaction matrix. -/
theorem doubledPrincipal_diagonal_cutoff {N : Matrix ι ι ℝ}
    (hcut : ∀ i, 2 * N i i ≤ diagonalCutoff / dimensionLog (Fintype.card ι))
    (mask : ι → Bool) [Nonempty (Coordinates mask)] (i : Coordinates mask) :
    doubledPrincipal N mask i i ≤
      diagonalCutoff / dimensionLog (Fintype.card (Coordinates mask)) := by
  have hcard : Fintype.card (Coordinates mask) ≤ Fintype.card ι :=
    Fintype.card_subtype_le _
  have hc := dimensionCutoff_antitone (Fintype.card_pos (α := Coordinates mask)) hcard
  exact (hcut i.val).trans hc

end
end TheoremA2.SpinCovariance
