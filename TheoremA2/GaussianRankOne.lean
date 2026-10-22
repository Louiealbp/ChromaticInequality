import TheoremA2.GaussianEnvelopeEuclidean
import TheoremA2.GaussianEnvelopeBox
import TheoremA2.GaussianFourierQuadratic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The actual rank-one covariance tilt used in A.27

The covariance update, its inverse, determinant, diagonal bound, and Gaussian
density change are all proved from positive definiteness. In particular the
factor `sqrt 2` is derived from the real Jacobian normalizers.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem squared_bilinear_le {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (x y : ι → ℝ) :
    (x ⬝ᵥ (T *ᵥ y)) ^ 2 ≤ quadratic T x * quadratic T y := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    ((CFC.sqrt T)ᵀ *ᵥ x) ((CFC.sqrt T)ᵀ *ᵥ y)
  change (((CFC.sqrt T)ᵀ *ᵥ x) ⬝ᵥ ((CFC.sqrt T)ᵀ *ᵥ y)) ^ 2 ≤
    normSq ((CFC.sqrt T)ᵀ *ᵥ x) * normSq ((CFC.sqrt T)ᵀ *ᵥ y) at hh
  rw [dot_sqrt hT, normSq_sqrt_transpose hT, normSq_sqrt_transpose hT] at hh
  exact hh

theorem squared_coordinate_mulVec_le {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (v : ι → ℝ) (i : ι) :
    (T *ᵥ v) i ^ 2 ≤ T i i * quadratic T v := by
  simpa only [quadratic, single_dotProduct, one_mul, Matrix.mulVec_single,
    Pi.smul_apply, op_smul_eq_smul, smul_eq_mul, mul_one, Matrix.col, Matrix.transpose_apply]
    using squared_bilinear_le hT (Pi.single i 1) v

def rankOneCovariance (T : Matrix ι ι ℝ) (v : ι → ℝ) : Matrix ι ι ℝ :=
  T + (quadratic T v)⁻¹ • Matrix.vecMulVec (T *ᵥ v) (T *ᵥ v)

theorem rankOneCovariance_posDef {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v : ι → ℝ) : (rankOneCovariance T v).PosDef := by
  apply hT.add_posSemidef
  have ho : (Matrix.vecMulVec (T *ᵥ v) (T *ᵥ v)).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star (T *ᵥ v)
  exact ho.smul (inv_nonneg.mpr (quadratic_nonneg hT.posSemidef v))

theorem rankOneCovariance_diag_le {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (v : ι → ℝ) (hw : 0 < quadratic T v) (i : ι) :
    rankOneCovariance T v i i ≤ 2 * T i i := by
  have hc := squared_coordinate_mulVec_le hT v i
  have hc' : (quadratic T v)⁻¹ * ((T *ᵥ v) i) ^ 2 ≤ T i i := by
    rw [inv_mul_le_iff₀ hw]
    simpa only [mul_comm] using hc
  simp only [rankOneCovariance, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  nlinarith

theorem rankOneCovariance_inverse {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v : ι → ℝ) (hw : 0 < quadratic T v) :
    (rankOneCovariance T v)⁻¹ =
      T⁻¹ - (2 * quadratic T v)⁻¹ • Matrix.vecMulVec v v := by
  have hdet : IsUnit T.det := isUnit_iff_ne_zero.mpr (ne_of_gt hT.det_pos)
  have htinv : (T⁻¹)ᵀ = T⁻¹ := by simpa using hT.inv.isHermitian.eq
  have hinv : (T *ᵥ v) ᵥ* T⁻¹ = v := by
    rw [← Matrix.mulVec_transpose, htinv, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hleft : T * Matrix.vecMulVec v v = Matrix.vecMulVec (T *ᵥ v) v :=
    Matrix.mul_vecMulVec T v v
  have hright : Matrix.vecMulVec (T *ᵥ v) (T *ᵥ v) * T⁻¹ =
      Matrix.vecMulVec (T *ᵥ v) v := by
    rw [Matrix.vecMulVec_mul, hinv]
  have houter : Matrix.vecMulVec (T *ᵥ v) (T *ᵥ v) * Matrix.vecMulVec v v =
      quadratic T v • Matrix.vecMulVec (T *ᵥ v) v := by
    rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_comm (T *ᵥ v),
      ← quadratic, Matrix.vecMulVec_smul]
  apply Matrix.inv_eq_right_inv
  unfold rankOneCovariance
  simp only [add_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [Matrix.mul_nonsing_inv _ hdet, hleft, hright, houter]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hw]
  ring

theorem quadratic_rankOne_inverse {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v : ι → ℝ) (hw : 0 < quadratic T v) (x : ι → ℝ) :
    quadratic (rankOneCovariance T v)⁻¹ x =
      quadratic T⁻¹ x - (v ⬝ᵥ x) ^ 2 / (2 * quadratic T v) := by
  rw [rankOneCovariance_inverse hT v hw]
  simp only [quadratic, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    smul_eq_mul]
  rw [dotProduct_comm x v]
  ring

theorem det_one_add_vecMulVec (u v : ι → ℝ) :
    (1 + Matrix.vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  rw [Matrix.vecMulVec_eq Unit]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow u v

theorem rankOneCovariance_det {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v : ι → ℝ) (hw : 0 < quadratic T v) :
    (rankOneCovariance T v).det = 2 * T.det := by
  have hf : rankOneCovariance T v =
      T * (1 + Matrix.vecMulVec ((quadratic T v)⁻¹ • v) (T *ᵥ v)) := by
    rw [mul_add, mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_smul,
      Matrix.smul_vecMulVec]
    rfl
  rw [hf, Matrix.det_mul, det_one_add_vecMulVec, dotProduct_smul,
    dotProduct_comm (T *ᵥ v)]
  change T.det * (1 + (quadratic T v)⁻¹ * quadratic T v) = _
  rw [inv_mul_cancel₀ (ne_of_gt hw)]
  ring

theorem det_sqrt_sq {T : Matrix ι ι ℝ} (hT : T.PosSemidef) :
    (CFC.sqrt T).det ^ 2 = T.det := by
  rw [pow_two, ← Matrix.det_mul, CFC.sqrt_mul_sqrt_self T hT.nonneg]

theorem rankOneCovariance_det_sqrt {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v : ι → ℝ) (hw : 0 < quadratic T v) :
    (CFC.sqrt (rankOneCovariance T v)).det = Real.sqrt 2 * (CFC.sqrt T).det := by
  have hU := rankOneCovariance_posDef hT v
  apply (sq_eq_sq₀ (covariance_sqrt_posDef hU).det_pos.le
    (mul_nonneg (Real.sqrt_nonneg _) (covariance_sqrt_posDef hT).det_pos.le)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    det_sqrt_sq hU.posSemidef, det_sqrt_sq hT.posSemidef, rankOneCovariance_det hT v hw]

theorem rankOneCovariance_density_zero {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v : ι → ℝ) (hw : 0 < quadratic T v) :
    covarianceDensity T 0 = Real.sqrt 2 * covarianceDensity (rankOneCovariance T v) 0 := by
  have hU := rankOneCovariance_posDef hT v
  simp only [covarianceDensity, Matrix.mulVec_zero,
    abs_of_pos (covariance_sqrt_posDef hT).det_pos, abs_of_pos (covariance_sqrt_posDef hU).det_pos]
  rw [rankOneCovariance_det_sqrt hT v hw]
  field_simp [ne_of_gt (covariance_sqrt_posDef hT).det_pos, ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]

/-- The exact Gaussian density tilt, including its normalizing factor. -/
theorem rankOneCovariance_density_tilt {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v : ι → ℝ) (hw : 0 < quadratic T v) (x : ι → ℝ) :
    covarianceDensity T x * Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)) =
      Real.sqrt 2 * covarianceDensity (rankOneCovariance T v) x := by
  rw [covarianceDensity_eq_exp hT x,
    covarianceDensity_eq_exp (rankOneCovariance_posDef hT v) x,
    quadratic_rankOne_inverse hT v hw, rankOneCovariance_density_zero hT v hw]
  rw [mul_assoc, mul_assoc, ← Real.exp_add]
  congr 2
  congr 1
  field_simp
  ring

theorem integrable_rankOne_tilt {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v : ι → ℝ) (hw : 0 < quadratic T v) :
    Integrable (fun x => Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)))
      (covarianceGaussian T) := by
  rw [integrable_covarianceGaussian_iff hT]
  simp_rw [rankOneCovariance_density_tilt hT v hw]
  exact (integrable_covarianceDensity (rankOneCovariance_posDef hT v)).const_mul _

/-- The rank-one tilt identity for every actual integral. -/
theorem integral_rankOne_tilt {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v : ι → ℝ) (hw : 0 < quadratic T v) (f : (ι → ℝ) → ℝ) :
    (∫ x, Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)) * f x ∂covarianceGaussian T) =
      Real.sqrt 2 * ∫ x, f x ∂covarianceGaussian (rankOneCovariance T v) := by
  rw [integral_covarianceGaussian_eq hT,
    integral_covarianceGaussian_eq (rankOneCovariance_posDef hT v), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← mul_assoc, rankOneCovariance_density_tilt hT v hw, mul_assoc]

theorem setIntegral_rankOne_tilt {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v : ι → ℝ) (hw : 0 < quadratic T v) (s : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) :
    (∫ x in s, Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)) * f x ∂covarianceGaussian T) =
      Real.sqrt 2 * ∫ x in s, f x ∂covarianceGaussian (rankOneCovariance T v) := by
  rw [setIntegral_covarianceGaussian_eq hT,
    setIntegral_covarianceGaussian_eq (rankOneCovariance_posDef hT v), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← mul_assoc, rankOneCovariance_density_tilt hT v hw, mul_assoc]

end

end TheoremA2.GaussianCovariance
