import TheoremA2.GaussianShift
import TheoremA2.PrincipalInverse

/-!
# Actual Gaussian laws with matrix covariance

The law is the pushforward of the genuine product standard Gaussian by the
positive-semidefinite matrix square root. In particular singular covariance
matrices are permitted. Its one-dimensional projections are derived exactly.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def standardGaussian : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => gaussianReal 0 1

instance standardGaussian_probability : IsProbabilityMeasure (standardGaussian (ι := ι)) := by
  unfold standardGaussian
  infer_instance

theorem standardGaussian_fin (r : ℕ) :
    standardGaussian (ι := Fin r) = GaussianShift.gaussian r 1 := by
  simp [standardGaussian, GaussianShift.gaussian, GaussianShift.variance]

def projection (b : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, b i • ContinuousLinearMap.proj i

omit [DecidableEq ι] in
@[simp] theorem projection_apply (b x : ι → ℝ) : projection b x = b ⬝ᵥ x := by
  simp [projection, dotProduct]

@[simp] theorem projection_single (b : ι → ℝ) (i : ι) (x : ℝ) :
    projection b (Pi.single i x) = b i * x := by
  simp [projection, Pi.single_apply]

theorem measurable_dot (b : ι → ℝ) : Measurable (fun x : ι → ℝ => b ⬝ᵥ x) := by
  have heq : (fun x : ι → ℝ => b ⬝ᵥ x) = ⇑(projection b) := by
    funext x
    exact (projection_apply b x).symm
  rw [heq]
  exact (projection b).measurable

omit [DecidableEq ι] in
theorem measurable_mulVec (M : Matrix ι ι ℝ) : Measurable (fun x : ι → ℝ => M *ᵥ x) := by
  unfold Matrix.mulVec
  fun_prop

/-- Every projection of the product Gaussian has its exact scalar Gaussian law. -/
theorem standardGaussian_map_dot (b : ι → ℝ) :
    (standardGaussian (ι := ι)).map (fun x => b ⬝ᵥ x) =
      gaussianReal 0 ((normSq b).toNNReal) := by
  rw [show (fun x => b ⬝ᵥ x) = ⇑(projection b) by funext x; exact (projection_apply b x).symm]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_eq_charFunDual_smul, standardGaussian, charFunDual_pi]
  simp_rw [charFunDual_eq_charFun_map_one, gaussianReal_map_continuousLinearMap,
    charFun_gaussianReal]
  simp only [map_zero, Complex.ofReal_zero, mul_zero, zero_mul,
    mul_one, zero_sub, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.single_apply,
    projection_single, smul_eq_mul,
    Real.coe_toNNReal _ (sq_nonneg _)]
  rw [← Complex.exp_sum]
  congr 1
  have hn : 0 ≤ normSq b := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.coe_toNNReal (normSq b) hn]
  simp only [normSq, Complex.ofReal_sum, Complex.ofReal_pow,
    Complex.ofReal_mul, Finset.sum_div, Finset.sum_neg_distrib,
    Finset.sum_mul, Complex.ofReal_one, one_pow, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Gaussian with the displayed matrix covariance, built by an actual square-root map. -/
def covarianceGaussian (T : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (standardGaussian (ι := ι)).map (fun z => CFC.sqrt T *ᵥ z)

instance covarianceGaussian_probability (T : Matrix ι ι ℝ) :
    IsProbabilityMeasure (covarianceGaussian T) := by
  unfold covarianceGaussian
  infer_instance

theorem normSq_sqrt_transpose {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    normSq ((CFC.sqrt T)ᵀ *ᵥ b) = quadratic T b := by
  have hC : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  have hCt : (CFC.sqrt T)ᵀ = CFC.sqrt T := by simpa using hC.isHermitian.eq
  have hCsq : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self T hT.nonneg
  rw [hCt]
  change (∑ i, (CFC.sqrt T *ᵥ b) i ^ 2) = b ⬝ᵥ T *ᵥ b
  simp only [pow_two]
  change (CFC.sqrt T *ᵥ b) ⬝ᵥ CFC.sqrt T *ᵥ b = _
  rw [symmetric_bilinear hC.isHermitian, Matrix.mulVec_mulVec, hCsq]

/-- Exact scalar Gaussian projections of the actual matrix-covariance law. -/
theorem covarianceGaussian_map_dot {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    (covarianceGaussian T).map (fun x => b ⬝ᵥ x) =
      gaussianReal 0 ((quadratic T b).toNNReal) := by
  unfold covarianceGaussian
  rw [Measure.map_map (measurable_dot b) (measurable_mulVec (CFC.sqrt T))]
  have hid : (fun x : ι → ℝ => b ⬝ᵥ (CFC.sqrt T *ᵥ x)) =
      (fun x => ((CFC.sqrt T)ᵀ *ᵥ b) ⬝ᵥ x) := by
    funext x
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  change (standardGaussian (ι := ι)).map (fun x => b ⬝ᵥ (CFC.sqrt T *ᵥ x)) = _
  rw [hid, standardGaussian_map_dot, normSq_sqrt_transpose hT]

theorem integrable_exp_dot {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    Integrable (fun x => Real.exp (b ⬝ᵥ x)) (covarianceGaussian T) := by
  have hi : Integrable Real.exp (gaussianReal 0 ((quadratic T b).toNNReal)) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := 0)
      (v := (quadratic T b).toNNReal) 1)
  rw [← covarianceGaussian_map_dot hT b] at hi
  exact hi.comp_measurable (measurable_dot b)

theorem integral_exp_dot {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    (∫ x, Real.exp (b ⬝ᵥ x) ∂covarianceGaussian T) = Real.exp (quadratic T b / 2) := by
  have hh := mgf_gaussianReal ⟨(measurable_dot b).aemeasurable, covarianceGaussian_map_dot hT b⟩ 1
  simpa only [mgf, one_mul, mul_one, zero_mul, zero_add, one_pow,
    Real.coe_toNNReal _ (quadratic_nonneg hT b)] using hh

theorem integral_fourier_dot {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    (∫ x, Complex.exp (Complex.I * (b ⬝ᵥ x : ℝ)) ∂covarianceGaussian T) =
      Complex.exp (-(quadratic T b : ℂ) / 2) := by
  have hh := complexMGF_gaussianReal ⟨(measurable_dot b).aemeasurable, covarianceGaussian_map_dot hT b⟩ Complex.I
  simpa only [complexMGF, Complex.ofReal_zero, mul_zero, zero_add, Complex.I_sq,
    mul_neg, mul_one, Real.coe_toNNReal _ (quadratic_nonneg hT b)] using hh

theorem integrable_dot {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    Integrable (fun x => b ⬝ᵥ x) (covarianceGaussian T) := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 ((quadratic T b).toNNReal)) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)
  rw [← covarianceGaussian_map_dot hT b] at hi
  exact hi.comp_measurable (measurable_dot b)

theorem integral_dot {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    (∫ x, b ⬝ᵥ x ∂covarianceGaussian T) = 0 := by
  rw [← integral_map (measurable_dot b).aemeasurable (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ => x) ((covarianceGaussian T).map (fun x => b ⬝ᵥ x))),
    covarianceGaussian_map_dot hT b]
  exact integral_id_gaussianReal

theorem integrable_dot_sq {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    Integrable (fun x => (b ⬝ᵥ x) ^ 2) (covarianceGaussian T) := by
  have hi : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 ((quadratic T b).toNNReal)) :=
    (memLp_id_gaussianReal 2).integrable_sq
  rw [← covarianceGaussian_map_dot hT b] at hi
  exact hi.comp_measurable (measurable_dot b)

/-- The actual second moment of every projection is the declared covariance form. -/
theorem integral_dot_sq {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    (∫ x, (b ⬝ᵥ x) ^ 2 ∂covarianceGaussian T) = quadratic T b := by
  rw [← integral_map (measurable_dot b).aemeasurable (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ => x ^ 2) ((covarianceGaussian T).map (fun x => b ⬝ᵥ x))),
    covarianceGaussian_map_dot hT b]
  have hh := variance_fun_id_gaussianReal (μ := 0) (v := (quadratic T b).toNNReal)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hh
  simpa only [integral_id_gaussianReal, sub_zero,
    Real.coe_toNNReal _ (quadratic_nonneg hT b)] using hh

end

end TheoremA2.GaussianCovariance
