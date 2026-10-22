import TheoremA2.GaussianCovarianceBasic

/-!
# The actual Lebesgue density of a nondegenerate matrix Gaussian

All change-of-variable factors are derived from the matrix square-root map.
The density is expressed using the product standard normal density; it is not
postulated as a Gaussian law.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def standardDensity (x : ι → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

theorem standardDensity_pos (x : ι → ℝ) : 0 < standardDensity x :=
  Finset.prod_pos fun i _ => gaussianPDFReal_pos _ _ _ (by norm_num)

theorem measurable_standardDensity : Measurable (@standardDensity ι _) := by
  unfold standardDensity
  fun_prop

theorem integrable_standardDensity : Integrable (@standardDensity ι _) :=
  Integrable.fintype_prod fun _ => integrable_gaussianPDFReal _ _

theorem standardGaussian_eq_withDensity :
    standardGaussian (ι := ι) =
      volume.withDensity (fun x => ENNReal.ofReal (standardDensity x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply' _ _]
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_standardDensity.integrableOn
    (Filter.Eventually.of_forall fun x => (standardDensity_pos x).le)]
  have hi : (∫ x in Set.univ.pi s, standardDensity x) =
      ∏ i, ∫ x in s i, gaussianPDFReal 0 1 x := by
    change (∫ x, standardDensity x ∂(Measure.pi fun _ : ι => volume).restrict
      (Set.univ.pi s)) = _
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod _
  rw [hi]
  simp_rw [gaussianReal_apply_eq_integral _ (by norm_num : (1 : ℝ≥0) ≠ 0)]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun x =>
    gaussianPDFReal_nonneg _ _ _)

/-- Transport of a genuine density by a measurable equivalence. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator hs, lintegral_map_equiv,
    ← lintegral_indicator (e.measurable hs)]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s <;> simp [hx]

/-- The actual invertible linear change of variables and its inverse. -/
def matrixMeasurableEquiv (M : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    (ι → ℝ) ≃ᵐ (ι → ℝ) where
  toFun := fun x => M *ᵥ x
  invFun := fun x => M⁻¹ *ᵥ x
  left_inv x := by
    change M⁻¹ *ᵥ (M *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
  right_inv x := by
    change M *ᵥ (M⁻¹ *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  measurable_toFun := measurable_mulVec M
  measurable_invFun := measurable_mulVec M⁻¹

@[simp] theorem matrixMeasurableEquiv_apply (M : Matrix ι ι ℝ) (hM : IsUnit M.det)
    (x : ι → ℝ) : matrixMeasurableEquiv M hM x = M *ᵥ x := rfl

@[simp] theorem matrixMeasurableEquiv_symm_apply (M : Matrix ι ι ℝ) (hM : IsUnit M.det)
    (x : ι → ℝ) : (matrixMeasurableEquiv M hM).symm x = M⁻¹ *ᵥ x := rfl

theorem matrixMeasurableEquiv_map_volume (M : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    volume.map (matrixMeasurableEquiv M hM) =
      ENNReal.ofReal (|M.det|⁻¹) • volume := by
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hM.ne_zero
  simp only [abs_inv] at h
  exact h

/-- Exact density of the square-root pushforward Gaussian. -/
def covarianceDensity (T : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  |(CFC.sqrt T).det|⁻¹ * standardDensity ((CFC.sqrt T)⁻¹ *ᵥ x)

theorem measurable_covarianceDensity (T : Matrix ι ι ℝ) :
    Measurable (covarianceDensity T) := by
  unfold covarianceDensity
  exact measurable_const.mul (measurable_standardDensity.comp (measurable_mulVec _))

theorem covarianceDensity_nonneg (T : Matrix ι ι ℝ) (x : ι → ℝ) :
    0 ≤ covarianceDensity T x :=
  mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (standardDensity_pos _).le

theorem covariance_sqrt_posDef {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    (CFC.sqrt T).PosDef :=
  Matrix.IsStrictlyPositive.posDef (IsStrictlyPositive.sqrt T hT.isStrictlyPositive)

theorem covarianceDensity_pos {T : Matrix ι ι ℝ} (hT : T.PosDef) (x : ι → ℝ) :
    0 < covarianceDensity T x := by
  apply mul_pos _ (standardDensity_pos _)
  exact inv_pos.mpr (abs_pos.mpr (ne_of_gt (covariance_sqrt_posDef hT).det_pos))

/-- The actual covariance Gaussian equals the derived volume density. -/
theorem covarianceGaussian_eq_withDensity {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    covarianceGaussian T =
      volume.withDensity (fun x => ENNReal.ofReal (covarianceDensity T x)) := by
  let e := matrixMeasurableEquiv (CFC.sqrt T) (isUnit_iff_ne_zero.mpr (ne_of_gt (covariance_sqrt_posDef hT).det_pos))
  unfold covarianceGaussian
  rw [standardGaussian_eq_withDensity]
  change (volume.withDensity (fun x => ENNReal.ofReal (standardDensity x))).map e = _
  rw [map_withDensity_equiv, matrixMeasurableEquiv_map_volume,
    withDensity_smul_measure, ← withDensity_smul]
  · congr 1
    funext x
    rw [covarianceDensity, ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _))]
    rfl
  · exact measurable_standardDensity.ennreal_ofReal.comp e.symm.measurable

theorem integral_covarianceGaussian_eq {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (f : (ι → ℝ) → ℝ) :
    (∫ x, f x ∂covarianceGaussian T) = ∫ x, covarianceDensity T x * f x := by
  rw [covarianceGaussian_eq_withDensity hT,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_covarianceDensity T).ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (covarianceDensity_nonneg T _), smul_eq_mul]

theorem integrable_covarianceGaussian_iff {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (f : (ι → ℝ) → ℝ) :
    Integrable f (covarianceGaussian T) ↔
      Integrable (fun x => covarianceDensity T x * f x) := by
  rw [covarianceGaussian_eq_withDensity hT,
    integrable_withDensity_iff_integrable_smul'
      (measurable_covarianceDensity T).ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (covarianceDensity_nonneg T _), smul_eq_mul]

end

end TheoremA2.GaussianCovariance
