import TheoremA2.GaussianRankOne
import TheoremA2.GaussianTail

/-!
# Quadratic exponential moments from actual linear MGFs

A genuine auxiliary standard Gaussian and Fubini's theorem convert a linear
subgaussian bound into the precise `sqrt 2` quadratic-exponential bound. This
then proves that the actual central envelope normalizer decreases under the
rank-one covariance update used in A.27.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

theorem scalar_pdf_quarter_tilt (z : ℝ) :
    gaussianPDFReal 0 1 z * Real.exp (z ^ 2 / 4) =
      Real.sqrt 2 * gaussianPDFReal 0 2 z := by
  rw [TheoremA2.GaussianTail.pdf_one_tilt]
  calc
    _ = (Real.sqrt 2 * gaussianPDFReal 0 2 z) *
        (Real.exp (-(z ^ 2) / 4) * Real.exp (z ^ 2 / 4)) := by ring
    _ = _ := by
      rw [← Real.exp_add, show -(z ^ 2) / 4 + z ^ 2 / 4 = 0 by ring,
        Real.exp_zero, mul_one]

theorem integrable_standard_exp_quarter_sq :
    Integrable (fun z : ℝ => Real.exp (z ^ 2 / 4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0), gaussianPDF_def,
    integrable_withDensity_iff_integrable_smul'
      ((measurable_gaussianPDFReal 0 1).ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _), smul_eq_mul,
    scalar_pdf_quarter_tilt]
  exact (integrable_gaussianPDFReal 0 2).const_mul _

theorem integral_standard_exp_quarter_sq :
    (∫ z : ℝ, Real.exp (z ^ 2 / 4) ∂gaussianReal 0 1) = Real.sqrt 2 := by
  rw [integral_gaussianReal_eq_integral_smul (f := fun z : ℝ => Real.exp (z ^ 2 / 4))
    (μ := 0) (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, scalar_pdf_quarter_tilt]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0 (by norm_num : (2 : ℝ≥0) ≠ 0), mul_one]

theorem scaled_gaussian_square {w : ℝ} (hw : 0 < w) (z : ℝ) :
    (z / Real.sqrt (2 * w)) ^ 2 * w / 2 = z ^ 2 / 4 := by
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * w)]
  field_simp
  ring

/-- Linear MGF control implies a genuine, integrable quadratic exponential
moment, proved with an actual auxiliary Gaussian. -/
theorem quadratic_exponential_of_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    {w : ℝ} (hw : 0 < w)
    (hint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * X x)) μ)
    (hmgf : ∀ t : ℝ, (∫ x, Real.exp (t * X x) ∂μ) ≤ Real.exp (t ^ 2 * w / 2)) :
    Integrable (fun x => Real.exp ((X x) ^ 2 / (4 * w))) μ ∧
      (∫ x, Real.exp ((X x) ^ 2 / (4 * w)) ∂μ) ≤ Real.sqrt 2 := by
  let F : ℝ × Ω → ℝ := fun p => Real.exp ((p.1 / Real.sqrt (2 * w)) * X p.2)
  have hm₁ : Measurable (fun p : ℝ × Ω => p.1 / Real.sqrt (2 * w)) :=
    measurable_fst.div_const _
  have hm₂ : Measurable (fun p : ℝ × Ω => X p.2) := hX.comp measurable_snd
  have hm : Measurable F :=
    (hm₁.mul hm₂).exp
  have hi (z : ℝ) : Integrable (fun x => F (z, x)) μ := by
    change Integrable (fun x => Real.exp ((z / Real.sqrt (2 * w)) * X x)) μ
    exact hint (z / Real.sqrt (2 * w))
  have hb (z : ℝ) : (∫ x, F (z, x) ∂μ) ≤ Real.exp (z ^ 2 / 4) := by
    change (∫ x, Real.exp ((z / Real.sqrt (2 * w)) * X x) ∂μ) ≤ _
    exact (hmgf (z / Real.sqrt (2 * w))).trans_eq
      (congrArg Real.exp (scaled_gaussian_square hw z))
  have hn (z : ℝ) : (∫ x, ‖F (z, x)‖ ∂μ) = ∫ x, F (z, x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    change ‖Real.exp ((z / Real.sqrt (2 * w)) * X x)‖ =
      Real.exp ((z / Real.sqrt (2 * w)) * X x)
    exact Real.norm_of_nonneg (Real.exp_pos ((z / Real.sqrt (2 * w)) * X x)).le
  have hmeas : AEStronglyMeasurable (fun z : ℝ => ∫ x, ‖F (z, x)‖ ∂μ)
      (gaussianReal 0 1) :=
    (hm.stronglyMeasurable.norm.integral_prod_right' (ν := μ)).aestronglyMeasurable
  have hout : Integrable (fun z => ∫ x, ‖F (z, x)‖ ∂μ) (gaussianReal 0 1) := by
    apply integrable_standard_exp_quarter_sq.mono' hmeas
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact (hn z).trans_le (hb z)
  have hprod : Integrable F ((gaussianReal 0 1).prod μ) :=
    (integrable_prod_iff (μ := gaussianReal 0 1) (ν := μ) hm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hi, hout⟩
  have hinner (x : Ω) :
      (∫ z : ℝ, F (z, x) ∂gaussianReal 0 1) = Real.exp ((X x) ^ 2 / (4 * w)) := by
    have hh := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1))
      (X x / Real.sqrt (2 * w))
    simp only [mgf, zero_mul, NNReal.coe_one, one_mul, zero_add] at hh
    calc
      _ = ∫ z : ℝ, Real.exp ((X x / Real.sqrt (2 * w)) * z) ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp [F]
        congr 1
        ring
      _ = Real.exp ((X x / Real.sqrt (2 * w)) ^ 2 / 2) := hh
      _ = _ := by
        congr 1
        rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * w)]
        ring
  have hquad : Integrable (fun x => Real.exp ((X x) ^ 2 / (4 * w))) μ := by
    exact hprod.integral_prod_right.congr (Filter.Eventually.of_forall hinner)
  refine ⟨hquad, ?_⟩
  calc
    _ = ∫ x, ∫ z : ℝ, F (z, x) ∂gaussianReal 0 1 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => (hinner x).symm))
    _ = ∫ z : ℝ, ∫ x, F (z, x) ∂μ ∂gaussianReal 0 1 :=
      (integral_integral_swap hprod).symm
    _ ≤ ∫ z : ℝ, Real.exp (z ^ 2 / 4) ∂gaussianReal 0 1 :=
      integral_mono hprod.integral_prod_left integrable_standard_exp_quarter_sq hb
    _ = _ := integral_standard_exp_quarter_sq

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem quadratic_smul_vector (T : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ) :
    quadratic T (t • v) = t ^ 2 * quadratic T v := by
  simp only [quadratic, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem boxEnvelopeNormalizer_le_global (T : Matrix ι ι ℝ) (b : ℝ) :
    boxEnvelopeNormalizer T b ≤ envelopeNormalizer T :=
  setIntegral_le_integral (integrable_envelopeWeight T)
    (Filter.Eventually.of_forall (fun x => (envelopeWeight_pos x).le))

/-- The normalizer comparison in A.27 is proved for the actual rank-one
updated covariance and the actual restricted envelope law. -/
theorem rankOne_boxNormalizer_le {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {b : ℝ} (hb : 0 < b)
    (hmgf : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw T b) ≤ Real.exp (quadratic T u / 2))
    (v : ι → ℝ) (hw : 0 < quadratic T v) :
    boxEnvelopeNormalizer (rankOneCovariance T v) b ≤ boxEnvelopeNormalizer T b := by
  letI := boxEnvelopeLaw_probability hT hb
  have hint (t : ℝ) : Integrable (fun x => Real.exp (t * (v ⬝ᵥ x))) (boxEnvelopeLaw T b) := by
    simpa only [smul_dotProduct, smul_eq_mul] using
      integrable_boxEnvelopeLaw_exp_dot hT.posSemidef b (t • v)
  have hmgf' (t : ℝ) :
      (∫ x, Real.exp (t * (v ⬝ᵥ x)) ∂boxEnvelopeLaw T b) ≤
        Real.exp (t ^ 2 * quadratic T v / 2) := by
    simpa only [smul_dotProduct, smul_eq_mul, quadratic_smul_vector] using hmgf (t • v)
  have hq := quadratic_exponential_of_mgf (boxEnvelopeLaw T b)
    (fun x => v ⬝ᵥ x) (measurable_dot v) hw hint hmgf'
  have he : boxEnvelopeNormalizer T b *
      (∫ x, Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)) ∂boxEnvelopeLaw T b) =
        Real.sqrt 2 * boxEnvelopeNormalizer (rankOneCovariance T v) b := by
    rw [integral_boxEnvelopeLaw]
    rw [mul_div_cancel₀ _ (ne_of_gt (boxEnvelopeNormalizer_pos hT hb))]
    calc
      _ = ∫ x in coordinateBox b,
          Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)) * envelopeWeight x
          ∂covarianceGaussian T := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
      _ = _ := setIntegral_rankOne_tilt hT v hw (coordinateBox b) envelopeWeight
  have hbnd := mul_le_mul_of_nonneg_left hq.2 (boxEnvelopeNormalizer_pos hT hb).le
  rw [he, mul_comm (boxEnvelopeNormalizer T b)] at hbnd
  exact (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mp hbnd

end

end TheoremA2.GaussianCovariance
