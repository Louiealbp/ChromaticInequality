import TheoremA2.GaussianEnvelopeLaw

/-!
# Actual central-box envelope laws and Gaussian cell identities

The central reference is a genuine normalized restriction of the Gaussian.
Its mass is proved positive, and translated-cell integrals are identified
with its literal exponential moments.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateBox (b : ℝ) : Set (ι → ℝ) := {x | ∀ i, |x i| ≤ b}

theorem coordinateBox_eq_pi (b : ℝ) :
    coordinateBox (ι := ι) b = Set.univ.pi (fun _ => Icc (-b) b) := by
  ext x
  simp only [coordinateBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc, abs_le]

theorem coordinateBox_isClosed (b : ℝ) : IsClosed (coordinateBox (ι := ι) b) := by
  simpa only [coordinateBox, Set.setOf_forall] using
    isClosed_iInter (fun i : ι => isClosed_le ((continuous_apply i).abs) continuous_const)

theorem coordinateBox_measurable (b : ℝ) : MeasurableSet (coordinateBox (ι := ι) b) :=
  (coordinateBox_isClosed b).measurableSet

theorem coordinateBox_neg_iff (b : ℝ) (x : ι → ℝ) :
    -x ∈ coordinateBox b ↔ x ∈ coordinateBox b := by
  simp only [coordinateBox, Set.mem_setOf_eq, Pi.neg_apply, abs_neg]

theorem coordinateBox_volume_pos {b : ℝ} (hb : 0 < b) :
    0 < (volume : Measure (ι → ℝ)) (coordinateBox b) := by
  rw [coordinateBox_eq_pi]
  change 0 < (Measure.pi (fun _ : ι => volume)) (Set.univ.pi (fun _ => Icc (-b) b))
  rw [Measure.pi_pi]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [Real.volume_Icc]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))

theorem volume_absolutelyContinuous_covarianceGaussian {T : Matrix ι ι ℝ}
    (hT : T.PosDef) : (volume : Measure (ι → ℝ)) ≪ covarianceGaussian T := by
  rw [covarianceGaussian_eq_withDensity hT]
  apply withDensity_absolutelyContinuous' (measurable_covarianceDensity T).ennreal_ofReal.aemeasurable
  exact Filter.Eventually.of_forall (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (covarianceDensity_pos hT x)))

theorem coordinateBox_gaussian_pos {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {b : ℝ} (hb : 0 < b) : 0 < covarianceGaussian T (coordinateBox b) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  exact (ne_of_gt (coordinateBox_volume_pos (ι := ι) hb))
    (volume_absolutelyContinuous_covarianceGaussian hT hz)

def boxEnvelopeNormalizer (T : Matrix ι ι ℝ) (b : ℝ) : ℝ :=
  ∫ x in coordinateBox b, envelopeWeight x ∂covarianceGaussian T

theorem boxEnvelopeNormalizer_pos {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {b : ℝ} (hb : 0 < b) : 0 < boxEnvelopeNormalizer T b := by
  haveI : NeZero ((covarianceGaussian T).restrict (coordinateBox b)) :=
    ⟨fun h => (ne_of_gt (coordinateBox_gaussian_pos hT hb)) (Measure.restrict_eq_zero.mp h)⟩
  exact integral_exp_pos (integrable_envelopeWeight T).integrableOn

def boxEnvelopeLaw (T : Matrix ι ι ℝ) (b : ℝ) : Measure (ι → ℝ) :=
  ((covarianceGaussian T).restrict (coordinateBox b)).tilted (fun x => -envelopePotential x)

theorem boxEnvelopeLaw_probability {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {b : ℝ} (hb : 0 < b) : IsProbabilityMeasure (boxEnvelopeLaw T b) := by
  haveI : NeZero ((covarianceGaussian T).restrict (coordinateBox b)) :=
    ⟨fun h => (ne_of_gt (coordinateBox_gaussian_pos hT hb)) (Measure.restrict_eq_zero.mp h)⟩
  exact isProbabilityMeasure_tilted (integrable_envelopeWeight T).integrableOn

theorem boxEnvelopeLaw_ae_mem (T : Matrix ι ι ℝ) (b : ℝ) :
    ∀ᵐ x ∂boxEnvelopeLaw T b, x ∈ coordinateBox b := by
  exact (tilted_absolutelyContinuous _ _).ae_le (ae_restrict_mem (coordinateBox_measurable b))

theorem integral_boxEnvelopeLaw (T : Matrix ι ι ℝ) (b : ℝ) (f : (ι → ℝ) → ℝ) :
    (∫ x, f x ∂boxEnvelopeLaw T b) =
      (∫ x in coordinateBox b, envelopeWeight x * f x ∂covarianceGaussian T) /
        boxEnvelopeNormalizer T b := by
  rw [boxEnvelopeLaw, integral_tilted]
  simp only [smul_eq_mul]
  calc
    _ = ∫ x in coordinateBox b, (envelopeWeight x * f x) / boxEnvelopeNormalizer T b
        ∂covarianceGaussian T := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (envelopeWeight x / boxEnvelopeNormalizer T b) * f x = _
      ring
    _ = _ := integral_div _ _

theorem integrable_boxEnvelopeLaw (T : Matrix ι ι ℝ) (b : ℝ)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f (covarianceGaussian T)) :
    Integrable f (boxEnvelopeLaw T b) := by
  rw [boxEnvelopeLaw, integrable_tilted_iff (integrable_envelopeWeight T).integrableOn]
  change Integrable (fun x => envelopeWeight x * f x)
    ((covarianceGaussian T).restrict (coordinateBox b))
  apply hf.norm.integrableOn.mono'
    (continuous_envelopeWeight.aestronglyMeasurable.mul hf.aestronglyMeasurable.restrict)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖envelopeWeight x * f x‖ ≤ ‖f x‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (envelopeWeight_pos x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (envelopeWeight_le_one x))

theorem integrable_boxEnvelopeLaw_exp_dot {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (b : ℝ) (u : ι → ℝ) :
    Integrable (fun x => Real.exp (u ⬝ᵥ x)) (boxEnvelopeLaw T b) :=
  integrable_boxEnvelopeLaw T b (integrable_exp_dot hT u)

theorem integral_boxEnvelopeLaw_dot (T : Matrix ι ι ℝ) (b : ℝ) (u : ι → ℝ) :
    (∫ x, u ⬝ᵥ x ∂boxEnvelopeLaw T b) = 0 := by
  let f : (ι → ℝ) → ℝ := (coordinateBox b).indicator
    (fun x => envelopeWeight x * (u ⬝ᵥ x))
  have he (x : ι → ℝ) : f (-x) = -f x := by
    by_cases hx : x ∈ coordinateBox b
    · simp [f, hx, (coordinateBox_neg_iff b x).mpr hx, envelopeWeight_neg, dotProduct_neg]
    · have hn : -x ∉ coordinateBox b := fun h => hx ((coordinateBox_neg_iff b x).mp h)
      simp [f, hx, hn]
  have hneg := integral_covarianceGaussian_neg T f
  simp_rw [he, integral_neg] at hneg
  have hz : (∫ x, f x ∂covarianceGaussian T) = 0 := by linarith
  have hz' : (∫ x in coordinateBox b, envelopeWeight x * (u ⬝ᵥ x)
      ∂covarianceGaussian T) = 0 := by
    rwa [show f = (coordinateBox b).indicator (fun x => envelopeWeight x * (u ⬝ᵥ x)) from rfl,
      integral_indicator (coordinateBox_measurable b)] at hz
  rw [integral_boxEnvelopeLaw, hz', zero_div]

theorem setIntegral_covarianceGaussian_eq {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (s : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) :
    (∫ x in s, f x ∂covarianceGaussian T) = ∫ x in s, covarianceDensity T x * f x := by
  rw [covarianceGaussian_eq_withDensity hT,
    setIntegral_withDensity_eq_setIntegral_toReal_smul' s
      (measurable_covarianceDensity T).ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (covarianceDensity_nonneg T _), smul_eq_mul]

/-- The actual translated Gaussian-envelope cell integral. -/
def translatedEnvelopeCell (T : Matrix ι ι ℝ) (b : ℝ) (z : ι → ℝ) : ℝ :=
  ∫ x in coordinateBox b, covarianceDensity T (z + x) * envelopeWeight x

/-- Exact cell identity before any subgaussian or lattice estimate. -/
theorem translatedEnvelopeCell_identity {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {b : ℝ} (hb : 0 < b) (z : ι → ℝ) :
    translatedEnvelopeCell T b z =
      boxEnvelopeNormalizer T b * Real.exp (-quadratic T⁻¹ z / 2) *
        ∫ x, Real.exp (-(z ⬝ᵥ (T⁻¹ *ᵥ x))) ∂boxEnvelopeLaw T b := by
  rw [integral_boxEnvelopeLaw, setIntegral_covarianceGaussian_eq hT]
  have hZ := ne_of_gt (boxEnvelopeNormalizer_pos hT hb)
  have he : translatedEnvelopeCell T b z =
      Real.exp (-quadratic T⁻¹ z / 2) *
        ∫ x in coordinateBox b, covarianceDensity T x *
          (envelopeWeight x * Real.exp (-(z ⬝ᵥ (T⁻¹ *ᵥ x)))) := by
    unfold translatedEnvelopeCell
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [covarianceDensity_shift hT, sub_eq_add_neg, Real.exp_add]
    simp only [neg_div]
    ring
  rw [he]
  field_simp

end

end TheoremA2.GaussianCovariance
