import TheoremA2.GaussianCovarianceTranslation
import TheoremA2.CosineEnvelope

/-!
# The actual global envelope Gaussian law

The positive reference law is the actual matrix Gaussian tilted by the
explicit cosine envelope. Its mass, moments, integrability and symmetry are
proved here before any Brascamp–Lieb estimate is applied.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem standardGaussian_map_neg :
    (standardGaussian (ι := ι)).map (fun x => -x) = standardGaussian := by
  haveI (i : ι) : IsProbabilityMeasure ((gaussianReal 0 1).map (fun x : ℝ => -x)) :=
    inferInstance
  change (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
    (fun x i => -x i) = _
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  simp only [gaussianReal_map_neg, neg_zero, standardGaussian]

theorem covarianceGaussian_map_neg (T : Matrix ι ι ℝ) :
    (covarianceGaussian T).map (fun x => -x) = covarianceGaussian T := by
  unfold covarianceGaussian
  rw [Measure.map_map (by fun_prop) (measurable_mulVec (CFC.sqrt T))]
  have he : (fun x : ι → ℝ => -(CFC.sqrt T *ᵥ x)) =
      (fun x => CFC.sqrt T *ᵥ (-x)) := by
    funext x
    exact (Matrix.mulVec_neg _ _).symm
  change (standardGaussian (ι := ι)).map (fun x => -(CFC.sqrt T *ᵥ x)) = _
  rw [he]
  have hm := Measure.map_map (μ := standardGaussian (ι := ι))
    (measurable_mulVec (CFC.sqrt T))
    (by fun_prop : Measurable (fun x : ι → ℝ => -x))
  rw [standardGaussian_map_neg] at hm
  exact hm.symm

theorem integral_covarianceGaussian_neg (T : Matrix ι ι ℝ) (f : (ι → ℝ) → ℝ) :
    (∫ x, f (-x) ∂covarianceGaussian T) = ∫ x, f x ∂covarianceGaussian T := by
  have hh := integral_map_equiv (μ := covarianceGaussian T) (MeasurableEquiv.neg (ι → ℝ)) f
  change (∫ x, f x ∂(covarianceGaussian T).map (fun x => -x)) =
    ∫ x, f (-x) ∂covarianceGaussian T at hh
  rw [covarianceGaussian_map_neg] at hh
  exact hh.symm

def envelopePotential (x : ι → ℝ) : ℝ := ∑ i, CosineEnvelope.envelope (x i)

def envelopeWeight (x : ι → ℝ) : ℝ := Real.exp (-envelopePotential x)

theorem continuous_envelopePotential : Continuous (@envelopePotential ι _) := by
  unfold envelopePotential
  exact continuous_finset_sum _ fun i _ =>
    CosineEnvelope.envelope_contDiff.continuous.comp (continuous_apply i)

theorem continuous_envelopeWeight : Continuous (@envelopeWeight ι _) :=
  Real.continuous_exp.comp continuous_envelopePotential.neg

theorem envelopePotential_nonneg (x : ι → ℝ) : 0 ≤ envelopePotential x :=
  Finset.sum_nonneg fun i _ => CosineEnvelope.envelope_nonneg _

theorem envelopePotential_neg (x : ι → ℝ) : envelopePotential (-x) = envelopePotential x := by
  simp only [envelopePotential, Pi.neg_apply, CosineEnvelope.envelope_even _]

theorem envelopeWeight_pos (x : ι → ℝ) : 0 < envelopeWeight x := Real.exp_pos _

theorem envelopeWeight_le_one (x : ι → ℝ) : envelopeWeight x ≤ 1 := by
  rw [envelopeWeight, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (envelopePotential_nonneg x)

theorem envelopeWeight_neg (x : ι → ℝ) : envelopeWeight (-x) = envelopeWeight x := by
  rw [envelopeWeight, envelopeWeight, envelopePotential_neg]

theorem integrable_envelopeWeight (T : Matrix ι ι ℝ) :
    Integrable envelopeWeight (covarianceGaussian T) := by
  apply (integrable_const (1 : ℝ)).mono' continuous_envelopeWeight.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (envelopeWeight_pos x)]
    exact envelopeWeight_le_one x)

def envelopeNormalizer (T : Matrix ι ι ℝ) : ℝ := ∫ x, envelopeWeight x ∂covarianceGaussian T

theorem envelopeNormalizer_pos (T : Matrix ι ι ℝ) : 0 < envelopeNormalizer T :=
  integral_exp_pos (integrable_envelopeWeight T)

theorem envelopeNormalizer_le_one (T : Matrix ι ι ℝ) : envelopeNormalizer T ≤ 1 := by
  have h := integral_mono (integrable_envelopeWeight T) (integrable_const (1 : ℝ))
    envelopeWeight_le_one
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  exact h

def envelopeLaw (T : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (covarianceGaussian T).tilted (fun x => -envelopePotential x)

instance envelopeLaw_probability (T : Matrix ι ι ℝ) : IsProbabilityMeasure (envelopeLaw T) :=
  isProbabilityMeasure_tilted (integrable_envelopeWeight T)

/-- Every genuinely Gaussian-integrable function remains integrable under the bounded tilt. -/
theorem integrable_envelopeLaw (T : Matrix ι ι ℝ) {f : (ι → ℝ) → ℝ}
    (hf : Integrable f (covarianceGaussian T)) : Integrable f (envelopeLaw T) := by
  rw [envelopeLaw, integrable_tilted_iff (integrable_envelopeWeight T)]
  change Integrable (fun x => envelopeWeight x * f x) (covarianceGaussian T)
  apply hf.norm.mono' (continuous_envelopeWeight.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖envelopeWeight x * f x‖ ≤ ‖f x‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (envelopeWeight_pos x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (envelopeWeight_le_one x))

/-- The normalizer is the actual positive Gaussian-envelope integral. -/
theorem integral_envelopeLaw (T : Matrix ι ι ℝ) (f : (ι → ℝ) → ℝ) :
    (∫ x, f x ∂envelopeLaw T) =
      (∫ x, envelopeWeight x * f x ∂covarianceGaussian T) / envelopeNormalizer T := by
  rw [envelopeLaw, integral_tilted]
  simp only [smul_eq_mul]
  calc
    _ = ∫ x, (envelopeWeight x * f x) / envelopeNormalizer T ∂covarianceGaussian T := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (envelopeWeight x / envelopeNormalizer T) * f x = _
      ring
    _ = _ := integral_div _ _

theorem integrable_envelopeLaw_dot {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    Integrable (fun x => b ⬝ᵥ x) (envelopeLaw T) :=
  integrable_envelopeLaw T (integrable_dot hT b)

theorem integrable_envelopeLaw_dot_sq {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    Integrable (fun x => (b ⬝ᵥ x) ^ 2) (envelopeLaw T) :=
  integrable_envelopeLaw T (integrable_dot_sq hT b)

theorem integrable_envelopeLaw_exp_dot {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (b : ι → ℝ) :
    Integrable (fun x => Real.exp (b ⬝ᵥ x)) (envelopeLaw T) :=
  integrable_envelopeLaw T (integrable_exp_dot hT b)

/-- Centering follows from the actual sign symmetry of both Gaussian and envelope. -/
theorem integral_envelopeLaw_dot (T : Matrix ι ι ℝ) (b : ι → ℝ) :
    (∫ x, b ⬝ᵥ x ∂envelopeLaw T) = 0 := by
  have hneg := integral_covarianceGaussian_neg T (fun x => envelopeWeight x * (b ⬝ᵥ x))
  simp only [envelopeWeight_neg, dotProduct_neg, mul_neg, integral_neg] at hneg
  have hz : (∫ x, envelopeWeight x * (b ⬝ᵥ x) ∂covarianceGaussian T) = 0 := by linarith
  rw [integral_envelopeLaw, hz, zero_div]

end

end TheoremA2.GaussianCovariance
