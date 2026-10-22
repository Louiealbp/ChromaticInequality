import TheoremA2.PrincipalInverse
import TheoremA2.FiniteExponential
import Mathlib.Probability.Moments.Variance

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-!
# Actual finite–continuous mixture laws and total variance

The joint law is the literal density `w / total` with respect to counting
measure times the base measure. Its continuous marginal has density
`partition / total`, and the finite conditional masses are exactly
`w / partition`. Disintegration and total variance are proved from these
concrete definitions, finite sums, and Fubini.
-/

namespace TheoremA2.FiniteContinuousMixture

open MeasureTheory ProbabilityTheory Set
open TheoremA2.ConvexSupport TheoremA2.PrincipalInverse
open scoped BigOperators ENNReal
noncomputable section

variable {Ω T : Type*} [Fintype Ω] [Nonempty Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [MeasurableSpace T]

/-- The actual finite partition at a fixed continuous coordinate. -/
def partition (w : Ω → T → ℝ) (t : T) : ℝ := ∑ ω, w ω t

def total (μ : Measure T) (w : Ω → T → ℝ) : ℝ := ∫ t, partition w t ∂μ

def base (μ : Measure T) : Measure (Ω × T) := Measure.count.prod μ

def joint (μ : Measure T) (w : Ω → T → ℝ) : Measure (Ω × T) :=
  (base μ).withDensity (fun p => ENNReal.ofReal (w p.1 p.2 / total μ w))

def marginal (μ : Measure T) (w : Ω → T → ℝ) : Measure T :=
  μ.withDensity (fun t => ENNReal.ofReal (partition w t / total μ w))

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [MeasurableSpace T] in
theorem partition_pos (w : Ω → T → ℝ) (hwpos : ∀ ω t, 0 < w ω t) (t : T) :
    0 < partition w t :=
  Finset.sum_pos (fun ω _ => hwpos ω t) Finset.univ_nonempty

/-- The literal finite conditional law. -/
def conditional (w : Ω → T → ℝ) (hwpos : ∀ ω t, 0 < w ω t) (t : T) :
    FiniteProbability Ω where
  mass ω := w ω t / partition w t
  nonneg ω := (div_pos (hwpos ω t) (partition_pos w hwpos t)).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (partition_pos w hwpos t))

def conditionalMean (w : Ω → T → ℝ) (hwpos : ∀ ω t, 0 < w ω t)
    (f : Ω × T → ℝ) (t : T) : ℝ :=
  (conditional w hwpos t).expectation (fun ω => f (ω, t))

def conditionalVariance (w : Ω → T → ℝ) (hwpos : ∀ ω t, 0 < w ω t)
    (f : Ω × T → ℝ) (t : T) : ℝ :=
  (conditional w hwpos t).expectation
    (fun ω => (f (ω, t) - conditionalMean w hwpos f t) ^ 2)

omit [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem measurable_partition (w : Ω → T → ℝ) (hw : ∀ ω, Measurable (w ω)) :
    Measurable (partition w) :=
  Finset.measurable_sum _ (fun ω _ => hw ω)

omit [Nonempty Ω] in
theorem measurable_weight (w : Ω → T → ℝ) (hw : ∀ ω, Measurable (w ω)) :
    Measurable (fun p : Ω × T => w p.1 p.2) := by
  apply measurable_from_prod_countable_right
  exact hw

omit [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem integrable_partition (μ : Measure T) (w : Ω → T → ℝ)
    (hwi : ∀ ω, Integrable (w ω) μ) : Integrable (partition w) μ :=
  integrable_finsetSum _ (fun ω _ => hwi ω)

theorem integrable_weight (μ : Measure T) [SFinite μ] (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwi : ∀ ω, Integrable (w ω) μ) :
    Integrable (fun p : Ω × T => w p.1 p.2) (base μ) := by
  apply (integrable_prod_iff (measurable_weight w hw).aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall hwi, Integrable.of_finite⟩

theorem integral_weight (μ : Measure T) [SFinite μ] (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwi : ∀ ω, Integrable (w ω) μ) :
    (∫ p : Ω × T, w p.1 p.2 ∂base μ) = total μ w := by
  rw [base, integral_prod_symm _ (integrable_weight μ w hw hwi)]
  simp only [integral_count]
  rfl

/-- Normalization of the actual joint density. -/
theorem isProbabilityMeasure_joint (μ : Measure T) [SFinite μ] (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (hwi : ∀ ω, Integrable (w ω) μ) (htotal : 0 < total μ w) :
    IsProbabilityMeasure (joint μ w) := by
  constructor
  rw [joint, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_weight μ w hw hwi).div_const _)
    (Filter.Eventually.of_forall fun p => div_nonneg (hwpos p.1 p.2).le htotal.le)]
  rw [integral_div, integral_weight μ w hw hwi, div_self (ne_of_gt htotal)]
  simp

/-- Normalization of the actual continuous marginal density. -/
theorem isProbabilityMeasure_marginal (μ : Measure T) (w : Ω → T → ℝ)
    (hwpos : ∀ ω t, 0 < w ω t) (hwi : ∀ ω, Integrable (w ω) μ)
    (htotal : 0 < total μ w) : IsProbabilityMeasure (marginal μ w) := by
  constructor
  rw [marginal, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_partition μ w hwi).div_const _)
    (Filter.Eventually.of_forall fun t => div_nonneg (partition_pos w hwpos t).le htotal.le)]
  rw [integral_div]
  change ENNReal.ofReal (total μ w / total μ w) = 1
  rw [div_self (ne_of_gt htotal)]
  simp

theorem integral_joint_raw (μ : Measure T) (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (htotal : 0 < total μ w) (f : Ω × T → ℝ) :
    (∫ p, f p ∂joint μ w) =
      (total μ w)⁻¹ * ∫ p, w p.1 p.2 * f p ∂base μ := by
  rw [joint, integral_withDensity_eq_integral_toReal_smul
    (((measurable_weight w hw).div_const _).ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (div_nonneg (hwpos _ _).le htotal.le), smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  ring

theorem integral_marginal_raw (μ : Measure T) (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (htotal : 0 < total μ w) (f : T → ℝ) :
    (∫ t, f t ∂marginal μ w) =
      (total μ w)⁻¹ * ∫ t, partition w t * f t ∂μ := by
  rw [marginal, integral_withDensity_eq_integral_toReal_smul
    (((measurable_partition w hw).div_const _).ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (div_nonneg (partition_pos w hwpos _).le htotal.le),
    smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem integrable_joint_iff (μ : Measure T) (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (htotal : 0 < total μ w) (f : Ω × T → ℝ) :
    Integrable f (joint μ w) ↔ Integrable (fun p => w p.1 p.2 * f p) (base μ) := by
  rw [joint, integrable_withDensity_iff_integrable_smul'
    (((measurable_weight w hw).div_const _).ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (div_nonneg (hwpos _ _).le htotal.le), smul_eq_mul]
  have he : (fun p : Ω × T => w p.1 p.2 / total μ w * f p) =
      fun p => (total μ w)⁻¹ * (w p.1 p.2 * f p) := by funext p; ring
  rw [he]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero (ne_of_gt htotal))) _

theorem integrable_marginal_iff (μ : Measure T) (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (htotal : 0 < total μ w) (f : T → ℝ) :
    Integrable f (marginal μ w) ↔ Integrable (fun t => partition w t * f t) μ := by
  rw [marginal, integrable_withDensity_iff_integrable_smul'
    (((measurable_partition w hw).div_const _).ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (div_nonneg (partition_pos w hwpos _).le htotal.le),
    smul_eq_mul]
  have he : (fun t => partition w t / total μ w * f t) =
      fun t => (total μ w)⁻¹ * (partition w t * f t) := by funext t; ring
  rw [he]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero (ne_of_gt htotal))) _

theorem partition_mul_conditionalMean (w : Ω → T → ℝ) (hwpos : ∀ ω t, 0 < w ω t)
    (f : Ω × T → ℝ) (t : T) :
    partition w t * conditionalMean w hwpos f t = ∑ ω, w ω t * f (ω, t) := by
  simp only [conditionalMean, FiniteProbability.expectation, conditional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  field_simp [ne_of_gt (partition_pos w hwpos t)]

theorem measurable_conditionalMean (w : Ω → T → ℝ) (hw : ∀ ω, Measurable (w ω))
    (hwpos : ∀ ω t, 0 < w ω t) (f : Ω × T → ℝ) (hf : Measurable f) :
    Measurable (conditionalMean w hwpos f) := by
  unfold conditionalMean FiniteProbability.expectation conditional
  apply Finset.measurable_sum
  intro ω _
  exact ((hw ω).div (measurable_partition w hw)).mul
    (hf.comp (measurable_const.prodMk measurable_id))

theorem integrable_weight_mul (μ : Measure T) [SFinite μ] (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (f : Ω × T → ℝ) (hf : Measurable f)
    (hfi : ∀ ω, Integrable (fun t => w ω t * f (ω, t)) μ) :
    Integrable (fun p => w p.1 p.2 * f p) (base μ) := by
  apply (integrable_prod_iff ((measurable_weight w hw).mul hf).aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall hfi, Integrable.of_finite⟩

theorem integrable_conditionalMean (μ : Measure T) (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (htotal : 0 < total μ w) (f : Ω × T → ℝ)
    (hfi : ∀ ω, Integrable (fun t => w ω t * f (ω, t)) μ) :
    Integrable (conditionalMean w hwpos f) (marginal μ w) := by
  rw [integrable_marginal_iff μ w hw hwpos htotal]
  simp_rw [partition_mul_conditionalMean]
  exact integrable_finsetSum _ (fun ω _ => hfi ω)

/-- Actual disintegration over the continuous coordinate. -/
theorem integral_disintegration (μ : Measure T) [SFinite μ] (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (htotal : 0 < total μ w) (f : Ω × T → ℝ) (hf : Measurable f)
    (hfi : ∀ ω, Integrable (fun t => w ω t * f (ω, t)) μ) :
    (∫ p, f p ∂joint μ w) = ∫ t, conditionalMean w hwpos f t ∂marginal μ w := by
  rw [integral_joint_raw μ w hw hwpos htotal, integral_marginal_raw μ w hw hwpos htotal]
  congr 1
  rw [base, integral_prod_symm _ (integrable_weight_mul μ w hw f hf hfi)]
  simp only [integral_count, partition_mul_conditionalMean]


omit [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The finite conditional variance has the ordinary second-moment formula. -/
theorem finite_centered_sq (p : FiniteProbability Ω) (g : Ω → ℝ) :
    p.expectation (fun ω => (g ω - p.expectation g) ^ 2) =
      p.expectation (fun ω => g ω ^ 2) - (p.expectation g) ^ 2 := by
  have he (ω : Ω) : (g ω - p.expectation g) ^ 2 =
      g ω ^ 2 - 2 * p.expectation g * g ω + (p.expectation g) ^ 2 := by ring
  simp_rw [he, expectation_add, expectation_sub, expectation_const_mul, expectation_const]
  ring

theorem conditionalVariance_eq (w : Ω → T → ℝ) (hwpos : ∀ ω t, 0 < w ω t)
    (f : Ω × T → ℝ) (t : T) :
    conditionalVariance w hwpos f t =
      conditionalMean w hwpos (fun p => f p ^ 2) t - conditionalMean w hwpos f t ^ 2 :=
  finite_centered_sq (conditional w hwpos t) (fun ω => f (ω, t))

theorem conditionalMean_sq_le (w : Ω → T → ℝ) (hwpos : ∀ ω t, 0 < w ω t)
    (f : Ω × T → ℝ) (t : T) :
    conditionalMean w hwpos f t ^ 2 ≤ conditionalMean w hwpos (fun p => f p ^ 2) t := by
  have h : 0 ≤ conditionalVariance w hwpos f t :=
    expectation_nonneg (conditional w hwpos t) (fun _ => sq_nonneg _)
  rw [conditionalVariance_eq] at h
  linarith

theorem integrable_conditionalMean_sq (μ : Measure T) (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (htotal : 0 < total μ w) (f : Ω × T → ℝ) (hf : Measurable f)
    (hfi2 : ∀ ω, Integrable (fun t => w ω t * f (ω, t) ^ 2) μ) :
    Integrable (fun t => conditionalMean w hwpos f t ^ 2) (marginal μ w) := by
  have hs := integrable_conditionalMean μ w hw hwpos htotal (fun p => f p ^ 2) hfi2
  apply hs.mono' ((measurable_conditionalMean w hw hwpos f hf).pow_const 2).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact conditionalMean_sq_le w hwpos f t

theorem integrable_conditionalVariance (μ : Measure T) (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (htotal : 0 < total μ w) (f : Ω × T → ℝ) (hf : Measurable f)
    (hfi2 : ∀ ω, Integrable (fun t => w ω t * f (ω, t) ^ 2) μ) :
    Integrable (conditionalVariance w hwpos f) (marginal μ w) := by
  have he : conditionalVariance w hwpos f = fun t =>
      conditionalMean w hwpos (fun p => f p ^ 2) t - conditionalMean w hwpos f t ^ 2 :=
    funext (conditionalVariance_eq w hwpos f)
  rw [he]
  exact (integrable_conditionalMean μ w hw hwpos htotal (fun p => f p ^ 2) hfi2).sub
    (integrable_conditionalMean_sq μ w hw hwpos htotal f hf hfi2)

/-- The law of total variance for the actual normalized joint and marginal laws.
All first and second weighted moments are explicit; conditional moments are
computed from the true finite conditional masses `w / partition`. -/
theorem total_variance (μ : Measure T) [SFinite μ] (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (hwi : ∀ ω, Integrable (w ω) μ) (htotal : 0 < total μ w)
    (f : Ω × T → ℝ) (hf : Measurable f)
    (hfi : ∀ ω, Integrable (fun t => w ω t * f (ω, t)) μ)
    (hfi2 : ∀ ω, Integrable (fun t => w ω t * f (ω, t) ^ 2) μ) :
    variance f (joint μ w) =
      (∫ t, conditionalVariance w hwpos f t ∂marginal μ w) +
        variance (conditionalMean w hwpos f) (marginal μ w) := by
  letI := isProbabilityMeasure_joint μ w hw hwpos hwi htotal
  letI := isProbabilityMeasure_marginal μ w hwpos hwi htotal
  have hf2 : Integrable (fun p => f p ^ 2) (joint μ w) :=
    (integrable_joint_iff μ w hw hwpos htotal _).2
      (integrable_weight_mul μ w hw (fun p => f p ^ 2) (hf.pow_const 2) hfi2)
  have hfLp : MemLp f 2 (joint μ w) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf2
  have hm2 := integrable_conditionalMean_sq μ w hw hwpos htotal f hf hfi2
  have hmLp : MemLp (conditionalMean w hwpos f) 2 (marginal μ w) :=
    (memLp_two_iff_integrable_sq
      (measurable_conditionalMean w hw hwpos f hf).aestronglyMeasurable).2 hm2
  rw [variance_eq_sub hfLp, variance_eq_sub hmLp]
  change (∫ p, f p ^ 2 ∂joint μ w) - (∫ p, f p ∂joint μ w) ^ 2 =
    (∫ t, conditionalVariance w hwpos f t ∂marginal μ w) +
      ((∫ t, conditionalMean w hwpos f t ^ 2 ∂marginal μ w) -
        (∫ t, conditionalMean w hwpos f t ∂marginal μ w) ^ 2)
  rw [integral_disintegration μ w hw hwpos htotal (fun p => f p ^ 2) (hf.pow_const 2) hfi2,
    integral_disintegration μ w hw hwpos htotal f hf hfi]
  have hv : (∫ t, conditionalVariance w hwpos f t ∂marginal μ w) =
      (∫ t, conditionalMean w hwpos (fun p => f p ^ 2) t ∂marginal μ w) -
        ∫ t, conditionalMean w hwpos f t ^ 2 ∂marginal μ w := by
    simp_rw [conditionalVariance_eq]
    exact integral_sub (integrable_conditionalMean μ w hw hwpos htotal (fun p => f p ^ 2) hfi2) hm2
  rw [hv]
  ring

/-- At a fixed continuous coordinate the auxiliary summand is constant. -/
theorem conditionalMean_add_aux (w : Ω → T → ℝ) (hwpos : ∀ ω t, 0 < w ω t)
    (a : Ω → ℝ) (b : T → ℝ) (t : T) :
    conditionalMean w hwpos (fun p => a p.1 + b p.2) t =
      (conditional w hwpos t).expectation a + b t := by
  change (conditional w hwpos t).expectation (fun ω => a ω + b t) =
    (conditional w hwpos t).expectation a + b t
  rw [expectation_add, expectation_const]

theorem conditionalVariance_add_aux (w : Ω → T → ℝ) (hwpos : ∀ ω t, 0 < w ω t)
    (a : Ω → ℝ) (b : T → ℝ) (t : T) :
    conditionalVariance w hwpos (fun p => a p.1 + b p.2) t =
      conditionalVariance w hwpos (fun p => a p.1) t := by
  unfold conditionalVariance
  rw [conditionalMean_add_aux]
  apply congrArg (conditional w hwpos t).expectation
  funext ω
  change (a ω + b t - ((conditional w hwpos t).expectation a + b t)) ^ 2 =
    (a ω - (conditional w hwpos t).expectation a) ^ 2
  ring

/-- The exact decomposition used for a spin-linear plus auxiliary-linear observable
in A.33; the statement is more general and permits any measurable auxiliary term. -/
theorem total_variance_add_aux (μ : Measure T) [SFinite μ] (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (hwi : ∀ ω, Integrable (w ω) μ) (htotal : 0 < total μ w)
    (a : Ω → ℝ) (b : T → ℝ) (hb : Measurable b)
    (hfi : ∀ ω, Integrable (fun t => w ω t * (a ω + b t)) μ)
    (hfi2 : ∀ ω, Integrable (fun t => w ω t * (a ω + b t) ^ 2) μ) :
    variance (fun p : Ω × T => a p.1 + b p.2) (joint μ w) =
      (∫ t, conditionalVariance w hwpos (fun p => a p.1) t ∂marginal μ w) +
        variance (fun t => (conditional w hwpos t).expectation a + b t) (marginal μ w) := by
  have hf : Measurable (fun p : Ω × T => a p.1 + b p.2) :=
    ((measurable_of_countable a).comp measurable_fst).add (hb.comp measurable_snd)
  have hm : conditionalMean w hwpos (fun p => a p.1 + b p.2) =
      fun t => (conditional w hwpos t).expectation a + b t :=
    funext (conditionalMean_add_aux w hwpos a b)
  simpa only [hm, conditionalVariance_add_aux] using
    total_variance μ w hw hwpos hwi htotal (fun p => a p.1 + b p.2) hf hfi hfi2

/-- The conditional masses coincide definitionally with the actual finite
exponential-family law used in the Hessian calculations. -/
theorem conditional_exponential [NormedAddCommGroup T] [NormedSpace ℝ T]
    (a : Ω → ℝ) (L : Ω → T →L[ℝ] ℝ) (t : T) :
    conditional (fun ω x => FiniteExponential.weight a L x ω)
      (fun _ _ => Real.exp_pos _) t = FiniteExponential.law a L t := rfl


/-- The unnormalized total-variance identity used directly with the Lebesgue
Brascamp–Lieb estimate. Every moment is a literal weighted integral; the
marginal weight is exactly the finite partition, with no law supplied as a premise. -/
theorem weighted_variance_decomposition (μ : Measure T) (w : Ω → T → ℝ)
    (hw : ∀ ω, Measurable (w ω)) (hwpos : ∀ ω t, 0 < w ω t)
    (htotal : 0 < total μ w) (f : Ω × T → ℝ) (hf : Measurable f)
    (hfi : ∀ ω, Integrable (fun t => w ω t * f (ω, t)) μ)
    (hfi2 : ∀ ω, Integrable (fun t => w ω t * f (ω, t) ^ 2) μ) :
    (∑ ω, ∫ t, w ω t * f (ω, t) ^ 2 ∂μ) -
        (∑ ω, ∫ t, w ω t * f (ω, t) ∂μ) ^ 2 / total μ w =
      ((∫ t, partition w t * conditionalMean w hwpos f t ^ 2 ∂μ) -
        (∫ t, partition w t * conditionalMean w hwpos f t ∂μ) ^ 2 / total μ w) +
          ∫ t, partition w t * conditionalVariance w hwpos f t ∂μ := by
  have hm : (∑ ω, ∫ t, w ω t * f (ω, t) ∂μ) =
      ∫ t, partition w t * conditionalMean w hwpos f t ∂μ := by
    rw [← integral_finsetSum _ (fun ω _ => hfi ω)]
    apply integral_congr_ae
    filter_upwards [] with t
    exact (partition_mul_conditionalMean w hwpos f t).symm
  have hs : (∑ ω, ∫ t, w ω t * f (ω, t) ^ 2 ∂μ) =
      ∫ t, partition w t * conditionalMean w hwpos (fun p => f p ^ 2) t ∂μ := by
    rw [← integral_finsetSum _ (fun ω _ => hfi2 ω)]
    apply integral_congr_ae
    filter_upwards [] with t
    exact (partition_mul_conditionalMean w hwpos (fun p => f p ^ 2) t).symm
  have hvInt : Integrable (fun t => partition w t * conditionalVariance w hwpos f t) μ :=
    (integrable_marginal_iff μ w hw hwpos htotal _).1
      (integrable_conditionalVariance μ w hw hwpos htotal f hf hfi2)
  have hmInt : Integrable (fun t => partition w t * conditionalMean w hwpos f t ^ 2) μ :=
    (integrable_marginal_iff μ w hw hwpos htotal _).1
      (integrable_conditionalMean_sq μ w hw hwpos htotal f hf hfi2)
  have hsplit : (∫ t, partition w t * conditionalMean w hwpos (fun p => f p ^ 2) t ∂μ) =
      (∫ t, partition w t * conditionalVariance w hwpos f t ∂μ) +
        ∫ t, partition w t * conditionalMean w hwpos f t ^ 2 ∂μ := by
    rw [← integral_add hvInt hmInt]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [conditionalVariance_eq]
    ring
  rw [hm, hs, hsplit]
  ring

end
end TheoremA2.FiniteContinuousMixture
