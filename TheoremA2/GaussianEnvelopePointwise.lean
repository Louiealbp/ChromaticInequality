import TheoremA2.GaussianEnvelopePeriods
import TheoremA2.GaussianSpinFourier
import TheoremA2.GaussianPolynomial

/-!
# Actual signed-cosine error and its two supports

The cosine product is never declared to be a probability density. Its absolute
difference from the positive envelope is bounded pointwise, then integrated
using genuine integrability of every term.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cosineProduct (x : ι → ℝ) : ℝ := ∏ i, Real.cos (x i)

theorem envelopeWeight_eq_prod (x : ι → ℝ) :
    envelopeWeight x = ∏ i, Real.exp (-CosineEnvelope.envelope (x i)) := by
  simp only [envelopeWeight, envelopePotential, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem cosineProduct_eq_envelope_inner {x : ι → ℝ}
    (hx : x ∈ coordinateBox (1 / 4)) : cosineProduct x = envelopeWeight x := by
  rw [cosineProduct, envelopeWeight_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (CosineEnvelope.exp_neg_envelope_eq_cos (hx i)).symm

theorem cosineProduct_nonneg_central {x : ι → ℝ}
    (hx : x ∈ coordinateBox (Real.pi / 2)) : 0 ≤ cosineProduct x := by
  apply Finset.prod_nonneg
  intro i _
  exact Real.cos_nonneg_of_mem_Icc (abs_le.mp (hx i))

theorem cosineProduct_le_envelope_central {x : ι → ℝ}
    (hx : x ∈ coordinateBox (Real.pi / 2)) : cosineProduct x ≤ envelopeWeight x := by
  rw [cosineProduct, envelopeWeight_eq_prod]
  apply Finset.prod_le_prod₀
  · intro i _
    exact Real.cos_nonneg_of_mem_Icc (abs_le.mp (hx i))
  · intro i _
    exact CosineEnvelope.cos_le_exp_neg_envelope (hx i)

theorem abs_cosineProduct_le_periodic (x : ι → ℝ) :
    |cosineProduct x| ≤ periodicEnvelopeWeight x := by
  rw [cosineProduct, Finset.abs_prod, periodicEnvelopeWeight, envelopeWeight_eq_prod]
  apply Finset.prod_le_prod₀
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [PeriodicCells.abs_cos_eq_remainder]
    exact CosineEnvelope.cos_le_exp_neg_envelope (PeriodicCells.abs_remainder_le (x i))

theorem inner_box_subset_central :
    coordinateBox (ι := ι) (1 / 4) ⊆ coordinateBox (Real.pi / 2) := by
  intro x hx i
  exact (hx i).trans (by linarith [Real.pi_gt_three])

/-- Equation (48), with both actual error supports and both actual weights. -/
theorem cosine_envelope_error_pointwise (x : ι → ℝ) :
    |cosineProduct x - envelopeWeight x| ≤
      ((coordinateBox (1 / 4))ᶜ).indicator envelopeWeight x +
        ((coordinateBox (Real.pi / 2))ᶜ).indicator periodicEnvelopeWeight x := by
  classical
  by_cases hx : x ∈ coordinateBox (1 / 4)
  · rw [cosineProduct_eq_envelope_inner hx, sub_self, abs_zero,
      Set.indicator_of_notMem (show x ∉ (coordinateBox (1 / 4))ᶜ from fun h => h hx),
      Set.indicator_of_notMem (show x ∉ (coordinateBox (Real.pi / 2))ᶜ from
        fun h => h (inner_box_subset_central hx))]
    norm_num
  · rw [Set.indicator_of_mem (show x ∈ (coordinateBox (1 / 4))ᶜ from hx)]
    by_cases hq : x ∈ coordinateBox (Real.pi / 2)
    · rw [Set.indicator_of_notMem (show x ∉ (coordinateBox (Real.pi / 2))ᶜ from fun h => h hq),
        add_zero, abs_of_nonpos (sub_nonpos.mpr (cosineProduct_le_envelope_central hq))]
      linarith [cosineProduct_nonneg_central hq]
    · rw [Set.indicator_of_mem (show x ∈ (coordinateBox (Real.pi / 2))ᶜ from hq)]
      have hab := abs_sub_le (cosineProduct x) 0 (envelopeWeight x)
      simp only [sub_zero, zero_sub, abs_neg, abs_of_pos (envelopeWeight_pos x)] at hab
      linarith [abs_cosineProduct_le_periodic x]

theorem integrable_cosineProduct (T : Matrix ι ι ℝ) :
    Integrable cosineProduct (covarianceGaussian T) := by
  have hc : Continuous (cosineProduct (ι := ι)) := by
    unfold cosineProduct
    fun_prop
  apply (integrable_const (1 : ℝ)).mono' hc.measurable.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact (abs_cosineProduct_le_periodic x).trans (periodicEnvelopeWeight_le_one x)

theorem integrable_dot_sq_cosineProduct {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (v : ι → ℝ) :
    Integrable (fun x => (v ⬝ᵥ x) ^ 2 * cosineProduct x) (covarianceGaussian T) := by
  apply (integrable_dot_sq hT v).mono' (by unfold cosineProduct dotProduct; fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_of_le_one_right (sq_nonneg _)
    ((abs_cosineProduct_le_periodic x).trans (periodicEnvelopeWeight_le_one x))

theorem integrable_dot_sq_envelopeWeight {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (v : ι → ℝ) :
    Integrable (fun x => (v ⬝ᵥ x) ^ 2 * envelopeWeight x) (covarianceGaussian T) := by
  apply (integrable_dot_sq hT v).mono'
    (((measurable_dot v).pow_const 2).mul
      continuous_envelopeWeight.measurable |>.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply] at *
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
    abs_of_pos (envelopeWeight_pos x)]
  exact mul_le_of_le_one_right (sq_nonneg _) (envelopeWeight_le_one x)

theorem integrable_dot_sq_periodicEnvelopeWeight {T : Matrix ι ι ℝ}
    (hT : T.PosSemidef) (v : ι → ℝ) :
    Integrable (fun x => (v ⬝ᵥ x) ^ 2 * periodicEnvelopeWeight x) (covarianceGaussian T) := by
  apply (integrable_dot_sq hT v).mono'
    (((measurable_dot v).pow_const 2).mul measurable_periodicEnvelopeWeight |>.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply] at *
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
    abs_of_pos (periodicEnvelopeWeight_pos x)]
  exact mul_le_of_le_one_right (sq_nonneg _) (periodicEnvelopeWeight_le_one x)

theorem normalizer_error_le_two_integrals {T : Matrix ι ι ℝ} (hT : T.PosSemidef) :
    |spinGaussianNormalizer T - envelopeNormalizer T| ≤
      (∫ x in (coordinateBox (1 / 4))ᶜ, envelopeWeight x ∂covarianceGaussian T) +
        ∫ x in (coordinateBox (Real.pi / 2))ᶜ, periodicEnvelopeWeight x ∂covarianceGaussian T := by
  have hcos := integrable_cosineProduct T
  have he := integrable_envelopeWeight T
  have hi := he.indicator (coordinateBox_measurable (1 / 4)).compl
  have hp := (integrable_periodicEnvelopeWeight T).indicator
    (coordinateBox_measurable (Real.pi / 2)).compl
  have hbound := integral_mono (hcos.sub he).abs (hi.add hp) cosine_envelope_error_pointwise
  simp only [Pi.add_apply, Pi.sub_apply] at hbound
  have hnorm := abs_integral_le_integral_abs
    (f := fun x : ι → ℝ => cosineProduct x - envelopeWeight x) (μ := covarianceGaussian T)
  rw [integral_sub hcos he, show (∫ x, cosineProduct x ∂covarianceGaussian T) =
    spinGaussianNormalizer T from integral_cosine_product hT] at hnorm
  rw [integral_add hi hp,
    integral_indicator (coordinateBox_measurable (1 / 4)).compl,
    integral_indicator (coordinateBox_measurable (Real.pi / 2)).compl] at hbound
  exact hnorm.trans hbound

theorem second_moment_error_le_two_integrals {T : Matrix ι ι ℝ}
    (hT : T.PosSemidef) (v : ι → ℝ) :
    |(∫ x, (v ⬝ᵥ x) ^ 2 * cosineProduct x ∂covarianceGaussian T) -
        (∫ x, (v ⬝ᵥ x) ^ 2 * envelopeWeight x ∂covarianceGaussian T)| ≤
      (∫ x in (coordinateBox (1 / 4))ᶜ, (v ⬝ᵥ x) ^ 2 * envelopeWeight x
        ∂covarianceGaussian T) +
      ∫ x in (coordinateBox (Real.pi / 2))ᶜ, (v ⬝ᵥ x) ^ 2 * periodicEnvelopeWeight x
        ∂covarianceGaussian T := by
  have hcos := integrable_dot_sq_cosineProduct hT v
  have he := integrable_dot_sq_envelopeWeight hT v
  have hi := he.indicator (coordinateBox_measurable (1 / 4)).compl
  have hp := (integrable_dot_sq_periodicEnvelopeWeight hT v).indicator
    (coordinateBox_measurable (Real.pi / 2)).compl
  have hpoint (x : ι → ℝ) :
      |(v ⬝ᵥ x) ^ 2 * cosineProduct x - (v ⬝ᵥ x) ^ 2 * envelopeWeight x| ≤
        ((coordinateBox (1 / 4))ᶜ).indicator (fun x => (v ⬝ᵥ x) ^ 2 * envelopeWeight x) x +
          ((coordinateBox (Real.pi / 2))ᶜ).indicator
            (fun x => (v ⬝ᵥ x) ^ 2 * periodicEnvelopeWeight x) x := by
    have hh := mul_le_mul_of_nonneg_left (cosine_envelope_error_pointwise x) (sq_nonneg (v ⬝ᵥ x))
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    simpa only [mul_add, Set.indicator_mul_right] using hh
  have hbound := integral_mono (hcos.sub he).abs (hi.add hp) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hbound
  have hnorm := abs_integral_le_integral_abs
    (f := fun x => (v ⬝ᵥ x) ^ 2 * cosineProduct x - (v ⬝ᵥ x) ^ 2 * envelopeWeight x)
    (μ := covarianceGaussian T)
  rw [integral_sub hcos he] at hnorm
  rw [integral_add hi hp,
    integral_indicator (coordinateBox_measurable (1 / 4)).compl,
    integral_indicator (coordinateBox_measurable (Real.pi / 2)).compl] at hbound
  exact hnorm.trans hbound

/-- Exact restricted integration under the positive normalized envelope law. -/
theorem setIntegral_envelopeLaw (T : Matrix ι ι ℝ) (s : Set (ι → ℝ))
    (f : (ι → ℝ) → ℝ) :
    (∫ x in s, f x ∂envelopeLaw T) =
      (∫ x in s, envelopeWeight x * f x ∂covarianceGaussian T) / envelopeNormalizer T := by
  rw [envelopeLaw, setIntegral_tilted]
  calc
    _ = ∫ x in s, (envelopeWeight x * f x) / envelopeNormalizer T ∂covarianceGaussian T := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (envelopeWeight x / envelopeNormalizer T) * f x = _
      ring
    _ = _ := integral_div _ _

theorem envelope_weighted_setIntegral (T : Matrix ι ι ℝ) (s : Set (ι → ℝ))
    (f : (ι → ℝ) → ℝ) :
    (∫ x in s, envelopeWeight x * f x ∂covarianceGaussian T) =
      envelopeNormalizer T * ∫ x in s, f x ∂envelopeLaw T := by
  rw [setIntegral_envelopeLaw]
  field_simp [ne_of_gt (envelopeNormalizer_pos T)]

end

end TheoremA2.GaussianCovariance
