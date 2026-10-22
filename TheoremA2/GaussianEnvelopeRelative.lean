import TheoremA2.GaussianEnvelopeCells
import TheoremA2.GaussianEnvelopePointwise
import TheoremA2.GaussianEnvelopeTail
import TheoremA2.GaussianSquareMGF
import TheoremA2.GaussianRelativeAlgebra

/-!
# Relative normalizer and second-moment comparison

All error terms below refer to the literal Gaussian and normalized envelope
integrals. The displayed MGF/fourth-moment inputs are the precise outputs of
the separate Brascamp–Lieb module; the cell decomposition, changes of Gaussian
covariance, Cauchy–Schwarz estimate, and division by the signed normalizer are
proved here.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem periodic_tail_relative_of_mgf {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {q : ℝ} (hq : 0 < q) (hdiag : ∀ i, T i i ≤ q)
    (hcut : q / decoderBeta ≤ 1 / 1000000)
    (hmgf : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw T (Real.pi / 2)) ≤
        Real.exp (quadratic (cellPrecision T)⁻¹ u / 2)) :
    (∫ x in (coordinateBox (Real.pi / 2))ᶜ, periodicEnvelopeWeight x ∂covarianceGaussian T) ≤
      latticeError (Fintype.card ι) q * boxEnvelopeNormalizer T (Real.pi / 2) := by
  obtain ⟨hs, hsum⟩ := noncentral_envelope_cells_of_mgf hT hq hdiag hcut hmgf
  exact (periodic_tail_le_cells hT hs).trans hsum

/-- Equation (49), derived from the genuine global and central MGFs. -/
theorem normalizer_relative_error_of_mgf {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {q : ℝ} (hq : 0 < q) (hdiag : ∀ i, T i i ≤ q)
    (hcut : q / decoderBeta ≤ 1 / 1000000)
    (hglobal : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂envelopeLaw T) ≤ Real.exp (quadratic T u / 2))
    (hbox : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw T (Real.pi / 2)) ≤
        Real.exp (quadratic (cellPrecision T)⁻¹ u / 2)) :
    |spinGaussianNormalizer T - envelopeNormalizer T| ≤
      SpinCovariance.zeroFieldAlpha (Fintype.card ι) q * envelopeNormalizer T := by
  have htail := inner_box_tail_of_matrix_mgf (envelopeLaw T) T hq hdiag
    (integrable_envelopeLaw_exp_dot hT.posSemidef) hglobal
  have hinner : (∫ x in (coordinateBox (1 / 4))ᶜ, envelopeWeight x ∂covarianceGaussian T) ≤
      SpinCovariance.zeroFieldDelta (Fintype.card ι) q * envelopeNormalizer T := by
    have he := envelope_weighted_setIntegral T ((coordinateBox (1 / 4))ᶜ) (fun _ => (1 : ℝ))
    simp only [mul_one] at he
    rw [he, mul_comm]
    exact mul_le_mul_of_nonneg_right htail (envelopeNormalizer_pos T).le
  have hperiod := periodic_tail_relative_of_mgf hT hq hdiag hcut hbox
  have hperiod' : (∫ x in (coordinateBox (Real.pi / 2))ᶜ, periodicEnvelopeWeight x
      ∂covarianceGaussian T) ≤ latticeError (Fintype.card ι) q * envelopeNormalizer T :=
    hperiod.trans (mul_le_mul_of_nonneg_left (boxEnvelopeNormalizer_le_global T (Real.pi / 2))
      (Real.exp_pos _).le)
  calc
    _ ≤ (∫ x in (coordinateBox (1 / 4))ᶜ, envelopeWeight x ∂covarianceGaussian T) +
        ∫ x in (coordinateBox (Real.pi / 2))ᶜ, periodicEnvelopeWeight x ∂covarianceGaussian T :=
      normalizer_error_le_two_integrals hT.posSemidef
    _ ≤ SpinCovariance.zeroFieldDelta (Fintype.card ι) q * envelopeNormalizer T +
        latticeError (Fintype.card ι) q * envelopeNormalizer T :=
      add_le_add hinner hperiod'
    _ = _ := by unfold SpinCovariance.zeroFieldAlpha; ring

/-- Actual Cauchy–Schwarz on the bad-box event, preserving its probability. -/
theorem inner_second_moment_of_fourth {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (v : ι → ℝ) {delta w : ℝ} (hdelta : 0 ≤ delta) (hw : 0 ≤ w)
    (htail : (∫ x in (coordinateBox (1 / 4))ᶜ, (1 : ℝ) ∂envelopeLaw T) ≤ delta)
    (hfourth : (∫ x, (v ⬝ᵥ x) ^ 4 ∂envelopeLaw T) ≤ 5 * w ^ 2) :
    (∫ x in (coordinateBox (1 / 4))ᶜ, (v ⬝ᵥ x) ^ 2 ∂envelopeLaw T) ≤
      Real.sqrt (5 * delta) * w := by
  let s : Set (ι → ℝ) := (coordinateBox (1 / 4))ᶜ
  let f : (ι → ℝ) → ℝ := fun x => (v ⬝ᵥ x) ^ 2
  let g : (ι → ℝ) → ℝ := s.indicator (fun _ => 1)
  have hs : MeasurableSet s := (coordinateBox_measurable (1 / 4)).compl
  have hf : MemLp f 2 (envelopeLaw T) := by
    apply (memLp_two_iff_integrable_sq (integrable_envelopeLaw_dot_sq hT v).aestronglyMeasurable).mpr
    convert integrable_envelopeLaw_dot_pow hT v 4 using 1
    funext x
    ring
  have hg : MemLp g 2 (envelopeLaw T) := (memLp_const (1 : ℝ)).indicator hs
  have hpq : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := envelopeLaw T) (f := f) (g := g) hpq
    (Filter.Eventually.of_forall (fun x => sq_nonneg (v ⬝ᵥ x)))
    (Filter.Eventually.of_forall (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x))
    (by simpa using hf) (by simpa using hg)
  have hprod (x : ι → ℝ) : f x * g x = s.indicator f x := by
    by_cases hx : x ∈ s <;> simp [g, hx]
  have hf2 (x : ι → ℝ) : f x ^ (2 : ℝ) = (v ⬝ᵥ x) ^ 4 := by
    rw [Real.rpow_two]
    dsimp [f]
    ring
  have hg2 (x : ι → ℝ) : g x ^ (2 : ℝ) = g x := by
    rw [Real.rpow_two]
    by_cases hx : x ∈ s <;> simp [g, hx]
  simp_rw [hprod, hf2, hg2] at hh
  rw [integral_indicator hs, show (∫ x, g x ∂envelopeLaw T) =
    ∫ x in s, (1 : ℝ) ∂envelopeLaw T from integral_indicator hs,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have hsqrt := mul_le_mul (Real.sqrt_le_sqrt hfourth) (Real.sqrt_le_sqrt htail)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have he : Real.sqrt (5 * w ^ 2) * Real.sqrt delta = Real.sqrt (5 * delta) * w := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 5 * w ^ 2),
      show (5 * w ^ 2) * delta = (5 * delta) * w ^ 2 by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 5 * delta), Real.sqrt_sq hw]
  exact hh.trans (he ▸ hsqrt)

theorem squared_projection_le_rankOne_exponential {T : Matrix ι ι ℝ}
    (v : ι → ℝ) (hw : 0 < quadratic T v) (x : ι → ℝ) :
    (v ⬝ᵥ x) ^ 2 ≤ 4 * quadratic T v * Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)) := by
  have hh := Real.add_one_le_exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v))
  have hle : (v ⬝ᵥ x) ^ 2 / (4 * quadratic T v) ≤
      Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)) := by linarith
  have hh' := (div_le_iff₀ (by positivity : 0 < 4 * quadratic T v)).mp hle
  simpa only [mul_comm] using hh'

/-- The weighted periodic error is absorbed into a genuine new Gaussian law.
The central normalizer comparison retains the factor `I(T)`. -/
theorem periodic_second_error_of_mgf {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {q : ℝ} (hq : 0 < q) (hdiag : ∀ i, T i i ≤ q)
    (hcut : 2 * q / decoderBeta ≤ 1 / 1000000)
    (hboxT : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw T (Real.pi / 2)) ≤ Real.exp (quadratic T u / 2))
    (v : ι → ℝ) (hw : 0 < quadratic T v)
    (hboxU : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw (rankOneCovariance T v) (Real.pi / 2)) ≤
        Real.exp (quadratic (cellPrecision (rankOneCovariance T v))⁻¹ u / 2)) :
    (∫ x in (coordinateBox (Real.pi / 2))ᶜ, (v ⬝ᵥ x) ^ 2 * periodicEnvelopeWeight x
      ∂covarianceGaussian T) ≤
      (4 * Real.sqrt 2 * latticeError (Fintype.card ι) (2 * q)) *
        envelopeNormalizer T * quadratic T v := by
  have hU := rankOneCovariance_posDef hT v
  have hdiagU (i : ι) : rankOneCovariance T v i i ≤ 2 * q :=
    (rankOneCovariance_diag_le hT.posSemidef v hw i).trans (by linarith [hdiag i])
  have htail := periodic_tail_relative_of_mgf hU (by positivity : 0 < 2 * q)
    hdiagU hcut hboxU
  have hnormalizer := (rankOne_boxNormalizer_le hT (by positivity : 0 < Real.pi / 2)
    hboxT v hw).trans (boxEnvelopeNormalizer_le_global T (Real.pi / 2))
  have hj : Integrable (fun x =>
      Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)) * periodicEnvelopeWeight x)
      (covarianceGaussian T) := by
    apply (integrable_rankOne_tilt hT v hw).mono'
      (((measurable_dot v).pow_const 2 |>.div_const (4 * quadratic T v) |>.exp).mul
        measurable_periodicEnvelopeWeight |>.aestronglyMeasurable)
    filter_upwards [] with x
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (periodicEnvelopeWeight_pos x).le)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (periodicEnvelopeWeight_le_one x)
  have hpoint (x : ι → ℝ) : (v ⬝ᵥ x) ^ 2 * periodicEnvelopeWeight x ≤
      (4 * quadratic T v) *
        (Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)) * periodicEnvelopeWeight x) := by
    have hh := mul_le_mul_of_nonneg_right (squared_projection_le_rankOne_exponential v hw x)
      (periodicEnvelopeWeight_pos x).le
    simpa only [mul_assoc] using hh
  calc
    _ ≤ ∫ x in (coordinateBox (Real.pi / 2))ᶜ, (4 * quadratic T v) *
        (Real.exp ((v ⬝ᵥ x) ^ 2 / (4 * quadratic T v)) * periodicEnvelopeWeight x)
        ∂covarianceGaussian T :=
      integral_mono (integrable_dot_sq_periodicEnvelopeWeight hT.posSemidef v).integrableOn
        (hj.const_mul _).integrableOn hpoint
    _ = (4 * quadratic T v) * (Real.sqrt 2 *
        ∫ x in (coordinateBox (Real.pi / 2))ᶜ, periodicEnvelopeWeight x
          ∂covarianceGaussian (rankOneCovariance T v)) := by
      rw [integral_const_mul, setIntegral_rankOne_tilt hT v hw]
    _ ≤ (4 * quadratic T v) * (Real.sqrt 2 *
        (latticeError (Fintype.card ι) (2 * q) * boxEnvelopeNormalizer (rankOneCovariance T v) (Real.pi / 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg _)) (by positivity)
    _ ≤ (4 * quadratic T v) * (Real.sqrt 2 *
        (latticeError (Fintype.card ι) (2 * q) * envelopeNormalizer T)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_left hnormalizer (Real.exp_pos _).le
    _ = _ := by ring

/-- The actual signed second moment comparison of A.27 from the literal BL
outputs. Its denominator is the proved positive spin partition, not a signed
probability law. Every Gaussian-period error is derived in this module. -/
theorem signed_second_moment_comparison_of_bounds {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {q : ℝ} (hq : 0 < q) (hdiag : ∀ i, T i i ≤ q)
    (hcut : 2 * q / decoderBeta ≤ 1 / 1000000)
    (halpha : SpinCovariance.zeroFieldAlpha (Fintype.card ι) q < 1)
    (hglobal : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂envelopeLaw T) ≤ Real.exp (quadratic T u / 2))
    (hbox : ∀ {U : Matrix ι ι ℝ}, U.PosDef → ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw U (Real.pi / 2)) ≤
        Real.exp (quadratic (cellPrecision U)⁻¹ u / 2))
    (hboxT : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw T (Real.pi / 2)) ≤ Real.exp (quadratic T u / 2))
    (hsecond : ∀ v : ι → ℝ,
      (∫ x, (v ⬝ᵥ x) ^ 2 ∂envelopeLaw T) ≤ quadratic T v)
    (hfourth : ∀ v : ι → ℝ,
      (∫ x, (v ⬝ᵥ x) ^ 4 ∂envelopeLaw T) ≤ 5 * (quadratic T v) ^ 2)
    (v : ι → ℝ) :
    |signedSecondMoment T v - (∫ x, (v ⬝ᵥ x) ^ 2 ∂envelopeLaw T)| ≤
      SpinCovariance.zeroFieldZeta (Fintype.card ι) q * quadratic T v := by
  by_cases hv : v = 0
  · subst v
    simp [signedSecondMoment, quadratic]
  have hw : 0 < quadratic T v := by simpa [quadratic] using hT.dotProduct_mulVec_pos hv
  have hcutq : q / decoderBeta ≤ 1 / 1000000 := by
    have hb : 0 < decoderBeta := by norm_num [decoderBeta]
    exact (div_le_div_of_nonneg_right (by linarith : q ≤ 2 * q) hb.le).trans hcut
  have hnormalizer := normalizer_relative_error_of_mgf hT hq hdiag hcutq hglobal (hbox hT)
  have htail := inner_box_tail_of_matrix_mgf (envelopeLaw T) T hq hdiag
    (integrable_envelopeLaw_exp_dot hT.posSemidef) hglobal
  have hdelta : 0 ≤ SpinCovariance.zeroFieldDelta (Fintype.card ι) q := by
    unfold SpinCovariance.zeroFieldDelta
    positivity
  have hinner := inner_second_moment_of_fourth hT.posSemidef v hdelta hw.le htail (hfourth v)
  have hinnerWeighted :
      (∫ x in (coordinateBox (1 / 4))ᶜ, (v ⬝ᵥ x) ^ 2 * envelopeWeight x ∂covarianceGaussian T) ≤
        Real.sqrt (5 * SpinCovariance.zeroFieldDelta (Fintype.card ι) q) *
          envelopeNormalizer T * quadratic T v := by
    have he := envelope_weighted_setIntegral T ((coordinateBox (1 / 4))ᶜ)
      (fun x => (v ⬝ᵥ x) ^ 2)
    have hh := mul_le_mul_of_nonneg_left hinner (envelopeNormalizer_pos T).le
    rw [← he] at hh
    simpa only [mul_comm (envelopeWeight _) ((v ⬝ᵥ _) ^ 2), mul_left_comm, mul_assoc] using hh
  have hperiod := periodic_second_error_of_mgf hT hq hdiag hcut hboxT v hw
    (hbox (rankOneCovariance_posDef hT v))
  have hpoint := second_moment_error_le_two_integrals hT.posSemidef v
  have hB : (∫ x, (v ⬝ᵥ x) ^ 2 * envelopeWeight x ∂covarianceGaussian T) =
      envelopeNormalizer T * (∫ x, (v ⬝ᵥ x) ^ 2 ∂envelopeLaw T) := by
    rw [integral_envelopeLaw]
    rw [mul_div_cancel₀ _ (ne_of_gt (envelopeNormalizer_pos T))]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))
  have hmom : |(∫ x, (v ⬝ᵥ x) ^ 2 * cosineProduct x ∂covarianceGaussian T) -
      envelopeNormalizer T * (∫ x, (v ⬝ᵥ x) ^ 2 ∂envelopeLaw T)| ≤
      (Real.sqrt (5 * SpinCovariance.zeroFieldDelta (Fintype.card ι) q) +
        4 * Real.sqrt 2 * latticeError (Fintype.card ι) (2 * q)) *
        envelopeNormalizer T * quadratic T v := by
    rw [← hB]
    calc
      _ ≤ (∫ x in (coordinateBox (1 / 4))ᶜ, (v ⬝ᵥ x) ^ 2 * envelopeWeight x
          ∂covarianceGaussian T) +
          ∫ x in (coordinateBox (Real.pi / 2))ᶜ, (v ⬝ᵥ x) ^ 2 * periodicEnvelopeWeight x
            ∂covarianceGaussian T := hpoint
      _ ≤ Real.sqrt (5 * SpinCovariance.zeroFieldDelta (Fintype.card ι) q) *
          envelopeNormalizer T * quadratic T v +
          (4 * Real.sqrt 2 * latticeError (Fintype.card ι) (2 * q)) *
            envelopeNormalizer T * quadratic T v :=
        add_le_add hinnerWeighted hperiod
      _ = _ := by ring
  have ha0 : 0 ≤ SpinCovariance.zeroFieldAlpha (Fintype.card ι) q := by
    unfold SpinCovariance.zeroFieldAlpha latticeError
    positivity
  have he0 : 0 ≤ Real.sqrt (5 * SpinCovariance.zeroFieldDelta (Fintype.card ι) q) +
      4 * Real.sqrt 2 * latticeError (Fintype.card ι) (2 * q) := by
    unfold latticeError
    positivity
  have hm0 : 0 ≤ ∫ x, (v ⬝ᵥ x) ^ 2 ∂envelopeLaw T :=
    integral_nonneg (fun x => sq_nonneg (v ⬝ᵥ x))
  have hh := relative_second_moment_algebra (spinGaussianNormalizer_pos T)
    (envelopeNormalizer_pos T) hw.le hm0
    (hsecond v) ha0 halpha he0 hnormalizer hmom
  simpa only [signedSecondMoment, cosineProduct, SpinCovariance.zeroFieldZeta, add_assoc] using hh

end

end TheoremA2.GaussianCovariance
