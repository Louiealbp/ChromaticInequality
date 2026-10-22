import TheoremA2.Imports
import TheoremA2.Normalizer

set_option maxHeartbeats 400000

/-!
# The actual positive scalar reference construction in Section A.8

We use the weight `exp(-t²/(4 lam))*cos(t/(2 lam))` on
`[-π lam, π lam]`. The scalar Gaussian prefactor appearing in the paper
cancels between the numerator and normalizer. These are ordinary real
Lebesgue integrals of explicit functions, not an abstract assumed reference.

This module proves positivity of the normalizer, a genuine normalized
probability density and MGF representation, evenness, the global lower bound
(62), and the resulting reference-normalizer lower bound (77). The scalar
prior curvature is proved below. The companion `CosineReferenceBounds.lean`
proves the central cosine majorant (60) and the quantitative error (61) for
this same explicit function, using a direct convolution argument.

The support is represented by a closed interval; the weight vanishes at its
endpoints. No extension of the logarithmic potential beyond its open support
is used in any derivative or curvature assertion. The paper's separate bound
`7/8 ≤ Zc ≤ 1` for its Gaussian-normalized scalar weight is not proved here;
our positivity, majorant, and error proofs do not require that bound.
-/

namespace TheoremA2.CosineReference

open MeasureTheory Set
open scoped Topology

noncomputable section

/-- The endpoint `b_lam = π lam`. -/
def endpoint (lam : ℝ) : ℝ := Real.pi * lam

/-- The unnormalized cosine-truncated Gaussian weight, before restriction. -/
def weight (lam t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2) / (4 * lam)) * Real.cos (t / (2 * lam))

/-- The normalizer without the common Gaussian prefactor. -/
def normalizer (lam : ℝ) : ℝ :=
  ∫ t in -endpoint lam..endpoint lam, weight lam t

/-- The exponential moment integral before normalization. -/
def momentIntegral (lam x : ℝ) : ℝ :=
  ∫ t in -endpoint lam..endpoint lam, weight lam t * Real.exp (x * t)

/-- The precise positive scalar reference function, with all integrals explicit. -/
def reference (lam x : ℝ) : ℝ :=
  Real.exp (-lam * x ^ 2) * (momentIntegral lam x / normalizer lam)

theorem continuous_weight (lam : ℝ) : Continuous (weight lam) := by
  unfold weight
  fun_prop

theorem continuous_momentIntegrand (lam x : ℝ) :
    Continuous (fun t : ℝ => weight lam t * Real.exp (x * t)) := by
  exact (continuous_weight lam).mul (by fun_prop)

@[simp] theorem weight_neg (lam t : ℝ) : weight lam (-t) = weight lam t := by
  simp [weight, neg_div]

@[simp] theorem weight_zero (lam : ℝ) : weight lam 0 = 1 := by
  simp [weight]

theorem endpoint_pos {lam : ℝ} (hlam : 0 < lam) : 0 < endpoint lam :=
  mul_pos Real.pi_pos hlam

theorem weight_nonneg {lam t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Icc (-endpoint lam) (endpoint lam)) : 0 ≤ weight lam t := by
  have hl2 : 0 < 2 * lam := by positivity
  apply mul_nonneg (Real.exp_pos _).le
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · apply (le_div_iff₀ hl2).2
    dsimp [endpoint] at ht
    nlinarith [ht.1]
  · apply (div_le_iff₀ hl2).2
    dsimp [endpoint] at ht
    nlinarith [ht.2]

theorem normalizer_pos {lam : ℝ} (hlam : 0 < lam) : 0 < normalizer lam := by
  have hb := endpoint_pos hlam
  apply intervalIntegral.integral_pos (by linarith)
    (continuous_weight lam).continuousOn
  · intro t ht
    exact weight_nonneg hlam ⟨ht.1.le, ht.2⟩
  · exact ⟨0, ⟨by linarith, by linarith⟩, by simp⟩

/-- Symmetry of the actual moment integral under `x ↦ -x`. -/
@[simp] theorem momentIntegral_neg (lam x : ℝ) :
    momentIntegral lam (-x) = momentIntegral lam x := by
  have h := intervalIntegral.integral_comp_neg
    (f := fun t : ℝ => weight lam t * Real.exp (x * t))
    (a := -endpoint lam) (b := endpoint lam)
  simpa [momentIntegral, mul_neg, neg_mul] using h

@[simp] theorem momentIntegral_zero (lam : ℝ) :
    momentIntegral lam 0 = normalizer lam := by
  simp [momentIntegral, normalizer]

@[simp] theorem reference_neg (lam x : ℝ) : reference lam (-x) = reference lam x := by
  simp [reference]

theorem reference_zero {lam : ℝ} (hlam : 0 < lam) : reference lam 0 = 1 := by
  simp [reference, ne_of_gt (normalizer_pos hlam)]

/-- Symmetry and the exponential tangent-line inequality give `E exp(x T) ≥ 1`. -/
theorem normalizer_le_momentIntegral {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    normalizer lam ≤ momentIntegral lam x := by
  have hb := endpoint_pos hlam
  have hpoint (t : ℝ) (ht : t ∈ Icc (-endpoint lam) (endpoint lam)) :
      2 * weight lam t ≤
        weight lam t * Real.exp (x * t) + weight lam t * Real.exp ((-x) * t) := by
    have he : 2 ≤ Real.exp (x * t) + Real.exp ((-x) * t) := by
      have h1 := Real.add_one_le_exp (x * t)
      have h2 := Real.add_one_le_exp ((-x) * t)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left he (weight_nonneg hlam ht)
    nlinarith
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -endpoint lam ≤ endpoint lam)
    ((continuous_const.mul (continuous_weight lam)).intervalIntegrable _ _)
    (((continuous_momentIntegrand lam x).add (continuous_momentIntegrand lam (-x))).intervalIntegrable _ _)
    hpoint
  simp only [Pi.mul_apply, Pi.add_apply] at h
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      ((continuous_momentIntegrand lam x).intervalIntegrable _ _)
      ((continuous_momentIntegrand lam (-x)).intervalIntegrable _ _)] at h
  change 2 * normalizer lam ≤ momentIntegral lam x + momentIntegral lam (-x) at h
  rw [momentIntegral_neg] at h
  linarith

/-- Equation (62), for the explicit scalar reference construction. -/
theorem gaussian_lower_bound {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    Real.exp (-lam * x ^ 2) ≤ reference lam x := by
  have hm : 1 ≤ momentIntegral lam x / normalizer lam :=
    (one_le_div (normalizer_pos hlam)).2 (normalizer_le_momentIntegral hlam x)
  unfold reference
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (Real.exp_pos (-lam * x ^ 2)).le

theorem reference_pos {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    0 < reference lam x :=
  lt_of_lt_of_le (Real.exp_pos _) (gaussian_lower_bound hlam x)


/-- The actual real-valued probability density, extended by zero outside its support. -/
def density (lam : ℝ) : ℝ → ℝ :=
  (Icc (-endpoint lam) (endpoint lam)).indicator
    (fun t => weight lam t / normalizer lam)

theorem density_nonneg {lam : ℝ} (hlam : 0 < lam) (t : ℝ) : 0 ≤ density lam t := by
  by_cases ht : t ∈ Icc (-endpoint lam) (endpoint lam)
  · simp only [density, indicator_of_mem ht]
    exact div_nonneg (weight_nonneg hlam ht) (normalizer_pos hlam).le
  · simp [density, ht]

theorem integrable_density (lam : ℝ) : Integrable (density lam) := by
  unfold density
  apply (integrable_indicator_iff measurableSet_Icc).2
  have hc : Continuous (fun t : ℝ => weight lam t / normalizer lam) := by
    unfold weight
    fun_prop
  exact hc.integrableOn_Icc

/-- The density is normalized by an ordinary Lebesgue integral. -/
theorem integral_density {lam : ℝ} (hlam : 0 < lam) : ∫ t, density lam t = 1 := by
  have hb := endpoint_pos hlam
  unfold density
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -endpoint lam ≤ endpoint lam),
    intervalIntegral.integral_div]
  change normalizer lam / normalizer lam = 1
  exact div_self (ne_of_gt (normalizer_pos hlam))

/-- Identifies the normalized moment integral with the actual density's MGF. -/
theorem density_exponential_moment {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    (∫ t, density lam t * Real.exp (x * t)) = momentIntegral lam x / normalizer lam := by
  have hb := endpoint_pos hlam
  have hf : (fun t => density lam t * Real.exp (x * t)) =
      (Icc (-endpoint lam) (endpoint lam)).indicator
        (fun t => (weight lam t * Real.exp (x * t)) / normalizer lam) := by
    funext t
    by_cases ht : t ∈ Icc (-endpoint lam) (endpoint lam)
    · simp only [density, indicator_of_mem ht]
      ring
    · simp [density, ht]
  rw [hf, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -endpoint lam ≤ endpoint lam),
    intervalIntegral.integral_div]
  rfl

/-- The positive reference really is a Gaussian factor times a probability MGF. -/
theorem reference_eq_gaussian_times_mgf {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    reference lam x = Real.exp (-lam * x ^ 2) *
      (∫ t, density lam t * Real.exp (x * t)) := by
  rw [density_exponential_moment hlam]
  rfl

/-- Equation (77) for the explicit reference function, with no majorant assumption. -/
theorem referenceNormalizer_lower_bound_explicit {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Real.exp (-lam * TheoremA2.frobeniusSq B) ≤
      TheoremA2.referenceNormalizer B (reference lam) := by
  exact TheoremA2.referenceNormalizer_lower_bound B lam (reference lam)
    (gaussian_lower_bound hlam)


/-- The potential of the unnormalized scalar prior on its open support. -/
def priorPotential (lam t : ℝ) : ℝ :=
  t ^ 2 / (4 * lam) - Real.log (Real.cos (t / (2 * lam)))

def priorDerivative (lam t : ℝ) : ℝ :=
  t / (2 * lam) + Real.tan (t / (2 * lam)) / (2 * lam)

def priorSecondDerivative (lam t : ℝ) : ℝ :=
  1 / (2 * lam) + (1 / (4 * lam ^ 2)) * (1 / Real.cos (t / (2 * lam)) ^ 2)

def curvatureConstant (lam : ℝ) : ℝ := (2 * lam + 1) / (4 * lam ^ 2)

theorem cosine_pos_on_support {lam t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Ioo (-endpoint lam) (endpoint lam)) :
    0 < Real.cos (t / (2 * lam)) := by
  apply Real.cos_pos_of_mem_Ioo
  have hl2 : 0 < 2 * lam := by positivity
  constructor
  · apply (lt_div_iff₀ hl2).2
    dsimp [endpoint] at ht
    nlinarith [ht.1]
  · apply (div_lt_iff₀ hl2).2
    dsimp [endpoint] at ht
    nlinarith [ht.2]

/-- The asserted potential is the actual negative logarithm of the weight. -/
theorem weight_eq_exp_neg_potential {lam t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Ioo (-endpoint lam) (endpoint lam)) :
    weight lam t = Real.exp (-priorPotential lam t) := by
  have hc := cosine_pos_on_support hlam ht
  unfold weight priorPotential
  rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hc]
  rw [neg_div]
  ring

theorem hasDerivAt_priorPotential {lam t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Ioo (-endpoint lam) (endpoint lam)) :
    HasDerivAt (priorPotential lam) (priorDerivative lam t) t := by
  have hc := ne_of_gt (cosine_pos_on_support hlam ht)
  have hquad := ((hasDerivAt_id t).pow 2).div_const (4 * lam)
  have hcos := (Real.hasDerivAt_cos (t / (2 * lam))).comp t
    ((hasDerivAt_id t).div_const (2 * lam))
  have hlog := hcos.log hc
  convert hquad.sub hlog using 1
  · rfl
  · unfold priorDerivative
    simp only [Real.tan_eq_sin_div_cos, Function.comp_apply, id_eq,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    have hl0 := ne_of_gt hlam
    field_simp
    ring

theorem hasDerivAt_priorDerivative {lam t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Ioo (-endpoint lam) (endpoint lam)) :
    HasDerivAt (priorDerivative lam) (priorSecondDerivative lam t) t := by
  have hc := ne_of_gt (cosine_pos_on_support hlam ht)
  have hlin := (hasDerivAt_id t).div_const (2 * lam)
  have htan := ((Real.hasDerivAt_tan hc).comp t
    ((hasDerivAt_id t).div_const (2 * lam))).div_const (2 * lam)
  convert hlin.add htan using 1
  · rfl
  · unfold priorSecondDerivative
    have hl0 := ne_of_gt hlam
    field_simp
    ring

/-- The precise lower bound on the scalar prior's second derivative from A.32. -/
theorem prior_curvature_lower_bound {lam t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Ioo (-endpoint lam) (endpoint lam)) :
    curvatureConstant lam ≤ priorSecondDerivative lam t := by
  have hc := cosine_pos_on_support hlam ht
  have hcs : 0 < Real.cos (t / (2 * lam)) ^ 2 := sq_pos_of_pos hc
  have hupper : Real.cos (t / (2 * lam)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (t / (2 * lam)),
      sq_nonneg (Real.sin (t / (2 * lam)))]
  have hi : 1 ≤ 1 / Real.cos (t / (2 * lam)) ^ 2 :=
    (one_le_div hcs).2 hupper
  have hp : 0 ≤ (1 : ℝ) / (4 * lam ^ 2) := by positivity
  have hh := mul_le_mul_of_nonneg_left hi hp
  have heq : curvatureConstant lam = 1 / (2 * lam) + 1 / (4 * lam ^ 2) := by
    unfold curvatureConstant
    field_simp
    ring
  rw [heq]
  unfold priorSecondDerivative
  linarith


/-- All real exponential moments of the genuine compactly supported density are integrable. -/
theorem integrable_density_exponential_moment (lam x : ℝ) :
    Integrable (fun t => density lam t * Real.exp (x * t)) := by
  have hf : (fun t => density lam t * Real.exp (x * t)) =
      (Icc (-endpoint lam) (endpoint lam)).indicator
        (fun t => (weight lam t * Real.exp (x * t)) / normalizer lam) := by
    funext t
    by_cases ht : t ∈ Icc (-endpoint lam) (endpoint lam)
    · simp only [density, indicator_of_mem ht]
      ring
    · simp [density, ht]
  rw [hf]
  apply (integrable_indicator_iff measurableSet_Icc).2
  have hc : Continuous (fun t : ℝ =>
      (weight lam t * Real.exp (x * t)) / normalizer lam) := by
    unfold weight
    fun_prop
  exact hc.integrableOn_Icc

/-- The second derivative is the actual iterated derivative of the prior potential. -/
theorem priorPotential_second_derivative {lam t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Ioo (-endpoint lam) (endpoint lam)) :
    deriv (deriv (priorPotential lam)) t = priorSecondDerivative lam t := by
  have heq : deriv (priorPotential lam) =ᶠ[𝓝 t] priorDerivative lam := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
    exact (hasDerivAt_priorPotential hlam hy).deriv
  rw [heq.deriv_eq]
  exact (hasDerivAt_priorDerivative hlam ht).deriv

/-- The curvature lower bound stated directly for the genuine second derivative. -/
theorem priorPotential_curvature {lam t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Ioo (-endpoint lam) (endpoint lam)) :
    curvatureConstant lam ≤ deriv (deriv (priorPotential lam)) t := by
  rw [priorPotential_second_derivative hlam ht]
  exact prior_curvature_lower_bound hlam ht

theorem weight_endpoint {lam : ℝ} (hlam : 0 < lam) : weight lam (endpoint lam) = 0 := by
  have hl0 := ne_of_gt hlam
  have harg : endpoint lam / (2 * lam) = Real.pi / 2 := by
    unfold endpoint
    field_simp
  unfold weight
  rw [harg, Real.cos_pi_div_two, mul_zero]

end

end TheoremA2.CosineReference
