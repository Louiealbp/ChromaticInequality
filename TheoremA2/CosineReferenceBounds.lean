import TheoremA2.CosineReference
import TheoremA2.ScalarGaussianBounds

/-!
# Bounds for the actual positive cosine reference

A direct convolution argument replaces the ODE argument of Lemma A.32.
The clipped central cosine obeys an elementary symmetrized cosine inequality.
All integrals and changes of variables refer to the explicit construction.

`reference_ge_cos` proves equation (60), for every positive `lam`.
`reference_log_gap` proves both inequalities in equation (61), with the exact
constant `4 * sqrt lam * exp (-lam / 4)`, for `2 ≤ lam` and `|x| ≤ 1`.
The latter uses actual Gaussian-tail and normalizer estimates from
`ScalarGaussianBounds.lean`, whose proofs do not assume the desired reference
comparison. The direct integral proof does not invoke an ODE or omit any
boundary term from one. Together with `CosineReference.lean`, this establishes
the scalar reference estimates used by the intended Theorem A.2 proof; it does
not establish the joint covariance or periodic-cell comparisons.
-/

namespace TheoremA2.CosineReference

open MeasureTheory Set
open scoped Topology
noncomputable section

/-- Cosine on its central nonnegative interval, and zero elsewhere. -/
def truncatedCos (u : ℝ) : ℝ :=
  if |u| ≤ Real.pi / 2 then Real.cos u else 0

/-- The Gaussian kernel after rescaling the scalar prior. -/
def gaussianKernel (lam v : ℝ) : ℝ := Real.exp (-lam * v ^ 2)

/-- Convolution of the kernel with the truncated central cosine. -/
def cosineConvolution (lam x : ℝ) : ℝ :=
  ∫ v, gaussianKernel lam v * truncatedCos (v + x)

@[simp] theorem truncatedCos_neg (u : ℝ) : truncatedCos (-u) = truncatedCos u := by
  simp [truncatedCos]

theorem truncatedCos_nonneg (u : ℝ) : 0 ≤ truncatedCos u := by
  unfold truncatedCos
  split_ifs with h
  · exact Real.cos_nonneg_of_mem_Icc (abs_le.mp h)
  · exact le_rfl

theorem truncatedCos_le_one (u : ℝ) : truncatedCos u ≤ 1 := by
  unfold truncatedCos
  split_ifs
  · exact Real.cos_le_one u
  · norm_num

theorem measurable_truncatedCos : Measurable truncatedCos := by
  unfold truncatedCos
  exact Measurable.ite
    (isClosed_le continuous_abs continuous_const).measurableSet
    Real.continuous_cos.measurable measurable_const

theorem truncatedCos_eq_indicator : truncatedCos =
    (Icc (-(Real.pi / 2)) (Real.pi / 2)).indicator Real.cos := by
  funext u
  by_cases hu : |u| ≤ Real.pi / 2
  · simp [truncatedCos, hu, abs_le.mp hu]
  · have hnot : u ∉ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      simpa only [mem_Icc, ← abs_le] using hu
    simp [truncatedCos, hu, hnot]

/-- Within one full half-period, removing the noncentral cosine only increases it. -/
theorem cos_le_truncatedCos {u : ℝ} (hu : |u| ≤ Real.pi) :
    Real.cos u ≤ truncatedCos u := by
  by_cases hc : |u| ≤ Real.pi / 2
  · simp [truncatedCos, hc]
  · have hhalf : Real.pi / 2 ≤ |u| := le_of_lt (lt_of_not_ge hc)
    have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le hhalf
      (show |u| ≤ Real.pi + Real.pi / 2 by linarith [Real.pi_pos])
    simpa [truncatedCos, hc] using hcos

/-- The pointwise positivity mechanism underlying the central majorant. -/
theorem truncatedCos_symmetrized {x : ℝ} (hx : |x| ≤ Real.pi / 2) (v : ℝ) :
    2 * Real.cos x * truncatedCos v ≤ truncatedCos (v + x) + truncatedCos (v - x) := by
  by_cases hv : |v| ≤ Real.pi / 2
  · have hp : |v + x| ≤ Real.pi := le_trans (abs_add_le v x) (by linarith)
    have hm : |v - x| ≤ Real.pi := le_trans (abs_sub v x) (by linarith)
    have hpc := cos_le_truncatedCos hp
    have hmc := cos_le_truncatedCos hm
    have hc : Real.cos (v + x) + Real.cos (v - x) = 2 * Real.cos x * Real.cos v := by
      rw [Real.cos_add, Real.cos_sub]
      ring
    rw [truncatedCos, if_pos hv]
    linarith
  · rw [truncatedCos, if_neg hv]
    simpa using add_nonneg (truncatedCos_nonneg (v + x)) (truncatedCos_nonneg (v - x))

/-- Twice the symmetrized convolution error integrand. -/
def cosineDefect (x v : ℝ) : ℝ :=
  truncatedCos (v + x) + truncatedCos (v - x) - 2 * Real.cos x * truncatedCos v

theorem cosineDefect_nonneg {x : ℝ} (hx : |x| ≤ Real.pi / 2) (v : ℝ) :
    0 ≤ cosineDefect x v := by
  exact sub_nonneg.mpr (truncatedCos_symmetrized hx v)

theorem cosineDefect_le_two {x : ℝ} (hx : |x| ≤ Real.pi / 2) (v : ℝ) :
    cosineDefect x v ≤ 2 := by
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc (abs_le.mp hx)
  have h0 : 0 ≤ 2 * Real.cos x * truncatedCos v := by
    exact mul_nonneg (by positivity) (truncatedCos_nonneg v)
  unfold cosineDefect
  linarith [truncatedCos_le_one (v + x), truncatedCos_le_one (v - x)]

theorem cosineDefect_eq_zero {x v : ℝ} (hvx : |v| + |x| ≤ Real.pi / 2) :
    cosineDefect x v = 0 := by
  have hv : |v| ≤ Real.pi / 2 := by linarith [abs_nonneg x]
  have hp : |v + x| ≤ Real.pi / 2 := le_trans (abs_add_le v x) hvx
  have hm : |v - x| ≤ Real.pi / 2 := le_trans (abs_sub v x) hvx
  simp only [cosineDefect, truncatedCos, if_pos hv, if_pos hp, if_pos hm,
    Real.cos_add, Real.cos_sub]
  ring

theorem cosineDefect_eq_zero_of_small {x v : ℝ} (hx : |x| ≤ 1) (hv : |v| < 1 / 2) :
    cosineDefect x v = 0 := by
  apply cosineDefect_eq_zero
  linarith [Real.pi_gt_three]

theorem integrable_kernel_times_truncatedCos {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    Integrable (fun v => gaussianKernel lam v * truncatedCos (v + x)) := by
  have hm : Measurable (fun v : ℝ => gaussianKernel lam v * truncatedCos (v + x)) := by
    have hk : Measurable (gaussianKernel lam) := by unfold gaussianKernel; fun_prop
    exact hk.mul (measurable_truncatedCos.comp (by fun_prop))
  apply (integrable_exp_neg_mul_sq hlam).mono' hm.aestronglyMeasurable
  filter_upwards [] with v
  unfold gaussianKernel
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.exp_pos _).le,
    abs_of_nonneg (truncatedCos_nonneg (v + x))]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (truncatedCos_le_one (v + x))

@[simp] theorem cosineConvolution_neg (lam x : ℝ) :
    cosineConvolution lam (-x) = cosineConvolution lam x := by
  have h := integral_neg_eq_self
    (fun v : ℝ => gaussianKernel lam v * truncatedCos (v + x)) volume
  have hid (v : ℝ) : gaussianKernel lam (-v) * truncatedCos (-v + x) =
      gaussianKernel lam v * truncatedCos (v + -x) := by
    have he : -v + x = -(v + -x) := by ring
    rw [he, truncatedCos_neg]
    simp [gaussianKernel]
  simpa only [cosineConvolution, hid] using h

/-- Majorant inequality before dividing by the strictly positive central normalizer. -/
theorem cosineConvolution_majorant {lam x : ℝ} (hlam : 0 < lam)
    (hx : |x| ≤ Real.pi / 2) :
    Real.cos x * cosineConvolution lam 0 ≤ cosineConvolution lam x := by
  have hi0 := integrable_kernel_times_truncatedCos hlam 0
  have hip := integrable_kernel_times_truncatedCos hlam x
  have him := integrable_kernel_times_truncatedCos hlam (-x)
  have hp (v : ℝ) :
      2 * Real.cos x * (gaussianKernel lam v * truncatedCos (v + 0)) ≤
        gaussianKernel lam v * truncatedCos (v + x) +
          gaussianKernel lam v * truncatedCos (v + -x) := by
    have hh := mul_le_mul_of_nonneg_left (truncatedCos_symmetrized hx v)
      (Real.exp_pos (-lam * v ^ 2)).le
    simpa only [gaussianKernel, add_zero, sub_eq_add_neg, mul_add, mul_left_comm,
      mul_assoc] using hh
  have h := integral_mono (hi0.const_mul (2 * Real.cos x)) (hip.add him) hp
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add hip him] at h
  change 2 * Real.cos x * cosineConvolution lam 0 ≤
    cosineConvolution lam x + cosineConvolution lam (-x) at h
  rw [cosineConvolution_neg] at h
  linarith


/-- Translation expresses the convolution as an integral over the fixed central interval. -/
theorem cosineConvolution_eq_interval (lam x : ℝ) :
    cosineConvolution lam x =
      ∫ u in -(Real.pi / 2)..Real.pi / 2,
        gaussianKernel lam (u - x) * Real.cos u := by
  unfold cosineConvolution
  calc
    (∫ v, gaussianKernel lam v * truncatedCos (v + x)) =
        ∫ u, gaussianKernel lam (u - x) * truncatedCos u := by
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self
          (fun u : ℝ => gaussianKernel lam (u - x) * truncatedCos u) x
    _ = ∫ u in Icc (-(Real.pi / 2)) (Real.pi / 2),
        gaussianKernel lam (u - x) * Real.cos u := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : |u| ≤ Real.pi / 2
      · simp [truncatedCos, hu, abs_le.mp hu]
      · have hn : u ∉ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          simpa only [mem_Icc, ← abs_le] using hu
        simp [truncatedCos, hu, hn]
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

/-- Positivity of the central convolution normalizer. -/
theorem cosineConvolution_zero_pos (lam : ℝ) : 0 < cosineConvolution lam 0 := by
  rw [cosineConvolution_eq_interval]
  apply intervalIntegral.integral_pos (by linarith [Real.pi_pos])
    (by unfold gaussianKernel; fun_prop)
  · intro u hu
    exact mul_nonneg (Real.exp_pos _).le
      (Real.cos_nonneg_of_mem_Icc ⟨hu.1.le, hu.2⟩)
  · refine ⟨0, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, ?_⟩
    simp [gaussianKernel]

/-- Complete the Gaussian square and rescale the original moment integral. -/
theorem scaled_moment_eq_convolution {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    Real.exp (-lam * x ^ 2) * momentIntegral lam x =
      (2 * lam) * cosineConvolution lam x := by
  have hl0 := ne_of_gt hlam
  have hl20 : 2 * lam ≠ 0 := by positivity
  have hleft : -endpoint lam / (2 * lam) = -(Real.pi / 2) := by
    unfold endpoint
    field_simp
  have hright : endpoint lam / (2 * lam) = Real.pi / 2 := by
    unfold endpoint
    field_simp
  have hintegrand (t : ℝ) :
      Real.exp (-lam * x ^ 2) * (weight lam t * Real.exp (x * t)) =
        gaussianKernel lam (t / (2 * lam) - x) * Real.cos (t / (2 * lam)) := by
    unfold weight gaussianKernel
    calc
      _ = Real.exp ((-lam * x ^ 2) + (-(t ^ 2) / (4 * lam)) + x * t) *
          Real.cos (t / (2 * lam)) := by
        rw [Real.exp_add, Real.exp_add]
        ring
      _ = _ := by
        congr 2
        field_simp
        ring
  unfold momentIntegral
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [hintegrand]
  rw [intervalIntegral.integral_comp_div
      (fun u : ℝ => gaussianKernel lam (u - x) * Real.cos u) hl20,
    hleft, hright, cosineConvolution_eq_interval]
  rfl

/-- The original scalar reference and the normalized convolution are exactly equal. -/
theorem reference_eq_convolution {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    reference lam x = cosineConvolution lam x / cosineConvolution lam 0 := by
  have hn := scaled_moment_eq_convolution hlam 0
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Real.exp_zero, one_mul,
    momentIntegral_zero] at hn
  have hl0 := ne_of_gt hlam
  have hN0 := ne_of_gt (cosineConvolution_zero_pos lam)
  unfold reference
  rw [← mul_div_assoc, scaled_moment_eq_convolution hlam, hn]
  field_simp

/-- Equation (60), proved for the explicit reference by the direct convolution argument. -/
theorem reference_ge_cos {lam x : ℝ} (hlam : 0 < lam) (hx : |x| ≤ Real.pi / 2) :
    Real.cos x ≤ reference lam x := by
  rw [reference_eq_convolution hlam]
  exact (le_div_iff₀ (cosineConvolution_zero_pos lam)).2
    (cosineConvolution_majorant hlam hx)


/-- Integrability of the signed defect is proved from the three actual convolution terms. -/
theorem integrable_kernel_defect {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    Integrable (fun v => gaussianKernel lam v * cosineDefect x v) := by
  have hip := integrable_kernel_times_truncatedCos hlam x
  have him := integrable_kernel_times_truncatedCos hlam (-x)
  have hi0 := integrable_kernel_times_truncatedCos hlam 0
  convert (hip.add him).sub (hi0.const_mul (2 * Real.cos x)) using 1
  funext v
  simp only [Pi.sub_apply, Pi.add_apply, cosineDefect, add_zero, sub_eq_add_neg]
  ring

/-- Exact integrated defect identity; no tail or sign is discarded. -/
theorem integral_kernel_defect {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    (∫ v, gaussianKernel lam v * cosineDefect x v) =
      2 * (cosineConvolution lam x - Real.cos x * cosineConvolution lam 0) := by
  have hip := integrable_kernel_times_truncatedCos hlam x
  have him := integrable_kernel_times_truncatedCos hlam (-x)
  have hi0 := integrable_kernel_times_truncatedCos hlam 0
  have hf : (fun v => gaussianKernel lam v * cosineDefect x v) =
      (fun v => gaussianKernel lam v * truncatedCos (v + x) +
        gaussianKernel lam v * truncatedCos (v + -x) -
          (2 * Real.cos x) * (gaussianKernel lam v * truncatedCos (v + 0))) := by
    funext v
    unfold cosineDefect
    simp only [add_zero, sub_eq_add_neg]
    ring
  have hisum : Integrable (fun v =>
      gaussianKernel lam v * truncatedCos (v + x) +
        gaussianKernel lam v * truncatedCos (v + -x)) := by
    exact hip.add him
  rw [hf, integral_sub hisum (hi0.const_mul (2 * Real.cos x)),
    integral_add hip him, integral_const_mul]
  change cosineConvolution lam x + cosineConvolution lam (-x) -
    (2 * Real.cos x) * cosineConvolution lam 0 = _
  rw [cosineConvolution_neg]
  ring

/-- The central error is bounded by the actual Gaussian tail outside `[-1/2,1/2]`. -/
theorem cosineConvolution_error_le_tail {lam x : ℝ} (hlam : 0 < lam) (hx : |x| ≤ 1) :
    cosineConvolution lam x - Real.cos x * cosineConvolution lam 0 ≤
      ∫ v in {v : ℝ | (1 / 2 : ℝ) ≤ |v|}, gaussianKernel lam v := by
  let T : Set ℝ := {v : ℝ | (1 / 2 : ℝ) ≤ |v|}
  have hT : MeasurableSet T := (isClosed_le continuous_const continuous_abs).measurableSet
  have hk : Integrable (gaussianKernel lam) := integrable_exp_neg_mul_sq hlam
  have htail := (hk.indicator hT).const_mul (2 : ℝ)
  have hcentral : |x| ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hp (v : ℝ) : gaussianKernel lam v * cosineDefect x v ≤
      2 * T.indicator (gaussianKernel lam) v := by
    by_cases hv : v ∈ T
    · rw [indicator_of_mem hv]
      have hh := mul_le_mul_of_nonneg_left (cosineDefect_le_two hcentral v)
        (Real.exp_pos (-lam * v ^ 2)).le
      simpa only [gaussianKernel, mul_comm] using hh
    · rw [indicator_of_notMem hv]
      have hs : |v| < 1 / 2 := lt_of_not_ge hv
      rw [cosineDefect_eq_zero_of_small hx hs]
      simp
  have h := integral_mono (integrable_kernel_defect hlam x) htail hp
  rw [integral_kernel_defect hlam, integral_const_mul,
    integral_indicator hT] at h
  dsimp [T] at h
  linarith

/-- At zero the convolution is precisely the positive central Gaussian-cosine integral. -/
theorem cosineConvolution_zero_eq_setIntegral (lam : ℝ) :
    cosineConvolution lam 0 =
      ∫ v in Icc (-(Real.pi / 2)) (Real.pi / 2), Real.exp (-lam * v ^ 2) * Real.cos v := by
  rw [cosineConvolution_eq_interval]
  simp only [sub_zero, gaussianKernel]
  rw [integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

/-- The central numerator error has the precise Gaussian-tail scale used below. -/
theorem cosineConvolution_error_le_exp {lam x : ℝ} (hlam : 2 ≤ lam) (hx : |x| ≤ 1) :
    cosineConvolution lam x - Real.cos x * cosineConvolution lam 0 ≤
      Real.exp (-lam / 4) := by
  exact le_trans (cosineConvolution_error_le_tail (by linarith) hx)
    (ScalarGaussianBounds.gaussian_tail_half hlam)

/-- A concrete quantitative lower bound for the actual central normalizer. -/
theorem cosineConvolution_zero_lower {lam : ℝ} (hlam : 2 ≤ lam) :
    1 / (2 * Real.sqrt lam) ≤ cosineConvolution lam 0 := by
  rw [cosineConvolution_zero_eq_setIntegral]
  exact ScalarGaussianBounds.gaussian_cosine_normalizer_lower hlam

/-- An additive error estimate for the explicit scalar reference on `[-1,1]`. -/
theorem reference_sub_cos_le {lam x : ℝ} (hlam : 2 ≤ lam) (hx : |x| ≤ 1) :
    reference lam x - Real.cos x ≤ 2 * Real.sqrt lam * Real.exp (-lam / 4) := by
  have hl : 0 < lam := by linarith
  have hs : 0 < 2 * Real.sqrt lam := mul_pos (by norm_num) (Real.sqrt_pos.2 hl)
  have hN := cosineConvolution_zero_pos lam
  have hnorm := (div_le_iff₀ hs).mp (cosineConvolution_zero_lower hlam)
  have he := mul_le_mul_of_nonneg_right hnorm (Real.exp_pos (-lam / 4)).le
  have hdiff := cosineConvolution_error_le_exp hlam hx
  have hid : reference lam x - Real.cos x =
      (cosineConvolution lam x - Real.cos x * cosineConvolution lam 0) /
        cosineConvolution lam 0 := by
    rw [reference_eq_convolution hl]
    field_simp
  rw [hid]
  apply (div_le_iff₀ hN).2
  nlinarith

/-- The cosine is uniformly positive on the interval used for the logarithmic error. -/
theorem half_le_cos_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    (1 / 2 : ℝ) ≤ Real.cos x := by
  have hsq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

/-- Equation (61): the exact two-sided logarithmic error, with the paper's constant.

This is proved from the explicit integral construction, the symmetrized clipping
identity, and elementary Gaussian estimates. No differential equation or comparison
principle is assumed.
-/
theorem reference_log_gap {lam x : ℝ} (hlam : 2 ≤ lam) (hx : |x| ≤ 1) :
    0 ≤ Real.log (reference lam x) - Real.log (Real.cos x) ∧
      Real.log (reference lam x) - Real.log (Real.cos x) ≤
        4 * Real.sqrt lam * Real.exp (-lam / 4) := by
  have hl : 0 < lam := by linarith
  have hc : 0 < Real.cos x := lt_of_lt_of_le (by norm_num) (half_le_cos_of_abs_le_one hx)
  have hF : 0 < reference lam x := reference_pos hl x
  have hcentral : |x| ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmajorant := reference_ge_cos hl hcentral
  constructor
  · exact sub_nonneg.mpr ((Real.log_le_log_iff hc hF).2 hmajorant)
  · have hadd := reference_sub_cos_le hlam hx
    have hd : 0 ≤ 4 * Real.sqrt lam * Real.exp (-lam / 4) := by positivity
    have hcosbound := mul_le_mul_of_nonneg_right (half_le_cos_of_abs_le_one hx) hd
    have hratio : reference lam x / Real.cos x ≤
        1 + 4 * Real.sqrt lam * Real.exp (-lam / 4) := by
      apply (div_le_iff₀ hc).2
      nlinarith
    have hlog := Real.log_le_sub_one_of_pos (div_pos hF hc)
    rw [Real.log_div (ne_of_gt hF) (ne_of_gt hc)] at hlog
    linarith

end
end TheoremA2.CosineReference
