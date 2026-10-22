import TheoremA2.PaddedDecoder
import TheoremA2.GaussianTail

set_option maxHeartbeats 800000

/-!
# The Gaussian expected loss of the actual padded decoder

This module proves equation (40) for the explicitly normalized decoder,
including every centered Gaussian variance below the stated variance proxy.
-/

namespace TheoremA2.PaddedDecoder

open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
noncomputable section

/-- The actual standard-Gaussian quadratic cost is integrable. -/
theorem integrable_gaussian_cost :
    Integrable (fun z : ℝ => z ^ 2 + Real.log 3) (gaussianReal 0 1) := by
  exact (memLp_id_gaussianReal 2).integrable_sq.add (integrable_const _)

/-- Finiteness of expected loss follows from the proved pointwise quadratic domination. -/
theorem integrable_loss_scaled_noise {v x s : ℝ} (hv : 0 < v)
    (hvsmall : v ≤ 1 / 1000000) (hx : |x| ≤ Real.pi / 2) (hsq : s ^ 2 ≤ v) :
    Integrable (fun z : ℝ => loss v 0 (x + s * z)) (gaussianReal 0 1) := by
  have hv1 : v ≤ 1 := by linarith
  have hm : Measurable (fun z : ℝ => loss v 0 (x + s * z)) :=
    (measurable_loss hv hv1 0).comp (by fun_prop)
  apply integrable_gaussian_cost.mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (loss_nonneg hv hv1 0 _)]
  exact loss_scaled_noise_le_cost hv hvsmall hx hsq z

/-- Combine a deterministic good-event estimate with the genuine Gaussian quadratic tail. -/
theorem expected_loss_le_good_bad {v x s t A : ℝ} (hv : 0 < v)
    (hvsmall : v ≤ 1 / 1000000) (hx : |x| ≤ Real.pi / 2)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ v) (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hgood : ∀ n : ℝ, |n| ≤ t → loss v 0 (x + n) ≤ A) :
    (∫ z : ℝ, loss v 0 (x + s * z) ∂gaussianReal 0 1) ≤
      A + 8 * Real.exp (-(t ^ 2) / (4 * v)) := by
  have hroot : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hsroot : s ≤ Real.sqrt v := by
    nlinarith [Real.sq_sqrt hv.le, Real.sqrt_nonneg v]
  let T := {z : ℝ | t / Real.sqrt v < |z|}
  have hT : MeasurableSet T := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hp (z : ℝ) : loss v 0 (x + s * z) ≤
      A + T.indicator (fun z : ℝ => z ^ 2 + Real.log 3) z := by
    by_cases hz : z ∈ T
    · rw [indicator_of_mem hz]
      linarith [loss_scaled_noise_le_cost hv hvsmall hx hsq z]
    · rw [indicator_of_notMem hz, add_zero]
      have hzle : |z| ≤ t / Real.sqrt v := le_of_not_gt hz
      have hn : |s * z| ≤ t := by
        rw [abs_mul, abs_of_nonneg hs]
        calc
          s * |z| ≤ Real.sqrt v * (t / Real.sqrt v) :=
            mul_le_mul hsroot hzle (abs_nonneg z) hroot.le
          _ = t := by field_simp
      exact hgood (s * z) hn
  have hl := integrable_loss_scaled_noise hv hvsmall hx hsq
  have hbad := integrable_gaussian_cost.indicator hT
  have h := integral_mono hl ((integrable_const A).add hbad) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const A) hbad] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  have htail := GaussianTail.quadratic_tail (t := t / Real.sqrt v) (by positivity)
  have hexponent : -((t / Real.sqrt v) ^ 2) / 4 = -(t ^ 2) / (4 * v) := by
    rw [div_pow, Real.sq_sqrt hv.le]
    ring
  rw [hexponent] at htail
  dsimp [T] at h
  linarith

/-- The precise exponential error bound for offsets of absolute value at most `1.5`. -/
theorem expected_loss_small_offset {v x s : ℝ} (hv : 0 < v)
    (hvsmall : v ≤ 1 / 1000000) (hx : |x| ≤ 3 / 2)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ v) :
    (∫ z : ℝ, loss v 0 (x + s * z) ∂gaussianReal 0 1) ≤
      16 * Real.exp (-(1 / 100000 : ℝ) / v) := by
  have hv1 : v ≤ 1 := by linarith
  have hxcentral : |x| ≤ Real.pi / 2 := hx.trans (by linarith [Real.pi_gt_three])
  have h := expected_loss_le_good_bad hv hvsmall hxcentral hs hsq
    (t := 1 / 100) (A := 4 * Real.exp (-(9 / 10000 : ℝ) / v))
    (by norm_num) (by positivity) (by
      intro n hn
      apply loss_small_observation hv hv1
      linarith [abs_add_le x n])
  have hsmall : Real.exp (-(9 / 10000 : ℝ) / v) ≤
      Real.exp (-(1 / 100000 : ℝ) / v) := by
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hv.le
    norm_num
  have htail : Real.exp (-((1 / 100 : ℝ) ^ 2) / (4 * v)) ≤
      Real.exp (-(1 / 100000 : ℝ) / v) := by
    apply Real.exp_le_exp.2
    rw [show -((1 / 100 : ℝ) ^ 2) / (4 * v) = -(1 / 40000 : ℝ) / v by ring]
    apply div_le_div_of_nonneg_right _ hv.le
    norm_num
  nlinarith [Real.exp_pos (-(1 / 100000 : ℝ) / v)]

/-- A convenient rigorous numerical logarithm bound. -/
theorem log_two_le_three_quarters : Real.log 2 ≤ (3 / 4 : ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).2
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)
  norm_num at h ⊢
  linarith

/-- A quadratic exponential lower bound suffices for both remaining tiny tails. -/
theorem exp_neg_le_ten_thousandth {y : ℝ} (hy : 200 ≤ y) :
    Real.exp (-y) ≤ (1 / 10000 : ℝ) := by
  have he : 10000 ≤ Real.exp y := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ y by linarith)
    nlinarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).2 (by linarith)

/-- Boundary offsets have bounded expected loss, strictly below the permitted quadratic cost. -/
theorem expected_loss_boundary_offset {v x s : ℝ} (hv : 0 < v)
    (hvsmall : v ≤ 1 / 1000000) (hx : |x| ≤ Real.pi / 2)
    (hxlarge : 3 / 2 ≤ |x|) (hs : 0 ≤ s) (hsq : s ^ 2 ≤ v) :
    (∫ z : ℝ, loss v 0 (x + s * z) ∂gaussianReal 0 1) ≤
      (27 / 80 : ℝ) * x ^ 2 := by
  have hv1 : v ≤ 1 := by linarith
  have h := expected_loss_le_good_bad hv hvsmall hx hs hsq
    (t := 29 / 1000) (A := Real.log 2 + 2 * Real.exp (-(9 / 4 : ℝ) / v))
    (by norm_num) (by positivity) (by
      intro n hn
      rw [loss_eq hv hv1]
      simp only [Int.cast_zero, mul_zero, sub_zero]
      rw [paddingDistance_eq_zero (show |x + n| ≤ 8 / 5 by
        linarith [abs_add_le x n, Real.pi_lt_d4])]
      simpa using log_denominator_le hv hv1 (x + n))
  have he1 : Real.exp (-(9 / 4 : ℝ) / v) ≤ 1 / 10000 := by
    rw [show -(9 / 4 : ℝ) / v = -((9 / 4 : ℝ) / v) by ring]
    apply exp_neg_le_ten_thousandth
    apply (le_div_iff₀ hv).2
    linarith
  have he2 : Real.exp (-((29 / 1000 : ℝ) ^ 2) / (4 * v)) ≤ 1 / 10000 := by
    rw [show -((29 / 1000 : ℝ) ^ 2) / (4 * v) = -((841 / 4000000 : ℝ) / v) by ring]
    apply exp_neg_le_ten_thousandth
    apply (le_div_iff₀ hv).2
    linarith
  have hxsq : (9 / 4 : ℝ) ≤ x ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) hxlarge 2
    norm_num [sq_abs] at hh
    exact hh
  linarith [log_two_le_three_quarters]

/-- Equation (40), for the actual decoder and an arbitrary standard-Gaussian scaling.
The scaling `s=0` includes the zero-variance Gaussian. -/
theorem expected_loss_scaled_noise {v x s : ℝ} (hv : 0 < v)
    (hvsmall : v ≤ 1 / 1000000) (hx : |x| ≤ Real.pi / 2)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ v) :
    (∫ z : ℝ, loss v 0 (x + s * z) ∂gaussianReal 0 1) ≤
      (27 / 80 : ℝ) * x ^ 2 + 16 * Real.exp (-(1 / 100000 : ℝ) / v) := by
  rcases le_total |x| (3 / 2) with hsmall | hlarge
  · have h := expected_loss_small_offset hv hvsmall hsmall hs hsq
    nlinarith [sq_nonneg x]
  · have h := expected_loss_boundary_offset hv hvsmall hx hlarge hs hsq
    linarith [Real.exp_pos (-(1 / 100000 : ℝ) / v)]

/-- The decoder bound holds for every integer period, not just the central label. -/
theorem expected_loss_integer_period {v x s : ℝ} (hv : 0 < v)
    (hvsmall : v ≤ 1 / 1000000) (k : ℤ) (hx : |x| ≤ Real.pi / 2)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ v) :
    (∫ z : ℝ, loss v k (Real.pi * k + x + s * z) ∂gaussianReal 0 1) ≤
      (27 / 80 : ℝ) * x ^ 2 + 16 * Real.exp (-(1 / 100000 : ℝ) / v) := by
  have hid (z : ℝ) : loss v k (Real.pi * k + x + s * z) = loss v 0 (x + s * z) := by
    simpa [add_comm, add_left_comm, add_assoc] using loss_add_period v (x + s * z) k 0
  simp_rw [hid]
  exact expected_loss_scaled_noise hv hvsmall hx hs hsq

/-- Every centered Gaussian, including a Dirac law, is the corresponding scaling of a standard one. -/
theorem gaussianReal_sqrt_map (w : ℝ≥0) :
    (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (w : ℝ) * z) = gaussianReal 0 w := by
  have hsq : NNReal.mk (Real.sqrt (w : ℝ) ^ 2) (sq_nonneg _) = w := by
    apply NNReal.eq
    exact Real.sq_sqrt w.coe_nonneg
  have hm := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt (w : ℝ))
  simp only [mul_zero, mul_one] at hm
  rw [hsq] at hm
  exact hm

/-- Equation (40), directly for the actual centered Gaussian law of any allowed variance. -/
theorem expected_loss_gaussian {v x : ℝ} (hv : 0 < v)
    (hvsmall : v ≤ 1 / 1000000) (w : ℝ≥0) (hw : (w : ℝ) ≤ v)
    (k : ℤ) (hx : |x| ≤ Real.pi / 2) :
    (∫ n : ℝ, loss v k (Real.pi * k + x + n) ∂gaussianReal 0 w) ≤
      (27 / 80 : ℝ) * x ^ 2 + 16 * Real.exp (-(1 / 100000 : ℝ) / v) := by
  have hv1 : v ≤ 1 := by linarith
  have hm : Measurable (fun n : ℝ => loss v k (Real.pi * k + x + n)) :=
    (measurable_loss hv hv1 k).comp (by fun_prop)
  rw [← gaussianReal_sqrt_map w, integral_map (by fun_prop) hm.aestronglyMeasurable]
  exact expected_loss_integer_period hv hvsmall k hx (Real.sqrt_nonneg _)
    (by simpa only [Real.sq_sqrt w.coe_nonneg] using hw)

/-- Integrability for the direct arbitrary-variance formulation, not merely a default integral value. -/
theorem integrable_loss_gaussian {v x : ℝ} (hv : 0 < v)
    (hvsmall : v ≤ 1 / 1000000) (w : ℝ≥0) (hw : (w : ℝ) ≤ v)
    (k : ℤ) (hx : |x| ≤ Real.pi / 2) :
    Integrable (fun n : ℝ => loss v k (Real.pi * k + x + n)) (gaussianReal 0 w) := by
  have hv1 : v ≤ 1 := by linarith
  have hm : Measurable (fun n : ℝ => loss v k (Real.pi * k + x + n)) :=
    (measurable_loss hv hv1 k).comp (by fun_prop)
  rw [← gaussianReal_sqrt_map w]
  apply (integrable_map_measure hm.aestronglyMeasurable (by fun_prop)).2
  have hbase := integrable_loss_scaled_noise hv hvsmall hx
    (s := Real.sqrt (w : ℝ)) (by simpa only [Real.sq_sqrt w.coe_nonneg] using hw)
  convert hbase using 1
  funext z
  simpa [Function.comp_def, add_comm, add_left_comm, add_assoc] using
    loss_add_period v (x + Real.sqrt (w : ℝ) * z) k 0

end
end TheoremA2.PaddedDecoder
