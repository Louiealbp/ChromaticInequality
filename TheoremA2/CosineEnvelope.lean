import TheoremA2.ScalarExtension
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The genuine global cosine envelope used in Lemmas A.27 and A.28

We double-integrate the curvature `sec²` clamped at `±1/4`. This is the
paper's quadratic continuation of `-log cos`: a globally C², even function,
with actual second derivative between 1 and `sec²(1/4) < 16/15`.
-/

namespace TheoremA2.CosineEnvelope

open MeasureTheory Set TheoremA2.BrascampLieb
open scoped ContDiff

noncomputable section

def curvature (x : ℝ) : ℝ := 1 / Real.cos x ^ 2

def envelope (x : ℝ) : ℝ := scalarExtension curvature (1 / 4) x

def upperCurvature : ℝ := curvature (1 / 4)

theorem cos_pos_central {x : ℝ} (hx : |x| < Real.pi / 2) : 0 < Real.cos x :=
  Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)

theorem cos_pos_inner {x : ℝ} (hx : x ∈ Icc (-(1 / 4 : ℝ)) (1 / 4)) :
    0 < Real.cos x := by
  apply cos_pos_central
  have hp := Real.pi_gt_three
  have ha : |x| ≤ (1 / 4 : ℝ) := abs_le.mpr hx
  linarith

theorem curvature_even : Function.Even curvature := by
  intro x
  simp [curvature]

theorem continuousOn_curvature {b : ℝ} (hb : b < Real.pi / 2) :
    ContinuousOn curvature (Icc (-b) b) := by
  apply continuousOn_const.div (Real.continuous_cos.pow 2).continuousOn
  intro x hx
  have hc : 0 < Real.cos x := cos_pos_central (lt_of_le_of_lt (abs_le.mpr hx) hb)
  exact pow_ne_zero _ hc.ne'

theorem curvature_ge_one {x : ℝ} (hx : |x| < Real.pi / 2) : 1 ≤ curvature x := by
  have hc := cos_pos_central hx
  rw [curvature, le_div_iff₀ (sq_pos_of_pos hc)]
  simpa using Real.cos_sq_le_one x

theorem curvature_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y < Real.pi / 2) : curvature x ≤ curvature y := by
  have hp := Real.pi_pos
  have hc₁ : 0 < Real.cos x := cos_pos_central (by rw [abs_of_nonneg hx]; linarith)
  have hc₂ : 0 < Real.cos y := cos_pos_central (by rw [abs_of_nonneg (hx.trans hxy)]; exact hy)
  have hcos : Real.cos y ≤ Real.cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi hx (by linarith) hxy
  apply one_div_le_one_div_of_le (sq_pos_of_pos hc₂)
  exact sq_le_sq₀ hc₂.le hc₁.le |>.2 hcos

theorem curvature_le_upper {x : ℝ} (hx : x ∈ Icc (-(1 / 4 : ℝ)) (1 / 4)) :
    curvature x ≤ upperCurvature := by
  have he : curvature |x| = curvature x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, curvature_even]
  rw [← he]
  apply curvature_mono (abs_nonneg x) (abs_le.mpr hx)
  linarith [Real.pi_gt_three]

theorem upperCurvature_pos : 0 < upperCurvature := by
  unfold upperCurvature curvature
  exact one_div_pos.mpr (sq_pos_of_pos (cos_pos_inner (by norm_num)))

theorem upperCurvature_lt : upperCurvature < (16 / 15 : ℝ) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1 / 4 : ℝ))
  have hp : 0 < Real.cos (1 / 4 : ℝ) := cos_pos_inner (by norm_num)
  unfold upperCurvature curvature
  apply (div_lt_iff₀ (sq_pos_of_pos hp)).2
  nlinarith

theorem envelope_contDiff : ContDiff ℝ 2 envelope := by
  exact scalarExtension_contDiff (by norm_num)
    (continuousOn_curvature (by linarith [Real.pi_gt_three]))

theorem envelope_even : Function.Even envelope :=
  secondPrimitive_even (clampedCurvature_even (by norm_num) curvature_even)

@[simp] theorem envelope_zero : envelope 0 = 0 := by
  simp [envelope, scalarExtension]

@[simp] theorem deriv_envelope_zero : deriv envelope 0 = 0 := by
  unfold envelope scalarExtension
  rw [deriv_secondPrimitive (continuous_clampedCurvature (by norm_num)
      (continuousOn_curvature (by linarith [Real.pi_gt_three])))]
  exact firstPrimitive_zero _

theorem envelope_second_derivative (x : ℝ) :
    deriv (deriv envelope) x = curvature (clamp (1 / 4) x) :=
  scalarExtension_second_derivative (by norm_num)
    (continuousOn_curvature (by linarith [Real.pi_gt_three])) x

theorem envelope_curvature_lower (x : ℝ) : 1 ≤ deriv (deriv envelope) x := by
  rw [envelope_second_derivative]
  apply curvature_ge_one
  have hc := clamp_mem (by norm_num : (0 : ℝ) ≤ 1 / 4) x
  have ha := abs_le.mpr hc
  linarith [Real.pi_gt_three]

theorem envelope_curvature_upper (x : ℝ) :
    deriv (deriv envelope) x ≤ upperCurvature := by
  rw [envelope_second_derivative]
  exact curvature_le_upper (clamp_mem (by norm_num) x)

theorem envelope_quadratic_lower (x : ℝ) : x ^ 2 / 2 ≤ envelope x := by
  change x ^ 2 / 2 ≤ scalarExtension curvature (1 / 4) x
  simpa only [one_mul] using scalarExtension_quadratic_lower (H := (1 : ℝ)) (by norm_num)
    (continuousOn_curvature (by linarith [Real.pi_gt_three]))
    (fun t ht => curvature_ge_one (by
      have ha := abs_le.mpr ht
      linarith [Real.pi_gt_three])) x

theorem envelope_nonneg (x : ℝ) : 0 ≤ envelope x :=
  (div_nonneg (sq_nonneg x) (by norm_num)).trans (envelope_quadratic_lower x)

theorem envelope_quadratic_upper (x : ℝ) : envelope x ≤ upperCurvature * x ^ 2 / 2 := by
  have hq := continuous_clampedCurvature (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (continuousOn_curvature (by linarith [Real.pi_gt_three]))
  have h := secondPrimitive_nonneg
    (q := fun t => upperCurvature - clampedCurvature curvature (1 / 4) t)
    (fun t => sub_nonneg.mpr (curvature_le_upper (clamp_mem (by norm_num) t))) x
  rw [secondPrimitive_sub continuous_const hq, secondPrimitive_const] at h
  exact sub_nonneg.mp h

theorem hasDerivAt_neg_log_cos {x : ℝ} (hx : |x| < Real.pi / 2) :
    HasDerivAt (fun t => -Real.log (Real.cos t)) (Real.tan x) x := by
  rw [Real.tan_eq_sin_div_cos]
  have h := ((Real.hasDerivAt_cos x).log (cos_pos_central hx).ne').neg
  simp only [neg_div, neg_neg] at h
  exact h

theorem scalarExtension_eq_neg_log_cos {b x : ℝ} (hb : 0 ≤ b)
    (hbpi : b < Real.pi / 2) (hx : x ∈ Icc (-b) b) :
    scalarExtension curvature b x = -Real.log (Real.cos x) := by
  have hcos (t : ℝ) (ht : t ∈ Icc (-b) b) : 0 < Real.cos t :=
    cos_pos_central (lt_of_le_of_lt (abs_le.mpr ht) hbpi)
  have ht : ContinuousOn Real.tan (Icc (-b) b) := by
    intro t ht
    exact (Real.hasDerivAt_tan (hcos t ht).ne').continuousAt.continuousWithinAt
  have he := scalarExtension_eq_on_inner (U := fun t => -Real.log (Real.cos t))
    (U₁ := Real.tan) hb (continuousOn_curvature hbpi) ht
    (fun t ht => hasDerivAt_neg_log_cos (lt_of_le_of_lt (abs_le.mpr ht) hbpi))
    (fun t ht => Real.hasDerivAt_tan (hcos t ht).ne') hx
  simpa using he

/-- Exact agreement with `-log cos`, not a separately assumed comparison. -/
theorem envelope_eq_neg_log_cos {x : ℝ} (hx : |x| ≤ (1 / 4 : ℝ)) :
    envelope x = -Real.log (Real.cos x) :=
  scalarExtension_eq_neg_log_cos (by norm_num)
    (by linarith [Real.pi_gt_three]) (abs_le.mp hx)


theorem clamped_curvature_le {x : ℝ} (hx : 0 ≤ x) (hpi : x < Real.pi / 2) :
    clampedCurvature curvature (1 / 4) x ≤ curvature x := by
  unfold clampedCurvature
  by_cases hxb : x ≤ (1 / 4 : ℝ)
  · rw [clamp_eq_self (show x ∈ Icc (-(1 / 4 : ℝ)) (1 / 4) from ⟨by linarith, hxb⟩)]
  · rw [clamp_eq_right (by norm_num) (le_of_not_ge hxb)]
    exact curvature_mono (by norm_num) (le_of_not_ge hxb) hpi

theorem firstPrimitive_le_tan {x : ℝ} (hx : 0 ≤ x) (hpi : x < Real.pi / 2) :
    firstPrimitive (clampedCurvature curvature (1 / 4)) x ≤ Real.tan x := by
  have hq := continuous_clampedCurvature (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (continuousOn_curvature (by linarith [Real.pi_gt_three]))
  have hc : ContinuousOn curvature (Icc (0 : ℝ) x) :=
    (continuousOn_curvature hpi).mono (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
  have hci : IntervalIntegrable curvature volume 0 x := by
    apply hc.intervalIntegrable_of_Icc hx
  calc
    firstPrimitive (clampedCurvature curvature (1 / 4)) x ≤
        ∫ t in (0 : ℝ)..x, curvature t :=
      intervalIntegral.integral_mono_on hx (hq.intervalIntegrable 0 x) hci
        (fun t ht => clamped_curvature_le ht.1 (lt_of_le_of_lt ht.2 hpi))
    _ = Real.tan x - Real.tan 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        have ht' : t ∈ Icc (0 : ℝ) x := by simpa [uIcc_of_le hx] using ht
        exact Real.hasDerivAt_tan (cos_pos_central (by
          rw [abs_of_nonneg ht'.1]
          exact lt_of_le_of_lt ht'.2 hpi)).ne'
      · exact hci
    _ = Real.tan x := by simp

theorem envelope_le_neg_log_cos_nonneg {x : ℝ} (hx : 0 ≤ x)
    (hpi : x < Real.pi / 2) : envelope x ≤ -Real.log (Real.cos x) := by
  have hq := continuous_clampedCurvature (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (continuousOn_curvature (by linarith [Real.pi_gt_three]))
  have htan : ContinuousOn Real.tan (Icc (0 : ℝ) x) := by
    intro t ht
    exact (Real.hasDerivAt_tan (cos_pos_central (by
      rw [abs_of_nonneg ht.1]
      exact lt_of_le_of_lt ht.2 hpi)).ne').continuousAt.continuousWithinAt
  have hti : IntervalIntegrable Real.tan volume 0 x := htan.intervalIntegrable_of_Icc hx
  calc
    envelope x ≤ ∫ t in (0 : ℝ)..x, Real.tan t :=
      intervalIntegral.integral_mono_on hx
        ((continuous_firstPrimitive hq).intervalIntegrable 0 x) hti
        (fun t ht => firstPrimitive_le_tan ht.1 (lt_of_le_of_lt ht.2 hpi))
    _ = -Real.log (Real.cos x) - (-Real.log (Real.cos 0)) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        have ht' : t ∈ Icc (0 : ℝ) x := by simpa [uIcc_of_le hx] using ht
        exact hasDerivAt_neg_log_cos (by
          rw [abs_of_nonneg ht'.1]
          exact lt_of_le_of_lt ht'.2 hpi)
      · exact hti
    _ = -Real.log (Real.cos x) := by simp

/-- The quadratic continuation lies below `-log cos` on the whole open central cell. -/
theorem envelope_le_neg_log_cos {x : ℝ} (hx : |x| < Real.pi / 2) :
    envelope x ≤ -Real.log (Real.cos x) := by
  rcases le_total 0 x with h | h
  · exact envelope_le_neg_log_cos_nonneg h (by rwa [abs_of_nonneg h] at hx)
  · have hh := envelope_le_neg_log_cos_nonneg (neg_nonneg.mpr h)
      (by rwa [abs_of_nonpos h] at hx)
    simpa only [envelope_even x, Real.cos_neg] using hh

theorem exp_neg_envelope_pos (x : ℝ) : 0 < Real.exp (-envelope x) := Real.exp_pos _

theorem exp_neg_envelope_le_one (x : ℝ) : Real.exp (-envelope x) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (envelope_nonneg x)

theorem exp_neg_envelope_eq_cos {x : ℝ} (hx : |x| ≤ (1 / 4 : ℝ)) :
    Real.exp (-envelope x) = Real.cos x := by
  rw [envelope_eq_neg_log_cos hx, neg_neg, Real.exp_log (cos_pos_inner (abs_le.mp hx))]

theorem cos_le_exp_neg_envelope {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    Real.cos x ≤ Real.exp (-envelope x) := by
  rcases lt_or_eq_of_le hx with h | h
  · calc
      Real.cos x = Real.exp (Real.log (Real.cos x)) := (Real.exp_log (cos_pos_central h)).symm
      _ ≤ Real.exp (-envelope x) := Real.exp_le_exp.mpr (by linarith [envelope_le_neg_log_cos h])
  · have hc : Real.cos x = 0 := by
      rw [← Real.cos_abs, h, Real.cos_pi_div_two]
    rw [hc]
    exact (exp_neg_envelope_pos x).le


/-- The first derivative is the actual first primitive of the clamped curvature. -/
theorem envelope_hasDerivAt (x : ℝ) :
    HasDerivAt envelope (firstPrimitive (clampedCurvature curvature (1 / 4)) x) x :=
  hasDerivAt_secondPrimitive (continuous_clampedCurvature (by norm_num)
    (continuousOn_curvature (by linarith [Real.pi_gt_three]))) x

theorem deriv_envelope_eq (x : ℝ) :
    deriv envelope x = firstPrimitive (clampedCurvature curvature (1 / 4)) x :=
  (envelope_hasDerivAt x).deriv

/-- The score contribution grows at most linearly, with the actual curvature constant. -/
theorem abs_deriv_envelope_le (x : ℝ) :
    |deriv envelope x| ≤ upperCurvature * |x| := by
  have hq := continuous_clampedCurvature (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (continuousOn_curvature (by linarith [Real.pi_gt_three]))
  have hq0 (t : ℝ) : 0 ≤ clampedCurvature curvature (1 / 4) t := by
    unfold clampedCurvature curvature
    positivity
  have hqu (t : ℝ) : clampedCurvature curvature (1 / 4) t ≤ upperCurvature :=
    curvature_le_upper (clamp_mem (by norm_num) t)
  have hpos (t : ℝ) (ht : 0 ≤ t) :
      |firstPrimitive (clampedCurvature curvature (1 / 4)) t| ≤ upperCurvature * |t| := by
    rw [abs_of_nonneg (firstPrimitive_nonneg hq0 ht), abs_of_nonneg ht]
    calc
      _ ≤ ∫ _u in (0 : ℝ)..t, upperCurvature :=
        intervalIntegral.integral_mono_on ht (hq.intervalIntegrable 0 t)
          intervalIntegrable_const (fun u _ => hqu u)
      _ = upperCurvature * t := by simp [mul_comm]
  rw [deriv_envelope_eq]
  rcases le_total 0 x with hx | hx
  · exact hpos x hx
  · have hh := hpos (-x) (neg_nonneg.mpr hx)
    rw [firstPrimitive_odd (clampedCurvature_even (by norm_num) curvature_even),
      abs_neg, abs_neg] at hh
    exact hh

end

end TheoremA2.CosineEnvelope
