import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Tactic

/-!
# Genuine globally C² extensions from clamped curvature

The construction integrates a continuous, clamped second derivative twice.
It supplies actual derivative identities, a uniform quadratic lower bound,
and exact agreement with the original potential on the inner interval.
No extension theorem or convexity certificate is postulated.
-/

namespace TheoremA2.BrascampLieb

open MeasureTheory Set
open scoped Topology ContDiff

noncomputable section

def firstPrimitive (q : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, q t

def secondPrimitive (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, firstPrimitive q t

@[simp] theorem firstPrimitive_zero (q : ℝ → ℝ) : firstPrimitive q 0 = 0 := by
  simp [firstPrimitive]

@[simp] theorem secondPrimitive_zero (q : ℝ → ℝ) : secondPrimitive q 0 = 0 := by
  simp [secondPrimitive]

theorem hasDerivAt_firstPrimitive {q : ℝ → ℝ} (hq : Continuous q) (x : ℝ) :
    HasDerivAt (firstPrimitive q) (q x) x :=
  intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable 0 x)
    hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt

theorem differentiable_firstPrimitive {q : ℝ → ℝ} (hq : Continuous q) :
    Differentiable ℝ (firstPrimitive q) :=
  fun x => (hasDerivAt_firstPrimitive hq x).differentiableAt

theorem continuous_firstPrimitive {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (firstPrimitive q) := (differentiable_firstPrimitive hq).continuous

theorem deriv_firstPrimitive {q : ℝ → ℝ} (hq : Continuous q) :
    deriv (firstPrimitive q) = q := by
  funext x
  exact (hasDerivAt_firstPrimitive hq x).deriv

theorem hasDerivAt_secondPrimitive {q : ℝ → ℝ} (hq : Continuous q) (x : ℝ) :
    HasDerivAt (secondPrimitive q) (firstPrimitive q x) x :=
  hasDerivAt_firstPrimitive (continuous_firstPrimitive hq) x

theorem deriv_secondPrimitive {q : ℝ → ℝ} (hq : Continuous q) :
    deriv (secondPrimitive q) = firstPrimitive q :=
  deriv_firstPrimitive (continuous_firstPrimitive hq)

theorem second_deriv_secondPrimitive {q : ℝ → ℝ} (hq : Continuous q) :
    deriv (deriv (secondPrimitive q)) = q := by
  rw [deriv_secondPrimitive hq, deriv_firstPrimitive hq]

theorem contDiff_secondPrimitive {q : ℝ → ℝ} (hq : Continuous q) :
    ContDiff ℝ 2 (secondPrimitive q) := by
  have hfirst : ContDiff ℝ 1 (firstPrimitive q) := by
    apply contDiff_one_iff_deriv.mpr
    exact ⟨differentiable_firstPrimitive hq, by rw [deriv_firstPrimitive hq]; exact hq⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_secondPrimitive hq x).differentiableAt, ?_, ?_⟩
  · simp
  · rw [deriv_secondPrimitive hq]
    exact hfirst

theorem firstPrimitive_nonneg {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ firstPrimitive q x :=
  intervalIntegral.integral_nonneg_of_forall hx hq

theorem firstPrimitive_nonpos {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t)
    {x : ℝ} (hx : x ≤ 0) : firstPrimitive q x ≤ 0 := by
  have h := intervalIntegral.integral_nonneg_of_forall (f := q) (μ := volume) hx hq
  rw [intervalIntegral.integral_symm] at h
  exact neg_nonneg.mp h

theorem secondPrimitive_nonneg {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (x : ℝ) :
    0 ≤ secondPrimitive q x := by
  rcases le_total 0 x with hx | hx
  · exact intervalIntegral.integral_nonneg hx
      (fun t ht => firstPrimitive_nonneg hq ht.1)
  · unfold secondPrimitive
    rw [intervalIntegral.integral_symm]
    have h := intervalIntegral.integral_nonneg (f := fun t => -firstPrimitive q t)
      (μ := volume) hx
      (fun t ht => neg_nonneg.mpr (firstPrimitive_nonpos hq ht.2))
    rwa [intervalIntegral.integral_neg] at h

theorem firstPrimitive_sub {q r : ℝ → ℝ} (hq : Continuous q) (hr : Continuous r) (x : ℝ) :
    firstPrimitive (fun t => q t - r t) x = firstPrimitive q x - firstPrimitive r x :=
  intervalIntegral.integral_sub (hq.intervalIntegrable 0 x) (hr.intervalIntegrable 0 x)

theorem secondPrimitive_sub {q r : ℝ → ℝ} (hq : Continuous q) (hr : Continuous r) (x : ℝ) :
    secondPrimitive (fun t => q t - r t) x = secondPrimitive q x - secondPrimitive r x := by
  unfold secondPrimitive
  simp_rw [firstPrimitive_sub hq hr]
  exact intervalIntegral.integral_sub
    ((continuous_firstPrimitive hq).intervalIntegrable 0 x)
    ((continuous_firstPrimitive hr).intervalIntegrable 0 x)

theorem secondPrimitive_const (H x : ℝ) :
    secondPrimitive (fun _ => H) x = H * x ^ 2 / 2 := by
  simp only [secondPrimitive, firstPrimitive, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  rw [intervalIntegral.integral_mul_const, integral_id]
  ring

theorem secondPrimitive_quadratic_lower {q : ℝ → ℝ} (hq : Continuous q)
    {H : ℝ} (hH : ∀ t, H ≤ q t) (x : ℝ) :
    H * x ^ 2 / 2 ≤ secondPrimitive q x := by
  have h := secondPrimitive_nonneg (q := fun t => q t - H)
    (fun t => sub_nonneg.mpr (hH t)) x
  rw [secondPrimitive_sub hq continuous_const, secondPrimitive_const] at h
  exact sub_nonneg.mp h

theorem firstPrimitive_odd {q : ℝ → ℝ} (hq : Function.Even q) (x : ℝ) :
    firstPrimitive q (-x) = -firstPrimitive q x := by
  have h := intervalIntegral.integral_comp_neg (f := q) (a := 0) (b := x)
  have heven (t : ℝ) : q (-t) = q t := hq t
  simp only [neg_zero, heven] at h
  unfold firstPrimitive
  calc
    _ = -(∫ t in (-x)..(0 : ℝ), q t) := intervalIntegral.integral_symm (-x) 0
    _ = _ := by rw [← h]

theorem secondPrimitive_even {q : ℝ → ℝ} (hq : Function.Even q) :
    Function.Even (secondPrimitive q) := by
  intro x
  have h := intervalIntegral.integral_comp_neg (f := firstPrimitive q) (a := 0) (b := x)
  simp only [neg_zero, firstPrimitive_odd hq, intervalIntegral.integral_neg] at h
  unfold secondPrimitive
  calc
    _ = -(∫ t in (-x)..(0 : ℝ), firstPrimitive q t) := intervalIntegral.integral_symm (-x) 0
    _ = _ := by rw [← h, neg_neg]

theorem secondPrimitive_monotoneOn_nonneg {q : ℝ → ℝ} (hq : Continuous q)
    (hq0 : ∀ t, 0 ≤ q t) : MonotoneOn (secondPrimitive q) (Ici 0) := by
  have hd : Differentiable ℝ (secondPrimitive q) :=
    fun x => (hasDerivAt_secondPrimitive hq x).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hd.continuous.continuousOn
    hd.differentiableOn
  intro x hx
  rw [deriv_secondPrimitive hq]
  have hxpos : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  exact firstPrimitive_nonneg hq0 hxpos.le

theorem secondPrimitive_boundary_lower {q : ℝ → ℝ} (hq : Continuous q)
    (hq0 : ∀ t, 0 ≤ q t) (hqe : Function.Even q) {b x : ℝ}
    (hb : 0 ≤ b) (hx : b ≤ |x|) : secondPrimitive q b ≤ secondPrimitive q x := by
  have h := secondPrimitive_monotoneOn_nonneg hq hq0 hb (abs_nonneg x) hx
  have he : secondPrimitive q |x| = secondPrimitive q x := by
    rcases le_total 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]
    · rw [abs_of_nonpos hx0, secondPrimitive_even hqe]
  rwa [he] at h

/-- Clamping to the actual inner interval. -/
def clamp (b x : ℝ) : ℝ := max (-b) (min b x)

theorem continuous_clamp (b : ℝ) : Continuous (clamp b) := by
  unfold clamp
  fun_prop

theorem clamp_mem {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : clamp b x ∈ Icc (-b) b := by
  refine ⟨le_max_left _ _, max_le ?_ (min_le_left _ _)⟩
  linarith

theorem clamp_eq_self {b x : ℝ} (hx : x ∈ Icc (-b) b) : clamp b x = x := by
  rw [clamp, min_eq_right hx.2, max_eq_right hx.1]

theorem clamp_eq_left {b x : ℝ} (hb : 0 ≤ b) (hx : x ≤ -b) : clamp b x = -b := by
  rw [clamp, min_eq_right (show x ≤ b by linarith), max_eq_left hx]

theorem clamp_eq_right {b x : ℝ} (hb : 0 ≤ b) (hx : b ≤ x) : clamp b x = b := by
  rw [clamp, min_eq_left hx, max_eq_right (show -b ≤ b by linarith)]

theorem clamp_neg {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : clamp b (-x) = -clamp b x := by
  rcases le_total x (-b) with hx | hx
  · rw [clamp_eq_left hb hx, clamp_eq_right hb (by linarith), neg_neg]
  · rcases le_total b x with hx' | hx'
    · rw [clamp_eq_right hb hx', clamp_eq_left hb (by linarith)]
    · rw [clamp_eq_self ⟨hx, hx'⟩,
        clamp_eq_self (show -x ∈ Icc (-b) b from ⟨by linarith, by linarith⟩)]

def clampedCurvature (q : ℝ → ℝ) (b x : ℝ) : ℝ := q (clamp b x)

theorem continuous_clampedCurvature {q : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hq : ContinuousOn q (Icc (-b) b)) : Continuous (clampedCurvature q b) :=
  hq.comp_continuous (continuous_clamp b) (fun x => clamp_mem hb x)

theorem clampedCurvature_even {q : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hq : Function.Even q) : Function.Even (clampedCurvature q b) := by
  intro x
  simp only [clampedCurvature, clamp_neg hb]
  exact hq _

/-- The extension is a concrete double integral of the clamped curvature. -/
def scalarExtension (q : ℝ → ℝ) (b x : ℝ) : ℝ :=
  secondPrimitive (clampedCurvature q b) x

theorem scalarExtension_contDiff {q : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hq : ContinuousOn q (Icc (-b) b)) : ContDiff ℝ 2 (scalarExtension q b) :=
  contDiff_secondPrimitive (continuous_clampedCurvature hb hq)

theorem scalarExtension_second_derivative {q : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hq : ContinuousOn q (Icc (-b) b)) (x : ℝ) :
    deriv (deriv (scalarExtension q b)) x = q (clamp b x) :=
  congrFun (second_deriv_secondPrimitive (continuous_clampedCurvature hb hq)) x

theorem scalarExtension_curvature_lower {q : ℝ → ℝ} {b H : ℝ} (hb : 0 ≤ b)
    (hq : ContinuousOn q (Icc (-b) b)) (hH : ∀ t ∈ Icc (-b) b, H ≤ q t) (x : ℝ) :
    H ≤ deriv (deriv (scalarExtension q b)) x := by
  rw [scalarExtension_second_derivative hb hq]
  exact hH _ (clamp_mem hb x)

theorem scalarExtension_curvature_upper {q : ℝ → ℝ} {b H : ℝ} (hb : 0 ≤ b)
    (hq : ContinuousOn q (Icc (-b) b)) (hH : ∀ t ∈ Icc (-b) b, q t ≤ H) (x : ℝ) :
    deriv (deriv (scalarExtension q b)) x ≤ H := by
  rw [scalarExtension_second_derivative hb hq]
  exact hH _ (clamp_mem hb x)

theorem scalarExtension_quadratic_lower {q : ℝ → ℝ} {b H : ℝ} (hb : 0 ≤ b)
    (hq : ContinuousOn q (Icc (-b) b)) (hH : ∀ t ∈ Icc (-b) b, H ≤ q t) (x : ℝ) :
    H * x ^ 2 / 2 ≤ scalarExtension q b x :=
  secondPrimitive_quadratic_lower (continuous_clampedCurvature hb hq)
    (fun t => hH _ (clamp_mem hb t)) x

theorem firstPrimitive_clamped_eq {U₁ q : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hq : ContinuousOn q (Icc (-b) b))
    (hderiv : ∀ t ∈ Icc (-b) b, HasDerivAt U₁ (q t) t)
    {x : ℝ} (hx : x ∈ Icc (-b) b) :
    firstPrimitive (clampedCurvature q b) x = U₁ x - U₁ 0 := by
  have hsub : uIcc (0 : ℝ) x ⊆ Icc (-b) b :=
    uIcc_subset_Icc ⟨by linarith, hb⟩ hx
  have heq : (∫ t in (0 : ℝ)..x, clampedCurvature q b t) =
      ∫ t in (0 : ℝ)..x, q t := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [clampedCurvature, clamp_eq_self (hsub ht)]
  rw [firstPrimitive, heq]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (hsub ht))
  exact (hq.mono hsub).intervalIntegrable

/-- Exact agreement on the inner interval, including all integration constants. -/
theorem scalarExtension_eq_on_inner {U U₁ q : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hq : ContinuousOn q (Icc (-b) b)) (hU₁ : ContinuousOn U₁ (Icc (-b) b))
    (hderiv : ∀ t ∈ Icc (-b) b, HasDerivAt U (U₁ t) t)
    (hderiv₁ : ∀ t ∈ Icc (-b) b, HasDerivAt U₁ (q t) t)
    {x : ℝ} (hx : x ∈ Icc (-b) b) :
    scalarExtension q b x = U x - U 0 - x * U₁ 0 := by
  have hsub : uIcc (0 : ℝ) x ⊆ Icc (-b) b :=
    uIcc_subset_Icc ⟨by linarith, hb⟩ hx
  have hU₁i : IntervalIntegrable U₁ volume 0 x := (hU₁.mono hsub).intervalIntegrable
  unfold scalarExtension secondPrimitive
  calc
    _ = ∫ t in (0 : ℝ)..x, U₁ t - U₁ 0 := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact firstPrimitive_clamped_eq hb hq hderiv₁ (hsub ht)
    _ = (∫ t in (0 : ℝ)..x, U₁ t) - x * U₁ 0 := by
      rw [intervalIntegral.integral_sub hU₁i intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp
    _ = _ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hderiv t (hsub ht)) hU₁i]

end

end TheoremA2.BrascampLieb
