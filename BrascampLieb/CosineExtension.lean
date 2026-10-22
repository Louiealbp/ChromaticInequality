import BrascampLieb.ScalarExtension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Globally C² approximants to the actual cosine prior

These definitions are the same explicit potential and curvature as the
positive cosine reference. Its derivatives are proved from the formulas.
The extensions are actual double integrals, not assumed approximants.
-/

namespace TheoremA2.BrascampLieb

open MeasureTheory Set Filter
open scoped Topology
noncomputable section

def endpoint (lam : ℝ) : ℝ := Real.pi * lam

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



@[simp] theorem priorPotential_zero (lam : ℝ) : priorPotential lam 0 = 0 := by
  simp [priorPotential]

@[simp] theorem priorDerivative_zero (lam : ℝ) : priorDerivative lam 0 = 0 := by
  simp [priorDerivative]

theorem curvatureConstant_pos {lam : ℝ} (hlam : 0 < lam) :
    0 < curvatureConstant lam := by
  unfold curvatureConstant
  positivity

theorem priorSecondDerivative_even (lam : ℝ) : Function.Even (priorSecondDerivative lam) := by
  intro t
  simp [priorSecondDerivative, neg_div]

theorem inner_interval_subset {lam b : ℝ} (hb : b < endpoint lam) :
    Icc (-b) b ⊆ Ioo (-endpoint lam) (endpoint lam) := by
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem continuousOn_priorSecondDerivative {lam b : ℝ} (hlam : 0 < lam)
    (hb : b < endpoint lam) : ContinuousOn (priorSecondDerivative lam) (Icc (-b) b) := by
  intro t ht
  have hc : Real.cos (t / (2 * lam)) ≠ 0 :=
    ne_of_gt (cosine_pos_on_support hlam (inner_interval_subset hb ht))
  apply ContinuousAt.continuousWithinAt
  unfold priorSecondDerivative
  have hcos : ContinuousAt (fun x : ℝ => Real.cos (x / (2 * lam))) t :=
    Real.continuous_cos.continuousAt.comp (continuousAt_id.div_const (2 * lam))
  exact continuousAt_const.add
    (continuousAt_const.mul (continuousAt_const.div (hcos.pow 2) (pow_ne_zero 2 hc)))

/-- A globally defined smooth potential with the cosine prior's clamped curvature. -/
def cosineExtension (lam b : ℝ) : ℝ → ℝ :=
  scalarExtension (priorSecondDerivative lam) b

theorem cosineExtension_contDiff {lam b : ℝ} (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hb : b < endpoint lam) : ContDiff ℝ 2 (cosineExtension lam b) :=
  scalarExtension_contDiff hb0 (continuousOn_priorSecondDerivative hlam hb)

theorem cosineExtension_eq_of_mem {lam b x : ℝ} (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hb : b < endpoint lam) (hx : x ∈ Icc (-b) b) :
    cosineExtension lam b x = priorPotential lam x := by
  have h := scalarExtension_eq_on_inner (U := priorPotential lam)
    (U₁ := priorDerivative lam) (q := priorSecondDerivative lam) hb0
    (continuousOn_priorSecondDerivative hlam hb)
    (fun t ht => (hasDerivAt_priorDerivative hlam
      (inner_interval_subset hb ht)).continuousAt.continuousWithinAt)
    (fun t ht => hasDerivAt_priorPotential hlam (inner_interval_subset hb ht))
    (fun t ht => hasDerivAt_priorDerivative hlam (inner_interval_subset hb ht)) hx
  simpa only [priorPotential_zero, priorDerivative_zero, mul_zero, sub_zero,
    cosineExtension] using h

theorem cosineExtension_second_derivative {lam b : ℝ} (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hb : b < endpoint lam) (x : ℝ) :
    deriv (deriv (cosineExtension lam b)) x = priorSecondDerivative lam (clamp b x) :=
  scalarExtension_second_derivative hb0 (continuousOn_priorSecondDerivative hlam hb) x

theorem cosineExtension_curvature {lam b : ℝ} (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hb : b < endpoint lam) (x : ℝ) :
    curvatureConstant lam ≤ deriv (deriv (cosineExtension lam b)) x :=
  scalarExtension_curvature_lower hb0 (continuousOn_priorSecondDerivative hlam hb)
    (fun t ht => prior_curvature_lower_bound hlam (inner_interval_subset hb ht)) x

theorem cosineExtension_quadratic_lower {lam b : ℝ} (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hb : b < endpoint lam) (x : ℝ) :
    curvatureConstant lam * x ^ 2 / 2 ≤ cosineExtension lam b x :=
  scalarExtension_quadratic_lower hb0 (continuousOn_priorSecondDerivative hlam hb)
    (fun t ht => prior_curvature_lower_bound hlam (inner_interval_subset hb ht)) x

theorem cosineExtension_even {lam b : ℝ} (hb0 : 0 ≤ b) :
    Function.Even (cosineExtension lam b) :=
  secondPrimitive_even (clampedCurvature_even hb0 (priorSecondDerivative_even lam))

/-- Outside the inner interval the extended potential is at least the true boundary value. -/
theorem cosineExtension_boundary_lower {lam b x : ℝ} (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hb : b < endpoint lam) (hx : b ≤ |x|) :
    priorPotential lam b ≤ cosineExtension lam b x := by
  have hnonneg (t : ℝ) : 0 ≤ clampedCurvature (priorSecondDerivative lam) b t :=
    (curvatureConstant_pos hlam).le.trans
      (prior_curvature_lower_bound hlam (inner_interval_subset hb (clamp_mem hb0 t)))
  have h := secondPrimitive_boundary_lower
    (continuous_clampedCurvature hb0 (continuousOn_priorSecondDerivative hlam hb))
    hnonneg (clampedCurvature_even hb0 (priorSecondDerivative_even lam)) hb0 hx
  change cosineExtension lam b b ≤ cosineExtension lam b x at h
  rw [cosineExtension_eq_of_mem hlam hb0 hb ⟨by linarith, le_rfl⟩] at h
  exact h

end
end TheoremA2.BrascampLieb
