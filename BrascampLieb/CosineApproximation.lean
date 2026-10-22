import BrascampLieb.CosineExtension
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual pointwise and dominated limits of the cosine-prior approximants

The approximating potentials are the concrete double-integral extensions.
Their densities converge even at the two singular endpoints: a boundary
comparison bounds the density by a cosine tending to zero.  The argument
does not identify undefined endpoint logarithms with their limiting values.
-/

namespace TheoremA2.BrascampLieb

open MeasureTheory Set Filter
open scoped Topology
noncomputable section

/-- The target density is zero outside the open cosine support. -/
def cosinePriorWeight (lam x : ℝ) : ℝ :=
  if x ∈ Ioo (-endpoint lam) (endpoint lam) then
    Real.exp (-(x ^ 2) / (4 * lam)) * Real.cos (x / (2 * lam))
  else 0

theorem exp_neg_priorPotential {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-endpoint lam) (endpoint lam)) :
    Real.exp (-priorPotential lam x) =
      Real.exp (-(x ^ 2) / (4 * lam)) * Real.cos (x / (2 * lam)) := by
  have hc := cosine_pos_on_support hlam hx
  unfold priorPotential
  rw [show -(x ^ 2 / (4 * lam) - Real.log (Real.cos (x / (2 * lam)))) =
    -(x ^ 2) / (4 * lam) + Real.log (Real.cos (x / (2 * lam))) by ring,
    Real.exp_add, Real.exp_log hc]

theorem exp_neg_priorPotential_le_cos {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-endpoint lam) (endpoint lam)) :
    Real.exp (-priorPotential lam x) ≤ Real.cos (x / (2 * lam)) := by
  rw [exp_neg_priorPotential hlam hx]
  have he : Real.exp (-(x ^ 2) / (4 * lam)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by positivity)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right he (cosine_pos_on_support hlam hx).le

/-- Concrete radii exhaust the open support, starting with the harmless radius zero. -/
def innerRadius (lam : ℝ) (n : ℕ) : ℝ :=
  endpoint lam * (1 - 1 / ((n : ℝ) + 1))

theorem innerRadius_nonneg {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    0 ≤ innerRadius lam n := by
  have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hi : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one hd).2
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold innerRadius endpoint
  positivity

theorem innerRadius_lt {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    innerRadius lam n < endpoint lam := by
  have hb : 0 < endpoint lam := mul_pos Real.pi_pos hlam
  have hd : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  unfold innerRadius
  nlinarith

theorem tendsto_innerRadius (lam : ℝ) :
    Tendsto (innerRadius lam) atTop (𝓝 (endpoint lam)) := by
  have h : Tendsto (fun n : ℕ => endpoint lam * (1 - 1 / ((n : ℝ) + 1)))
      atTop (𝓝 (endpoint lam * (1 - 0))) := tendsto_const_nhds.mul
    (tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  change Tendsto (fun n : ℕ => endpoint lam * (1 - 1 / ((n : ℝ) + 1)))
    atTop (𝓝 (endpoint lam))
  simpa only [sub_zero, mul_one] using h

theorem cosinePriorWeight_nonneg {lam x : ℝ} (hlam : 0 < lam) :
    0 ≤ cosinePriorWeight lam x := by
  unfold cosinePriorWeight
  split_ifs with hx
  · exact mul_nonneg (Real.exp_pos _).le (cosine_pos_on_support hlam hx).le
  · exact le_rfl

theorem cosineExtension_density_domination {lam b : ℝ} (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hb : b < endpoint lam) (x : ℝ) :
    Real.exp (-cosineExtension lam b x) ≤
      Real.exp (-(curvatureConstant lam) * x ^ 2 / 2) := by
  apply Real.exp_le_exp.mpr
  have h := cosineExtension_quadratic_lower hlam hb0 hb x
  nlinarith

/-- Actual density convergence, including points on and beyond the singular boundary. -/
theorem tendsto_cosineExtension_density {lam : ℝ} (hlam : 0 < lam)
    (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hb : ∀ n, b n < endpoint lam)
    (hbt : Tendsto b atTop (𝓝 (endpoint lam))) (x : ℝ) :
    Tendsto (fun n => Real.exp (-cosineExtension lam (b n) x)) atTop
      (𝓝 (cosinePriorWeight lam x)) := by
  by_cases hx : x ∈ Ioo (-endpoint lam) (endpoint lam)
  · have hax : |x| < endpoint lam := abs_lt.mpr hx
    have hev : ∀ᶠ n in atTop, |x| < b n := hbt.eventually (eventually_gt_nhds hax)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    have hmem : x ∈ Icc (-(b n)) (b n) := by
      exact ⟨(abs_le.mp hn.le).1, (abs_le.mp hn.le).2⟩
    rw [cosineExtension_eq_of_mem hlam (hb0 n) (hb n) hmem,
      exp_neg_priorPotential hlam hx, cosinePriorWeight, if_pos hx]
  · have hax : endpoint lam ≤ |x| := le_of_not_gt (fun h => hx (abs_lt.mp h))
    have hboundary (n : ℕ) :
        Real.exp (-cosineExtension lam (b n) x) ≤ Real.cos (b n / (2 * lam)) := by
      apply (Real.exp_le_exp.mpr (neg_le_neg
        (cosineExtension_boundary_lower hlam (hb0 n) (hb n)
          ((hb n).le.trans hax)))).trans
      exact exp_neg_priorPotential_le_cos hlam
        (inner_interval_subset (hb n) ⟨by linarith [hb0 n], le_rfl⟩)
    have hcos : Tendsto (fun n => Real.cos (b n / (2 * lam))) atTop (𝓝 0) := by
      have heq : endpoint lam / (2 * lam) = Real.pi / 2 := by
        unfold endpoint
        field_simp
      have hh := Real.continuous_cos.continuousAt.tendsto.comp (hbt.div_const (2 * lam))
      simpa only [heq, Real.cos_pi_div_two, Function.comp_def] using hh
    rw [cosinePriorWeight, if_neg hx]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcos
      (fun n => (Real.exp_pos _).le) hboundary

theorem tendsto_innerRadius_density {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    Tendsto (fun n => Real.exp (-cosineExtension lam (innerRadius lam n) x)) atTop
      (𝓝 (cosinePriorWeight lam x)) :=
  tendsto_cosineExtension_density hlam (innerRadius lam)
    (innerRadius_nonneg hlam) (innerRadius_lt hlam) (tendsto_innerRadius lam) x

theorem measurable_cosinePriorWeight (lam : ℝ) : Measurable (cosinePriorWeight lam) := by
  unfold cosinePriorWeight
  apply Measurable.ite measurableSet_Ioo _ measurable_const
  fun_prop

theorem cosinePriorWeight_domination {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    cosinePriorWeight lam x ≤ Real.exp (-(curvatureConstant lam) * x ^ 2 / 2) := by
  exact le_of_tendsto (tendsto_innerRadius_density hlam x)
    (Eventually.of_forall (fun n => cosineExtension_density_domination hlam
      (innerRadius_nonneg hlam n) (innerRadius_lt hlam n) x))

theorem integrable_curvatureGaussian {lam : ℝ} (hlam : 0 < lam) :
    Integrable (fun x : ℝ => Real.exp (-(curvatureConstant lam) * x ^ 2 / 2)) := by
  have h := integrable_exp_neg_mul_sq (div_pos (curvatureConstant_pos hlam) (by norm_num : (0 : ℝ) < 2))
  convert h using 1
  ext x
  congr 1
  ring

theorem integrable_cosineExtension_density {lam b : ℝ} (hlam : 0 < lam)
    (hb0 : 0 ≤ b) (hb : b < endpoint lam) :
    Integrable (fun x => Real.exp (-cosineExtension lam b x)) := by
  apply (integrable_curvatureGaussian hlam).mono'
    (Real.continuous_exp.comp (cosineExtension_contDiff hlam hb0 hb).continuous.neg).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change |Real.exp (-cosineExtension lam b x)| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    exact cosineExtension_density_domination hlam hb0 hb x)

theorem integrable_cosinePriorWeight {lam : ℝ} (hlam : 0 < lam) :
    Integrable (cosinePriorWeight lam) := by
  apply (integrable_curvatureGaussian hlam).mono'
    (measurable_cosinePriorWeight lam).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (cosinePriorWeight_nonneg hlam)]
    exact cosinePriorWeight_domination hlam x)

theorem cosinePriorWeight_pos {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-endpoint lam) (endpoint lam)) :
    0 < cosinePriorWeight lam x := by
  rw [cosinePriorWeight, if_pos hx]
  exact mul_pos (Real.exp_pos _) (cosine_pos_on_support hlam hx)

theorem cosinePriorWeight_mass_pos {lam : ℝ} (hlam : 0 < lam) :
    0 < ∫ x, cosinePriorWeight lam x := by
  apply (integral_pos_iff_support_of_nonneg
    (fun x => cosinePriorWeight_nonneg hlam) (integrable_cosinePriorWeight hlam)).mpr
  have hsub : Ioo (-endpoint lam) (endpoint lam) ⊆ Function.support (cosinePriorWeight lam) :=
    fun x hx => ne_of_gt (cosinePriorWeight_pos hlam hx)
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [Real.volume_Ioo]
  apply ENNReal.ofReal_pos.mpr
  have hendpoint : 0 < endpoint lam := mul_pos Real.pi_pos hlam
  linarith

/-- Lebesgue mass convergence follows from the actual common Gaussian majorant. -/
theorem tendsto_cosineExtension_mass {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n => ∫ x, Real.exp (-cosineExtension lam (innerRadius lam n) x)) atTop
      (𝓝 (∫ x, cosinePriorWeight lam x)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x : ℝ => Real.exp (-(curvatureConstant lam) * x ^ 2 / 2))
  · intro n
    exact (Real.continuous_exp.comp (cosineExtension_contDiff hlam
      (innerRadius_nonneg hlam n) (innerRadius_lt hlam n)).continuous.neg).aestronglyMeasurable
  · exact integrable_curvatureGaussian hlam
  · intro n
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact cosineExtension_density_domination hlam
        (innerRadius_nonneg hlam n) (innerRadius_lt hlam n) x)
  · exact Eventually.of_forall (tendsto_innerRadius_density hlam)

end
end TheoremA2.BrascampLieb
