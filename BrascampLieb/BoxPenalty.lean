import BrascampLieb.ScalarExtension
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A genuine convex C² penalty for a closed interval

The penalty is defined by integrating the continuous nonnegative curvature
`max 0 (|x| - b)` twice. It vanishes exactly on `[-b,b]` and is positive
elsewhere. Multiplying it by natural numbers therefore approximates hard
restriction to that interval, including the correct nonzero boundary values.
-/

namespace TheoremA2.BrascampLieb

open MeasureTheory Set Filter
open scoped Topology
noncomputable section

def boxCurvature (b x : ℝ) : ℝ := max 0 (|x| - b)

def boxPenalty (b : ℝ) : ℝ → ℝ := secondPrimitive (boxCurvature b)

theorem continuous_boxCurvature (b : ℝ) : Continuous (boxCurvature b) := by
  unfold boxCurvature
  fun_prop

theorem boxCurvature_nonneg (b x : ℝ) : 0 ≤ boxCurvature b x := le_max_left _ _

theorem boxCurvature_even (b : ℝ) : Function.Even (boxCurvature b) := by
  intro x
  simp [boxCurvature]

theorem boxCurvature_eq_zero {b x : ℝ} (hx : |x| ≤ b) : boxCurvature b x = 0 := by
  exact max_eq_left (sub_nonpos.mpr hx)

theorem boxCurvature_pos {b x : ℝ} (hx : b < |x|) : 0 < boxCurvature b x :=
  (sub_pos.mpr hx).trans_le (le_max_right _ _)

theorem boxPenalty_contDiff (b : ℝ) : ContDiff ℝ 2 (boxPenalty b) :=
  contDiff_secondPrimitive (continuous_boxCurvature b)

theorem boxPenalty_second_derivative (b x : ℝ) :
    deriv (deriv (boxPenalty b)) x = boxCurvature b x :=
  congrFun (second_deriv_secondPrimitive (continuous_boxCurvature b)) x

theorem boxPenalty_curvature_nonneg (b x : ℝ) :
    0 ≤ deriv (deriv (boxPenalty b)) x := by
  rw [boxPenalty_second_derivative]
  exact boxCurvature_nonneg b x

theorem boxPenalty_nonneg (b x : ℝ) : 0 ≤ boxPenalty b x :=
  secondPrimitive_nonneg (boxCurvature_nonneg b) x

theorem boxPenalty_even (b : ℝ) : Function.Even (boxPenalty b) :=
  secondPrimitive_even (boxCurvature_even b)

theorem firstPrimitive_boxCurvature_eq_zero {b x : ℝ} (hb : 0 ≤ b)
    (hx : |x| ≤ b) : firstPrimitive (boxCurvature b) x = 0 := by
  have hsub : uIcc (0 : ℝ) x ⊆ Icc (-b) b :=
    uIcc_subset_Icc ⟨by linarith, hb⟩ (abs_le.mp hx)
  unfold firstPrimitive
  calc
    _ = ∫ _t in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact boxCurvature_eq_zero (abs_le.mpr (hsub ht))
    _ = 0 := by simp

theorem boxPenalty_eq_zero {b x : ℝ} (hb : 0 ≤ b) (hx : |x| ≤ b) :
    boxPenalty b x = 0 := by
  have hsub : uIcc (0 : ℝ) x ⊆ Icc (-b) b :=
    uIcc_subset_Icc ⟨by linarith, hb⟩ (abs_le.mp hx)
  unfold boxPenalty secondPrimitive
  calc
    _ = ∫ _t in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact firstPrimitive_boxCurvature_eq_zero hb (abs_le.mpr (hsub ht))
    _ = 0 := by simp

theorem firstPrimitive_boxCurvature_pos {b x : ℝ} (hb : 0 ≤ b)
    (hx : b < x) : 0 < firstPrimitive (boxCurvature b) x := by
  have hx0 : 0 < x := hb.trans_lt hx
  apply intervalIntegral.integral_pos hx0 (continuous_boxCurvature b).continuousOn
  · intro t _
    exact boxCurvature_nonneg b t
  · exact ⟨x, ⟨hx0.le, le_rfl⟩, boxCurvature_pos (by rwa [abs_of_pos hx0])⟩

theorem boxPenalty_pos_of_gt {b x : ℝ} (hb : 0 ≤ b) (hx : b < x) :
    0 < boxPenalty b x := by
  have hx0 : 0 < x := hb.trans_lt hx
  apply intervalIntegral.integral_pos hx0
    (continuous_firstPrimitive (continuous_boxCurvature b)).continuousOn
  · intro t ht
    exact firstPrimitive_nonneg (boxCurvature_nonneg b) ht.1.le
  · exact ⟨x, ⟨hx0.le, le_rfl⟩, firstPrimitive_boxCurvature_pos hb hx⟩

theorem boxPenalty_pos {b x : ℝ} (hb : 0 ≤ b) (hx : b < |x|) :
    0 < boxPenalty b x := by
  have h := boxPenalty_pos_of_gt hb hx
  rcases le_total 0 x with hx0 | hx0
  · simpa only [abs_of_nonneg hx0] using h
  · simpa only [abs_of_nonpos hx0, (boxPenalty_even b).eq] using h

theorem boxPenalty_eq_zero_iff {b x : ℝ} (hb : 0 ≤ b) :
    boxPenalty b x = 0 ↔ |x| ≤ b := by
  constructor
  · intro h
    by_contra hx
    exact (ne_of_gt (boxPenalty_pos hb (lt_of_not_ge hx))) h
  · exact boxPenalty_eq_zero hb

theorem tendsto_exp_neg_nat_mul {p : ℝ} (hp : 0 ≤ p) :
    Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * p)) atTop
      (𝓝 (if p = 0 then (1 : ℝ) else 0)) := by
  by_cases hp0 : p = 0
  · simp only [hp0, mul_zero, Real.exp_zero, if_pos rfl]
    exact tendsto_const_nhds
  · rw [if_neg hp0]
    have hpt : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have ht : Tendsto (fun n : ℕ => (n : ℝ) * p) atTop atTop :=
      Tendsto.atTop_mul_const hpt tendsto_natCast_atTop_atTop
    have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)
    convert h using 1
    ext n
    simp only [Function.comp_apply, neg_mul]

theorem integrable_penalty_weight {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (P f : α → ℝ) (hP : Measurable P) (hP0 : ∀ x, 0 ≤ P x)
    (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun x => f x * Real.exp (-(n : ℝ) * P x)) μ := by
  apply hf.norm.mono'
  · exact hf.aestronglyMeasurable.mul
      ((measurable_const.mul hP).exp.aestronglyMeasurable)
  · exact Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
      apply mul_le_of_le_one_right (norm_nonneg _)
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)) (hP0 x))

/-- An integrable density or moment passes to its exact restriction under the
concrete nonnegative penalty. No normalization is omitted. -/
theorem integral_penalty_limit {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (P f : α → ℝ) (hP : Measurable P) (hP0 : ∀ x, 0 ≤ P x)
    (hf : Integrable f μ) :
    Tendsto (fun n : ℕ => ∫ x, f x * Real.exp (-(n : ℝ) * P x) ∂μ) atTop
      (𝓝 (∫ x in {x | P x = 0}, f x ∂μ)) := by
  have hs : MeasurableSet {x | P x = 0} := measurableSet_eq_fun hP measurable_const
  rw [← integral_indicator hs]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact hf.aestronglyMeasurable.mul
      ((measurable_const.mul hP).exp.aestronglyMeasurable)
  · exact hf.norm
  · intro n
    exact Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
      apply mul_le_of_le_one_right (norm_nonneg _)
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)) (hP0 x))
  · exact Eventually.of_forall (fun x => by
      have h := (tendsto_exp_neg_nat_mul (hP0 x)).const_mul (f x)
      simpa only [Set.indicator_apply, mem_setOf_eq, mul_ite, mul_one, mul_zero] using h)

end
end TheoremA2.BrascampLieb
