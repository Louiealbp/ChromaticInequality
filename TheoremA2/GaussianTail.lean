import TheoremA2.Imports

/-!
# Claim A.23: a Gaussian tail with quadratic cost

This proves the actual integral under the standard Gaussian probability
measure. The proof exponentially tilts its density to variance two, obtaining
the slightly stronger result for every nonnegative threshold. All functions
compared under integrals are proved integrable.
-/

namespace TheoremA2.GaussianTail

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

noncomputable section

def cost (z : ℝ) : ℝ := z ^ 2 + Real.log 3

theorem cost_nonneg (z : ℝ) : 0 ≤ cost z := by
  unfold cost
  exact add_nonneg (sq_nonneg z) (Real.log_nonneg (by norm_num))

theorem integrable_weighted_cost {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : ℝ => cost z * Real.exp (-b * z ^ 2)) := by
  have hsq : Integrable (fun z : ℝ => z ^ 2 * Real.exp (-b * z ^ 2)) := by
    simpa only [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2))
  simp only [cost, add_mul]
  exact hsq.add ((integrable_exp_neg_mul_sq hb).const_mul (Real.log 3))

theorem integrable_pdf_cost {v : ℝ≥0} (hv : 0 < v) :
    Integrable (fun z : ℝ => gaussianPDFReal 0 v z * cost z) := by
  have hvR : (0 : ℝ) < v := hv
  have h := (integrable_weighted_cost
    (by positivity : (0 : ℝ) < (2 * (v : ℝ))⁻¹)).const_mul
      (Real.sqrt (2 * Real.pi * v))⁻¹
  convert h using 1
  funext z
  simp only [gaussianPDFReal, sub_zero]
  rw [show -(z ^ 2) / (2 * (v : ℝ)) = -(2 * (v : ℝ))⁻¹ * z ^ 2 by ring]
  ring

theorem integral_pdf_cost_two :
    (∫ z : ℝ, gaussianPDFReal 0 2 z * cost z) = 2 + Real.log 3 := by
  have hconvert := integral_gaussianReal_eq_integral_smul
    (f := cost) (μ := 0) (by norm_num : (2 : ℝ≥0) ≠ 0)
  simp only [smul_eq_mul] at hconvert
  rw [← hconvert]
  have hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 2) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hm := variance_fun_id_gaussianReal (μ := 0) (v := 2)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hm
  simp only [integral_id_gaussianReal, sub_zero, NNReal.coe_ofNat] at hm
  unfold cost
  rw [integral_add hsq (integrable_const _), hm]
  simp

theorem pdf_one_tilt (z : ℝ) :
    gaussianPDFReal 0 1 z =
      Real.sqrt 2 * Real.exp (-(z ^ 2) / 4) * gaussianPDFReal 0 2 z := by
  have hsp : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hs : Real.sqrt (2 * Real.pi * (2 : ℝ)) =
      Real.sqrt 2 * Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, NNReal.coe_ofNat]
  rw [hs]
  have hs2n : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp
  rw [← Real.exp_add]
  congr 1
  ring

/-- Exponential tilting gives a stronger constant than the paper needs. -/
theorem quadratic_tail_tilted {t : ℝ} (ht : 0 ≤ t) :
    (∫ z : ℝ, ({z : ℝ | t < |z|}).indicator cost z ∂gaussianReal 0 1) ≤
      Real.sqrt 2 * (2 + Real.log 3) * Real.exp (-(t ^ 2) / 4) := by
  have hset : MeasurableSet {z : ℝ | t < |z|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hind : (fun z : ℝ => gaussianPDFReal 0 1 z *
      ({z : ℝ | t < |z|}).indicator cost z) =
      ({z : ℝ | t < |z|}).indicator (fun z => gaussianPDFReal 0 1 z * cost z) := by
    funext z
    by_cases hz : t < |z| <;> simp [hz]
  have hi : Integrable (fun z : ℝ => gaussianPDFReal 0 1 z *
      ({z : ℝ | t < |z|}).indicator cost z) := by
    rw [hind]
    exact (integrable_pdf_cost (v := 1) (by norm_num)).indicator hset
  have hj : Integrable (fun z : ℝ =>
      (Real.sqrt 2 * Real.exp (-(t ^ 2) / 4)) * (gaussianPDFReal 0 2 z * cost z)) :=
    (integrable_pdf_cost (v := 2) (by norm_num)).const_mul _
  have hp (z : ℝ) : gaussianPDFReal 0 1 z *
      ({z : ℝ | t < |z|}).indicator cost z ≤
      (Real.sqrt 2 * Real.exp (-(t ^ 2) / 4)) * (gaussianPDFReal 0 2 z * cost z) := by
    have hcost := cost_nonneg z
    have hpdf := gaussianPDFReal_nonneg 0 2 z
    by_cases hz : t < |z|
    · rw [indicator_of_mem (show z ∈ {z : ℝ | t < |z|} from hz), pdf_one_tilt]
      have hs : t ^ 2 ≤ z ^ 2 := by
        simpa only [sq_abs] using ((sq_le_sq₀ ht (abs_nonneg z)).2 hz.le)
      have he : Real.exp (-(z ^ 2) / 4) ≤ Real.exp (-(t ^ 2) / 4) :=
        Real.exp_le_exp.2 (by linarith)
      calc
        Real.sqrt 2 * Real.exp (-(z ^ 2) / 4) * gaussianPDFReal 0 2 z * cost z =
            (Real.sqrt 2 * (gaussianPDFReal 0 2 z * cost z)) * Real.exp (-(z ^ 2) / 4) := by ring
        _ ≤ (Real.sqrt 2 * (gaussianPDFReal 0 2 z * cost z)) * Real.exp (-(t ^ 2) / 4) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ = _ := by ring
    · rw [indicator_of_notMem (show z ∉ {z : ℝ | t < |z|} from hz), mul_zero]
      positivity
  calc
    (∫ z : ℝ, ({z : ℝ | t < |z|}).indicator cost z ∂gaussianReal 0 1) =
        ∫ z : ℝ, gaussianPDFReal 0 1 z * ({z : ℝ | t < |z|}).indicator cost z := by
      simpa only [smul_eq_mul] using integral_gaussianReal_eq_integral_smul
        (f := fun z : ℝ => ({z : ℝ | t < |z|}).indicator cost z)
        (μ := 0) (by norm_num : (1 : ℝ≥0) ≠ 0)
    _ ≤ ∫ z : ℝ, (Real.sqrt 2 * Real.exp (-(t ^ 2) / 4)) *
        (gaussianPDFReal 0 2 z * cost z) := integral_mono hi hj hp
    _ = (Real.sqrt 2 * Real.exp (-(t ^ 2) / 4)) * (2 + Real.log 3) := by
      rw [integral_const_mul, integral_pdf_cost_two]
    _ = _ := by ring

/-- Claim A.23, in fact valid for every `t ≥ 0`. -/
theorem quadratic_tail {t : ℝ} (ht : 0 ≤ t) :
    (∫ z : ℝ, ({z : ℝ | t < |z|}).indicator
      (fun z => z ^ 2 + Real.log 3) z ∂gaussianReal 0 1) ≤
        8 * Real.exp (-(t ^ 2) / 4) := by
  have hlog : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hlog0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hs : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hc : Real.sqrt 2 * (2 + Real.log 3) ≤ 8 := by
    calc Real.sqrt 2 * (2 + Real.log 3) ≤ 2 * (2 + Real.log 3) :=
          mul_le_mul_of_nonneg_right hs (by linarith)
      _ ≤ 8 := by linarith
  exact (quadratic_tail_tilted ht).trans
    (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le)

/-- The exact threshold range used by the paper. -/
theorem claim_A23 {t : ℝ} (ht : 2 ≤ t) :
    (∫ z : ℝ, ({z : ℝ | t < |z|}).indicator
      (fun z => z ^ 2 + Real.log 3) z ∂gaussianReal 0 1) ≤
        8 * Real.exp (-(t ^ 2) / 4) :=
  quadratic_tail (by linarith)

end

end TheoremA2.GaussianTail
