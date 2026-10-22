import TheoremA2.GaussianEnvelopeBox
import TheoremA2.WeightedTail
import TheoremA2.SpinCovarianceParameters

/-! The literal coordinate union tail used by A.27, derived from actual MGFs. -/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inner_box_indicator_le {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    ((coordinateBox (1 / 4))ᶜ).indicator (fun _ => (1 : ℝ)) x ≤
      ∑ i, Real.exp (-t) * (Real.exp ((4 * t) * x i) + Real.exp ((-4 * t) * x i)) := by
  classical
  by_cases hx : x ∈ coordinateBox (1 / 4)
  · rw [Set.indicator_of_notMem (show x ∉ (coordinateBox (1 / 4))ᶜ from fun h => h hx)]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  · rw [Set.indicator_of_mem (show x ∈ (coordinateBox (1 / 4))ᶜ from hx)]
    obtain ⟨i, hi⟩ : ∃ i, (1 / 4 : ℝ) < |x i| := by
      simpa only [coordinateBox, Set.mem_setOf_eq, not_forall, not_le] using hx
    have hlarge : 1 ≤ |4 * x i| := by rw [abs_mul]; norm_num; linarith
    have hpair := TheoremA2.WeightedTail.one_le_exponentialPair ht hlarge
    have hpair' : 1 ≤ Real.exp (-t) *
        (Real.exp ((4 * t) * x i) + Real.exp ((-4 * t) * x i)) := by
      simpa only [show t * (4 * x i) = (4 * t) * x i by ring,
        show -t * (4 * x i) = (-4 * t) * x i by ring] using hpair
    have hsingle : Real.exp (-t) *
        (Real.exp ((4 * t) * x i) + Real.exp ((-4 * t) * x i)) ≤
        ∑ j : ι, Real.exp (-t) *
          (Real.exp ((4 * t) * x j) + Real.exp ((-4 * t) * x j)) :=
      Finset.single_le_sum
        (f := fun j : ι => Real.exp (-t) *
          (Real.exp ((4 * t) * x j) + Real.exp ((-4 * t) * x j)))
        (fun _ _ => by positivity) (Finset.mem_univ i)
    exact hpair'.trans hsingle

/-- The expectation of the actual bad-box indicator has the paper's full
dimension factor. Coordinate dependence is unrestricted. -/
theorem inner_box_tail_of_coordinate_mgf (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : 0 < q)
    (hint : ∀ (t : ℝ) (i : ι), Integrable (fun x => Real.exp (t * x i)) μ)
    (hmgf : ∀ (t : ℝ) (i : ι),
      (∫ x, Real.exp (t * x i) ∂μ) ≤ Real.exp (t ^ 2 * q / 2)) :
    (∫ x in (coordinateBox (1 / 4))ᶜ, (1 : ℝ) ∂μ) ≤
      SpinCovariance.zeroFieldDelta (Fintype.card ι) q := by
  let t : ℝ := 1 / (16 * q)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hi (i : ι) : Integrable (fun x : ι → ℝ => Real.exp (-t) *
      (Real.exp ((4 * t) * x i) + Real.exp ((-4 * t) * x i))) μ :=
    ((hint (4 * t) i).add (hint (-4 * t) i)).const_mul _
  have hind : Integrable
      (((coordinateBox (ι := ι) (1 / 4))ᶜ).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (coordinateBox_measurable (1 / 4)).compl
  have hbound := integral_mono hind (integrable_finsetSum _ (fun i _ => hi i))
    (inner_box_indicator_le (ι := ι) ht)
  rw [integral_indicator (coordinateBox_measurable (1 / 4)).compl,
    integral_finsetSum _ (fun i _ => hi i)] at hbound
  have hterm (i : ι) :
      (∫ x, Real.exp (-t) * (Real.exp ((4 * t) * x i) + Real.exp ((-4 * t) * x i)) ∂μ) ≤
      Real.exp (-t) * (2 * Real.exp ((4 * t) ^ 2 * q / 2)) := by
    rw [integral_const_mul, integral_add (hint (4 * t) i) (hint (-4 * t) i)]
    have hn := hmgf (-4 * t) i
    rw [show (-4 * t) ^ 2 = (4 * t) ^ 2 by ring] at hn
    exact mul_le_mul_of_nonneg_left (by linarith [hmgf (4 * t) i]) (Real.exp_pos _).le
  have hex : -t + (4 * t) ^ 2 * q / 2 = -(1 : ℝ) / (32 * q) := by
    dsimp [t]
    field_simp [ne_of_gt hq]
    ring
  calc
    _ ≤ ∑ i : ι, Real.exp (-t) * (2 * Real.exp ((4 * t) ^ 2 * q / 2)) :=
      hbound.trans (Finset.sum_le_sum (fun i _ => hterm i))
    _ = SpinCovariance.zeroFieldDelta (Fintype.card ι) q := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, SpinCovariance.zeroFieldDelta]
      rw [← hex, Real.exp_add]
      ring

theorem quadratic_single (T : Matrix ι ι ℝ) (i : ι) (t : ℝ) :
    quadratic T (Pi.single i t) = t ^ 2 * T i i := by
  simp only [quadratic, single_dotProduct, Matrix.mulVec_single,
    op_smul_eq_smul, Pi.smul_apply, smul_eq_mul, Matrix.col, Matrix.transpose_apply]
  ring

/-- Apply the coordinate tail estimate to any actual law with matrix proxy T. -/
theorem inner_box_tail_of_matrix_mgf (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (T : Matrix ι ι ℝ) {q : ℝ} (hq : 0 < q) (hdiag : ∀ i, T i i ≤ q)
    (hint : ∀ u : ι → ℝ, Integrable (fun x => Real.exp (u ⬝ᵥ x)) μ)
    (hmgf : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂μ) ≤ Real.exp (quadratic T u / 2)) :
    (∫ x in (coordinateBox (1 / 4))ᶜ, (1 : ℝ) ∂μ) ≤
      SpinCovariance.zeroFieldDelta (Fintype.card ι) q := by
  apply inner_box_tail_of_coordinate_mgf μ hq
  · intro t i
    simpa only [single_dotProduct] using hint (Pi.single i t)
  · intro t i
    have h := hmgf (Pi.single i t)
    simp only [quadratic_single] at h
    have hd : t ^ 2 * T i i / 2 ≤ t ^ 2 * q / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hdiag i) (sq_nonneg t)) (by norm_num)
    have h' : (∫ x, Real.exp (t * x i) ∂μ) ≤ Real.exp (t ^ 2 * T i i / 2) := by
      simpa only [single_dotProduct] using h
    exact h'.trans (Real.exp_le_exp.mpr hd)

end

end TheoremA2.GaussianCovariance
