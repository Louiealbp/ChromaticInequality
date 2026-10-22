import BrascampLieb.BoxVariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Tilted

/-! Exact normalized versions of the proved weighted variance estimates. -/

namespace TheoremA2.BrascampLieb

open MeasureTheory Measure ProbabilityTheory GinibrePoincare
open scoped Topology ContDiff BigOperators Matrix
noncomputable section

theorem integral_gibbs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (W f : α → ℝ) :
    (∫ x, f x ∂μ.tilted (fun x => -W x)) =
      (∫ x, f x * Real.exp (-W x) ∂μ) / (∫ x, Real.exp (-W x) ∂μ) := by
  rw [integral_tilted, ← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp only [smul_eq_mul]; ring

theorem variance_gibbs {α : Type*} [MeasurableSpace α] (μ : Measure α) [NeZero μ]
    (W g : α → ℝ) (hWi : Integrable (fun x => Real.exp (-W x)) μ)
    (hgm : Measurable g)
    (hg2 : Integrable (fun x => g x ^ 2 * Real.exp (-W x)) μ) :
    Var[g; μ.tilted (fun x => -W x)] =
      (∫ x, g x ^ 2 * Real.exp (-W x) ∂μ) / (∫ x, Real.exp (-W x) ∂μ) -
        ((∫ x, g x * Real.exp (-W x) ∂μ) / (∫ x, Real.exp (-W x) ∂μ)) ^ 2 := by
  letI := isProbabilityMeasure_tilted hWi
  have hi : Integrable (fun x => g x ^ 2) (μ.tilted (fun x => -W x)) := by
    rw [integrable_tilted_iff hWi]
    simp only [smul_eq_mul]
    simpa only [mul_comm] using hg2
  have hLp : MemLp g 2 (μ.tilted (fun x => -W x)) :=
    (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr hi
  rw [variance_eq_sub hLp]
  change (∫ x, g x ^ 2 ∂μ.tilted (fun x => -W x)) -
    (∫ x, g x ∂μ.tilted (fun x => -W x)) ^ 2 = _
  rw [integral_gibbs, integral_gibbs]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem wholeSpace_variance_hessian_bound
    (W g : E → ℝ) (b : OrthonormalBasis ι ℝ E) (D : E → Matrix ι ι ℝ)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hD : ∀ x, (D x).PosDef)
    (hHD : ∀ x, (correspondenceBrascampLiebHessian W b x - D x).PosSemidef)
    (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2 * bakryEmeryGibbsWeight W x))
    (hR : Integrable (fun x =>
      (correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
        correspondenceBrascampLiebGradient g b x) * bakryEmeryGibbsWeight W x)) :
    Var[g; volume.tilted (fun x => -W x)] ≤
      ∫ x, correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
        correspondenceBrascampLiebGradient g b x ∂volume.tilted (fun x => -W x) := by
  have hZ := correspondenceBrascampLieb_positive_mass W hWi
  have hZ0 : (∫ x, Real.exp (-W x)) ≠ 0 := ne_of_gt hZ
  have h := wholeSpace_weighted_variance_hessian_bound W g b D hW hWi hD hHD hg hg2 hR
  rw [variance_gibbs volume W g hWi hg.continuous.measurable hg2, integral_gibbs]
  have he : (∫ x, g x ^ 2 * Real.exp (-W x)) / (∫ x, Real.exp (-W x)) -
      ((∫ x, g x * Real.exp (-W x)) / (∫ x, Real.exp (-W x))) ^ 2 =
      ((∫ x, g x ^ 2 * Real.exp (-W x)) -
        (∫ x, g x * Real.exp (-W x)) ^ 2 / (∫ x, Real.exp (-W x))) /
          (∫ x, Real.exp (-W x)) := by field_simp [hZ0] <;> ring
  rw [he]
  exact (div_le_div_iff_of_pos_right hZ).mpr h

/-- The actual normalized Gibbs law on the literal closed coordinate box. -/
theorem box_variance_hessian_bound
    (W g : E → ℝ) (b : OrthonormalBasis ι ℝ E) (D : E → Matrix ι ι ℝ)
    {r : ℝ} (hr : 0 < r) (hW : ContDiff ℝ 2 W)
    (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hD : ∀ x, (D x).PosDef)
    (hHD : ∀ x, (correspondenceBrascampLiebHessian W b x - D x).PosSemidef)
    (hg : ContDiff ℝ 1 g)
    (hg1 : Integrable (fun x => g x * bakryEmeryGibbsWeight W x))
    (hg2 : Integrable (fun x => g x ^ 2 * bakryEmeryGibbsWeight W x))
    (hR : Integrable (fun x =>
      (correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
        correspondenceBrascampLiebGradient g b x) * bakryEmeryGibbsWeight W x)) :
    Var[g; (volume.restrict (coordinateBox b r)).tilted (fun x => -W x)] ≤
      ∫ x, correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
        correspondenceBrascampLiebGradient g b x
          ∂(volume.restrict (coordinateBox b r)).tilted (fun x => -W x) := by
  have hs : 0 < volume (coordinateBox b r) :=
    (Metric.measure_ball_pos volume (0 : E) hr).trans_le
      (measure_mono (ball_subset_coordinateBox b))
  haveI : NeZero (volume.restrict (coordinateBox b r)) :=
    ⟨fun hz => (ne_of_gt hs) (Measure.restrict_eq_zero.mp hz)⟩
  have hZ := coordinateBox_mass_pos b hr W hWi
  have hZ0 : (∫ x in coordinateBox b r, Real.exp (-W x)) ≠ 0 := ne_of_gt hZ
  have h := box_weighted_variance_hessian_bound W g b D hr hW hWi hD hHD hg hg1 hg2 hR
  rw [variance_gibbs _ W g hWi.integrableOn hg.continuous.measurable hg2.integrableOn,
    integral_gibbs]
  have he : (∫ x in coordinateBox b r, g x ^ 2 * Real.exp (-W x)) /
      (∫ x in coordinateBox b r, Real.exp (-W x)) -
      ((∫ x in coordinateBox b r, g x * Real.exp (-W x)) /
        (∫ x in coordinateBox b r, Real.exp (-W x))) ^ 2 =
      ((∫ x in coordinateBox b r, g x ^ 2 * Real.exp (-W x)) -
        (∫ x in coordinateBox b r, g x * Real.exp (-W x)) ^ 2 /
          (∫ x in coordinateBox b r, Real.exp (-W x))) /
            (∫ x in coordinateBox b r, Real.exp (-W x)) := by field_simp [hZ0] <;> ring
  rw [he]
  exact (div_le_div_iff_of_pos_right hZ).mpr h

end
end TheoremA2.BrascampLieb
