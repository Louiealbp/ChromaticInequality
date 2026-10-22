import BrascampLieb.SeparableHessian
import BrascampLieb.WeightedLimit
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The inverse-Hessian variance inequality on an actual closed coordinate box

The proof adds the concrete convex C² penalty to a globally defined C²
potential, applies the verified whole-space inequality, and passes all four
Lebesgue moments to the exact restricted integrals. The hypotheses concern
ordinary smoothness, curvature and integrability of the given potential;
no box-domain functional inequality is assumed.
-/

namespace TheoremA2.BrascampLieb

open MeasureTheory Measure Set Filter GinibrePoincare
open scoped Topology ContDiff BigOperators Matrix RealInnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual restriction to the zero set of a convex C² penalty. -/
theorem penalty_restriction_weighted_variance
    (W g P : E → ℝ) (b : OrthonormalBasis ι ℝ E) (D : E → Matrix ι ι ℝ)
    (hW : ContDiff ℝ 2 W) (hP : ContDiff ℝ 2 P)
    (hP0 : ∀ x, 0 ≤ P x)
    (hHP : ∀ x, (correspondenceBrascampLiebHessian P b x).PosSemidef)
    (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hD : ∀ x, (D x).PosDef)
    (hHD : ∀ x, (correspondenceBrascampLiebHessian W b x - D x).PosSemidef)
    (hg : ContDiff ℝ 1 g)
    (hg1 : Integrable (fun x => g x * bakryEmeryGibbsWeight W x))
    (hg2 : Integrable (fun x => g x ^ 2 * bakryEmeryGibbsWeight W x))
    (hR : Integrable (fun x =>
      (correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
        correspondenceBrascampLiebGradient g b x) * bakryEmeryGibbsWeight W x))
    (hZ : 0 < ∫ x in {x | P x = 0}, bakryEmeryGibbsWeight W x) :
    (∫ x in {x | P x = 0}, g x ^ 2 * bakryEmeryGibbsWeight W x) -
      (∫ x in {x | P x = 0}, g x * bakryEmeryGibbsWeight W x) ^ 2 /
        (∫ x in {x | P x = 0}, bakryEmeryGibbsWeight W x) ≤
      ∫ x in {x | P x = 0},
        (correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
          correspondenceBrascampLiebGradient g b x) * bakryEmeryGibbsWeight W x := by
  let Wn : ℕ → E → ℝ := fun n x => W x + (n : ℝ) * P x
  let R : E → ℝ := fun x =>
    (correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
      correspondenceBrascampLiebGradient g b x) * bakryEmeryGibbsWeight W x
  have hw (n : ℕ) (x : E) : bakryEmeryGibbsWeight (Wn n) x =
      bakryEmeryGibbsWeight W x * Real.exp (-(n : ℝ) * P x) := by
    simp only [bakryEmeryGibbsWeight, Wn, neg_add, Real.exp_add, neg_mul]
  have hWn (n : ℕ) : ContDiff ℝ 2 (Wn n) := hW.add (contDiff_const.mul hP)
  have hWni (n : ℕ) : Integrable (bakryEmeryGibbsWeight (Wn n)) := by
    change Integrable (fun x => bakryEmeryGibbsWeight (Wn n) x)
    simp_rw [hw]
    exact integrable_penalty_weight volume P _ hP.continuous.measurable hP0 hWi n
  have hHn (n : ℕ) (x : E) :
      (correspondenceBrascampLiebHessian (Wn n) b x - D x).PosSemidef := by
    change (correspondenceBrascampLiebHessian
      (fun y => W y + (n : ℝ) * P y) b x - D x).PosSemidef
    rw [actualHessian_add b hW (contDiff_const.mul hP), actualHessian_const_mul b hP]
    have he : correspondenceBrascampLiebHessian W b x +
        (n : ℝ) • correspondenceBrascampLiebHessian P b x - D x =
        (correspondenceBrascampLiebHessian W b x - D x) +
          (n : ℝ) • correspondenceBrascampLiebHessian P b x := by abel
    rw [he]
    exact (hHD x).add ((hHP x).smul (Nat.cast_nonneg n))
  have hbound (n : ℕ) :
      (∫ x, (g x ^ 2 * bakryEmeryGibbsWeight W x) * Real.exp (-(n : ℝ) * P x)) -
        (∫ x, (g x * bakryEmeryGibbsWeight W x) * Real.exp (-(n : ℝ) * P x)) ^ 2 /
          (∫ x, bakryEmeryGibbsWeight W x * Real.exp (-(n : ℝ) * P x)) ≤
        ∫ x, R x * Real.exp (-(n : ℝ) * P x) := by
    have h2 : Integrable (fun x => g x ^ 2 * bakryEmeryGibbsWeight (Wn n) x) := by
      simp_rw [hw, ← mul_assoc]
      exact integrable_penalty_weight volume P _ hP.continuous.measurable hP0 hg2 n
    have hr : Integrable (fun x =>
        (correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
          correspondenceBrascampLiebGradient g b x) * bakryEmeryGibbsWeight (Wn n) x) := by
      simp_rw [hw, ← mul_assoc]
      exact integrable_penalty_weight volume P _ hP.continuous.measurable hP0 hR n
    have h := wholeSpace_weighted_variance_hessian_bound
      (Wn n) g b D (hWn n) (hWni n) hD (hHn n) hg h2 hr
    simpa only [hw, ← mul_assoc, R] using h
  exact weighted_variance_limit _ _ _ _
    (integral_penalty_limit volume P _ hP.continuous.measurable hP0 hWi)
    (integral_penalty_limit volume P _ hP.continuous.measurable hP0 hg1)
    (integral_penalty_limit volume P _ hP.continuous.measurable hP0 hg2)
    (integral_penalty_limit volume P R hP.continuous.measurable hP0 hR) hZ hbound

/-- The literal closed box in orthonormal coordinates. -/
def coordinateBox (b : OrthonormalBasis ι ℝ E) (r : ℝ) : Set E :=
  {x | ∀ i, |⟪b i, x⟫| ≤ r}

theorem measurableSet_coordinateBox (b : OrthonormalBasis ι ℝ E) (r : ℝ) :
    MeasurableSet (coordinateBox b r) := by
  simp only [coordinateBox, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (isClosed_le ((innerSL ℝ (b i)).continuous.abs) continuous_const).measurableSet

theorem ball_subset_coordinateBox (b : OrthonormalBasis ι ℝ E) {r : ℝ} :
    Metric.ball (0 : E) r ⊆ coordinateBox b r := by
  intro x hx i
  have hn : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hi : |⟪b i, x⟫| ≤ ‖x‖ := by
    simpa only [b.orthonormal.norm_eq_one i, one_mul] using abs_real_inner_le_norm (b i) x
  exact hi.trans hn.le

theorem coordinateBox_mass_pos (b : OrthonormalBasis ι ℝ E) {r : ℝ} (hr : 0 < r)
    (W : E → ℝ) (hWi : Integrable (bakryEmeryGibbsWeight W)) :
    0 < ∫ x in coordinateBox b r, bakryEmeryGibbsWeight W x := by
  have hs : 0 < volume (coordinateBox b r) :=
    (Metric.measure_ball_pos volume (0 : E) hr).trans_le
      (measure_mono (ball_subset_coordinateBox b))
  haveI : NeZero (volume.restrict (coordinateBox b r)) := by
    exact ⟨fun hz => (ne_of_gt hs) (Measure.restrict_eq_zero.mp hz)⟩
  exact integral_exp_pos hWi.integrableOn

/-- The required closed-box inverse-Hessian estimate, derived from the
actual whole-space theorem by the explicit convex penalty limit. -/
theorem box_weighted_variance_hessian_bound
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
    (∫ x in coordinateBox b r, g x ^ 2 * bakryEmeryGibbsWeight W x) -
      (∫ x in coordinateBox b r, g x * bakryEmeryGibbsWeight W x) ^ 2 /
        (∫ x in coordinateBox b r, bakryEmeryGibbsWeight W x) ≤
      ∫ x in coordinateBox b r,
        (correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
          correspondenceBrascampLiebGradient g b x) * bakryEmeryGibbsWeight W x := by
  have he : {x | finiteBoxPenalty b r x = 0} = coordinateBox b r := by
    ext x
    exact finiteBoxPenalty_eq_zero_iff b hr.le x
  have hm : 0 < ∫ x in {x | finiteBoxPenalty b r x = 0}, bakryEmeryGibbsWeight W x := by
    rw [he]
    exact coordinateBox_mass_pos b hr W hWi
  have h := penalty_restriction_weighted_variance W g (finiteBoxPenalty b r) b D hW
    (finiteBoxPenalty_contDiff b r) (finiteBoxPenalty_nonneg b r)
    (finiteBoxPenalty_hessian_posSemidef b r) hWi hD hHD hg hg1 hg2 hR hm
  simpa only [he] using h

end
end TheoremA2.BrascampLieb
