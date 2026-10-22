module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebJets
@[expose] public section
open MeasureTheory Measure
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def correspondenceBrascampLiebAdjoint (W f : E → ℝ) (v : E) (x : E) : ℝ :=
  bakryEmeryGibbsDirectional W v x * f x - bakryEmeryGibbsDirectional f v x

theorem correspondenceBrascampLieb_adjoint_contDiff (W f : E → ℝ) (v : E)
    (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (correspondenceBrascampLiebAdjoint W f v) := by
  exact ((correspondenceBrascampLieb_direction_contDiff (m := 1) hW v).mul
    (hf.of_le (by norm_num))).sub
      (correspondenceBrascampLieb_direction_contDiff (m := 1) hf v)

theorem correspondenceBrascampLieb_adjoint_commutator
    (W f : E → ℝ) (v w : E) (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 2 f)
    (x : E) :
    bakryEmeryGibbsDirectional (correspondenceBrascampLiebAdjoint W f v) w x =
      correspondenceBrascampLiebAdjoint W (bakryEmeryGibbsDirectional f w) v x +
        bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x * f x := by
  have hWv := correspondenceBrascampLieb_direction_contDiff (m := 1) hW v
  have hfv := correspondenceBrascampLieb_direction_contDiff (m := 1) hf v
  unfold correspondenceBrascampLiebAdjoint
  rw [correspondenceBrascampLieb_direction_sub
    (hWv.mul (hf.of_le (by norm_num))) hfv,
    correspondenceBrascampLieb_direction_mul hWv (hf.of_le (by norm_num))]
  rw [congrFun (correspondenceBrascampLieb_direction_commute hf v w) x]
  ring

variable [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- Exact variable-Hessian weighted commutator identity for compact tests. -/
theorem correspondenceBrascampLieb_adjoint_integral
    (W f g : E → ℝ) (v w : E)
    (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x, correspondenceBrascampLiebAdjoint W f v x *
      correspondenceBrascampLiebAdjoint W g w x * bakryEmeryGibbsWeight W x) =
    (∫ x, bakryEmeryGibbsDirectional f w x * bakryEmeryGibbsDirectional g v x *
      bakryEmeryGibbsWeight W x) +
    ∫ x, bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x *
      f x * g x * bakryEmeryGibbsWeight W x := by
  have hfw := correspondenceBrascampLieb_direction_contDiff (m := 1) hf w
  have hWv := correspondenceBrascampLieb_direction_contDiff (m := 1) hW v
  have hweight : Continuous (bakryEmeryGibbsWeight W) :=
    Real.continuous_exp.comp hW.continuous.neg
  have hH : Continuous (bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w) :=
    (hWv.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  have hA := correspondenceBrascampLieb_adjoint_contDiff W f v hW hf
  have hA' : Continuous (correspondenceBrascampLiebAdjoint W
      (bakryEmeryGibbsDirectional f w) v) := by
    exact (((hW.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuous.clm_apply continuous_const |>.mul
        hfw.continuous).sub
          ((hfw.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const)
  have hiA : Integrable (fun x => correspondenceBrascampLiebAdjoint W
      (bakryEmeryGibbsDirectional f w) v x * g x * bakryEmeryGibbsWeight W x) :=
    ((hA'.mul hg.continuous).mul hweight).integrable_of_hasCompactSupport
      (hgc.mul_left.mul_right)
  have hiH : Integrable (fun x =>
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x *
        f x * g x * bakryEmeryGibbsWeight W x) :=
    (((hH.mul hf.continuous).mul hg.continuous).mul hweight).integrable_of_hasCompactSupport
      (hgc.mul_left.mul_right)
  have h1 := bakryEmeryGibbs_directional_adjoint W
    (correspondenceBrascampLiebAdjoint W f v) g w
    (hW.of_le (by norm_num)) hA hg hgc
  have h2 := bakryEmeryGibbs_directional_adjoint W g
    (bakryEmeryGibbsDirectional f w) v (hW.of_le (by norm_num)) hg hfw
    (hfc.fderiv_apply ℝ w)
  change (∫ x, bakryEmeryGibbsDirectional (correspondenceBrascampLiebAdjoint W f v) w x *
    g x * bakryEmeryGibbsWeight W x) = _ at h1
  change (∫ x, bakryEmeryGibbsDirectional (correspondenceBrascampLiebAdjoint W f v) w x *
    g x * bakryEmeryGibbsWeight W x) =
    ∫ x, correspondenceBrascampLiebAdjoint W f v x *
      correspondenceBrascampLiebAdjoint W g w x * bakryEmeryGibbsWeight W x at h1
  rw [← h1]
  simp_rw [correspondenceBrascampLieb_adjoint_commutator W f v w hW hf]
  have hsplit : (∫ x, (correspondenceBrascampLiebAdjoint W
      (bakryEmeryGibbsDirectional f w) v x +
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x * f x) *
      g x * bakryEmeryGibbsWeight W x) =
      (∫ x, correspondenceBrascampLiebAdjoint W (bakryEmeryGibbsDirectional f w) v x *
        g x * bakryEmeryGibbsWeight W x) +
      ∫ x, bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x *
        f x * g x * bakryEmeryGibbsWeight W x := by
    simp_rw [add_mul]
    exact integral_add hiA hiH
  rw [hsplit]
  congr 1
  calc
    _ = ∫ x, g x * correspondenceBrascampLiebAdjoint W
        (bakryEmeryGibbsDirectional f w) v x * bakryEmeryGibbsWeight W x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = ∫ x, bakryEmeryGibbsDirectional g v x * bakryEmeryGibbsDirectional f w x *
        bakryEmeryGibbsWeight W x := h2.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring

#print axioms correspondenceBrascampLieb_adjoint_integral
#print axioms correspondenceBrascampLieb_adjoint_commutator
end
end GinibrePoincare
