module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebCore
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebDuality
@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem correspondenceBrascampLieb_toLp_inner
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]
  simp [mul_comm]

 theorem correspondenceBrascampLieb_toLp_norm_sq
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ x, f x^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, correspondenceBrascampLieb_toLp_inner μ f f hf hf]
  simp only [pow_two]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem correspondenceBrascampLieb_core_dual_bound
    (W g : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ 1 g)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hgL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W))
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W))
    (f : CorrespondenceBrascampLiebCompactTest E) :
    (inner ℝ (hgL2.toLp g) (correspondenceBrascampLiebCoreL2 W b hW f))^2 ≤
    (∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W) *
    ‖correspondenceBrascampLiebCoreL2 W b hW f‖^2 := by
  unfold correspondenceBrascampLiebCoreL2
  rw [correspondenceBrascampLieb_toLp_inner, correspondenceBrascampLieb_toLp_norm_sq]
  exact correspondenceBrascampLieb_compact_generator_bound W g f.val b hW hg
    (f.smooth.of_le (by norm_num)) f.compact hpos hgE

#print axioms correspondenceBrascampLieb_core_dual_bound
end
end GinibrePoincare
