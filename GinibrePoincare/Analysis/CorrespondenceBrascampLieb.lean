module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebDense
@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The concrete real Brascamp–Lieb inequality with the variable inverse
Hessian, for arbitrary C² strictly convex integrable Gibbs potentials.
There is no uniform lower curvature assumption or elliptic certificate. -/
theorem correspondenceBrascampLieb_variance
    (W g : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hg : ContDiff ℝ 1 g) (hgL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W))
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W)) :
    (∫ x, correspondenceBrascampLiebCenter W g x^2 ∂correspondenceBrascampLiebMeasure W) ≤
      ∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W := by
  letI := correspondenceBrascampLieb_finite_measure W hWi
  have hgc : ContDiff ℝ 1 (correspondenceBrascampLiebCenter W g) := hg.sub contDiff_const
  have hgcL2 := correspondenceBrascampLieb_center_memLp W g hgL2
  have he : correspondenceBrascampLiebInverseEnergy W (correspondenceBrascampLiebCenter W g) b =
      correspondenceBrascampLiebInverseEnergy W g b := by
    funext x
    unfold correspondenceBrascampLiebInverseEnergy
    rw [correspondenceBrascampLieb_center_gradient W g b]
  have hgcE : Integrable (correspondenceBrascampLiebInverseEnergy W
      (correspondenceBrascampLiebCenter W g) b) (correspondenceBrascampLiebMeasure W) := by
    rw [he]
    exact hgE
  have hc : hgcL2.toLp (correspondenceBrascampLiebCenter W g) ∈
      (correspondenceBrascampLiebCoreRange W b hW).topologicalClosure := by
    rw [correspondenceBrascampLieb_core_dense_centered W b hW]
    exact correspondenceBrascampLieb_center_orthogonal W g hWi hgL2
  have hv := correspondenceBrascampLieb_closed_core_bound W (correspondenceBrascampLiebCenter W g)
    b hW hgc hpos hgcL2 hgcE hc
  rwa [he] at hv

/-- Probability-normalized form of the exact inverse-Hessian inequality. -/
theorem correspondenceBrascampLieb_probability_variance
    (W g : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hMass : (∫ x, bakryEmeryGibbsWeight W x) = 1)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hg : ContDiff ℝ 1 g) (hgL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W))
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W)) :
    (∫ x, (g x-(∫ y, g y ∂correspondenceBrascampLiebMeasure W))^2
      ∂correspondenceBrascampLiebMeasure W) ≤
      ∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W := by
  simpa only [correspondenceBrascampLiebCenter, correspondenceBrascampLiebMean, hMass, div_one] using
    correspondenceBrascampLieb_variance W g b hW hWi hpos hg hgL2 hgE

#print axioms correspondenceBrascampLieb_variance
#print axioms correspondenceBrascampLieb_probability_variance
end
end GinibrePoincare
