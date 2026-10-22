module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebCoreRange
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebCoreDual
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

def correspondenceBrascampLiebOneL2 (W : E → ℝ)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)] :
    Lp ℝ 2 (correspondenceBrascampLiebMeasure W) :=
  (memLp_const (μ := correspondenceBrascampLiebMeasure W) (p := 2) (1 : ℝ)).toLp (fun _ => 1)

theorem correspondenceBrascampLieb_constants_orthogonal
    (W : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)] :
    (ℝ ∙ correspondenceBrascampLiebOneL2 W) ≤
      (correspondenceBrascampLiebCoreRange W b hW)ᗮ := by
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨f, rfl⟩
  unfold correspondenceBrascampLiebOneL2 correspondenceBrascampLiebCoreL2
  rw [correspondenceBrascampLieb_toLp_inner]
  simp only [mul_one]
  rw [correspondenceBrascampLieb_integral_density W _ hW.continuous]
  exact bakryEmeryGibbs_core_stationarity W f.val b (hW.of_le (by norm_num))
    (f.smooth.of_le (by norm_num)) f.compact

/-- Final Hilbert dual step once centered-range membership has been obtained
from the concrete weighted elliptic theorem. This is an internal reduction. -/
theorem correspondenceBrascampLieb_closed_core_bound
    (W g : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ 1 g)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hgL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W))
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W))
    (hu : hgL2.toLp g ∈ (correspondenceBrascampLiebCoreRange W b hW).topologicalClosure) :
    (∫ x, g x^2 ∂correspondenceBrascampLiebMeasure W) ≤
      ∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W := by
  rw [← correspondenceBrascampLieb_toLp_norm_sq _ g hgL2]
  apply correspondenceBrascampLieb_duality (hgL2.toLp g)
    (correspondenceBrascampLiebCoreRange W b hW)
    (∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W)
  · apply integral_nonneg
    intro x
    change 0 ≤ correspondenceBrascampLiebGradient g b x ⬝ᵥ
      (correspondenceBrascampLiebHessian W b x)⁻¹ *ᵥ correspondenceBrascampLiebGradient g b x
    simpa only [star_trivial] using
      (hpos x).posSemidef.inv.dotProduct_mulVec_nonneg (correspondenceBrascampLiebGradient g b x)
  · exact hu
  · rintro _ ⟨f, rfl⟩
    exact correspondenceBrascampLieb_core_dual_bound W g b hW hg hpos hgL2 hgE f

#print axioms correspondenceBrascampLieb_constants_orthogonal
#print axioms correspondenceBrascampLieb_closed_core_bound
end
end GinibrePoincare
