module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebHessian
public import Mathlib.Topology.Instances.Matrix
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

def correspondenceBrascampLiebInverseEnergy (W g : E → ℝ) (b : ι → E) (x : E) : ℝ :=
  correspondenceBrascampLiebGradient g b x ⬝ᵥ
    (correspondenceBrascampLiebHessian W b x)⁻¹ *ᵥ correspondenceBrascampLiebGradient g b x

theorem correspondenceBrascampLieb_hessian_continuous
    (W : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W) :
    Continuous (correspondenceBrascampLiebHessian W b) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((correspondenceBrascampLieb_direction_contDiff (m := 1) hW (b i)).fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const

theorem correspondenceBrascampLieb_hessian_inverse_continuous
    (W : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef) :
    Continuous (fun x => (correspondenceBrascampLiebHessian W b x)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hd : (correspondenceBrascampLiebHessian W b x).det ≠ 0 :=
    ((correspondenceBrascampLiebHessian W b x).isUnit_iff_isUnit_det.mp (hpos x).isUnit).ne_zero
  have hi : ContinuousAt Ring.inverse (correspondenceBrascampLiebHessian W b x).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  exact (continuousAt_matrix_inv _ hi).comp
    (correspondenceBrascampLieb_hessian_continuous W b hW).continuousAt

theorem correspondenceBrascampLieb_inverse_energy_continuous
    (W g : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ 1 g)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef) :
    Continuous (correspondenceBrascampLiebInverseEnergy W g b) := by
  have hG : Continuous (correspondenceBrascampLiebGradient g b) := by
    apply continuous_pi
    intro i
    exact (hg.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  have hI := correspondenceBrascampLieb_hessian_inverse_continuous W b hW hpos
  unfold correspondenceBrascampLiebInverseEnergy
  exact hG.dotProduct (hI.matrix_mulVec hG)

theorem correspondenceBrascampLieb_inverse_energy_compact
    (W g : E → ℝ) (b : ι → E) (hc : HasCompactSupport g) :
    HasCompactSupport (correspondenceBrascampLiebInverseEnergy W g b) := by
  apply (hc.fderiv ℝ).mono
  intro x hx hz
  apply hx
  have hG : correspondenceBrascampLiebGradient g b x = 0 := by
    funext i
    simp [correspondenceBrascampLiebGradient, bakryEmeryGibbsDirectional, hz]
  simp [correspondenceBrascampLiebInverseEnergy, hG]

theorem correspondenceBrascampLieb_inverse_energy_integrable
    (W g : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef) :
    Integrable (fun x => correspondenceBrascampLiebInverseEnergy W g b x *
      bakryEmeryGibbsWeight W x) := by
  exact ((correspondenceBrascampLieb_inverse_energy_continuous W g b hW hg hpos).mul
    (Real.continuous_exp.comp hW.continuous.neg)).integrable_of_hasCompactSupport
      ((correspondenceBrascampLieb_inverse_energy_compact W g b hc).mul_right)

#print axioms correspondenceBrascampLieb_inverse_energy_integrable
end
end GinibrePoincare
