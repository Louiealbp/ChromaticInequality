module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebGibbs
@[expose] public section
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem correspondenceBrascampLieb_density_derivative
    (W : E → ℝ) (hW : ContDiff ℝ 1 W) (v x : E) :
    bakryEmeryGibbsDirectional (bakryEmeryGibbsWeight W) v x =
      -bakryEmeryGibbsDirectional W v x * bakryEmeryGibbsWeight W x := by
  have hd := ((hW.differentiable (by norm_num) x).hasFDerivAt).neg.exp
  change HasFDerivAt (bakryEmeryGibbsWeight W) _ x at hd
  unfold bakryEmeryGibbsDirectional
  rw [hd.fderiv]
  simp [bakryEmeryGibbsWeight, mul_comm]

 theorem correspondenceBrascampLieb_density_generator
    {ι : Type*} [Fintype ι] (W f : E → ℝ) (b : ι → E)
    (hW : ContDiff ℝ 1 W) (x : E) :
    bakryEmeryGibbsGenerator W b f x =
    (∑ i, bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i) x) +
    ∑ i, (bakryEmeryGibbsWeight W x)⁻¹ *
      bakryEmeryGibbsDirectional (bakryEmeryGibbsWeight W) (b i) x *
      bakryEmeryGibbsDirectional f (b i) x := by
  simp_rw [correspondenceBrascampLieb_density_derivative W hW]
  unfold bakryEmeryGibbsGenerator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hn : bakryEmeryGibbsWeight W x ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

#print axioms correspondenceBrascampLieb_density_generator
end
end GinibrePoincare
