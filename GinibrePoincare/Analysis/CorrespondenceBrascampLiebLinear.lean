module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebCore
@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem correspondenceBrascampLieb_direction_add {f g : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v : E) :
    bakryEmeryGibbsDirectional (f+g) v =
      bakryEmeryGibbsDirectional f v + bakryEmeryGibbsDirectional g v := by
  funext x
  unfold bakryEmeryGibbsDirectional
  rw [fderiv_add (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)]
  simp

 theorem correspondenceBrascampLieb_direction_smul {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (c : ℝ) (v : E) :
    bakryEmeryGibbsDirectional (c • f) v = c • bakryEmeryGibbsDirectional f v := by
  funext x
  unfold bakryEmeryGibbsDirectional
  rw [fderiv_const_smul (hf.differentiable (by norm_num) x)]
  simp

variable {ι : Type*} [Fintype ι]
 theorem correspondenceBrascampLieb_generator_add
    (W f g : E → ℝ) (b : ι → E) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    bakryEmeryGibbsGenerator W b (f+g) =
      bakryEmeryGibbsGenerator W b f + bakryEmeryGibbsGenerator W b g := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  funext x
  unfold bakryEmeryGibbsGenerator
  simp_rw [correspondenceBrascampLieb_direction_add hf1 hg1]
  simp_rw [correspondenceBrascampLieb_direction_add
    (correspondenceBrascampLieb_direction_contDiff (m := 1) hf _)
    (correspondenceBrascampLieb_direction_contDiff (m := 1) hg _)]
  simp only [Pi.add_apply]
  simp_rw [mul_add, add_sub_add_comm, Finset.sum_add_distrib]

 theorem correspondenceBrascampLieb_generator_smul
    (W f : E → ℝ) (b : ι → E) (hf : ContDiff ℝ 2 f) (c : ℝ) :
    bakryEmeryGibbsGenerator W b (c • f) = c • bakryEmeryGibbsGenerator W b f := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  funext x
  unfold bakryEmeryGibbsGenerator
  simp_rw [correspondenceBrascampLieb_direction_smul hf1 c]
  simp_rw [correspondenceBrascampLieb_direction_smul
    (correspondenceBrascampLieb_direction_contDiff (m := 1) hf _) c]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms correspondenceBrascampLieb_generator_add
#print axioms correspondenceBrascampLieb_generator_smul
end
end GinibrePoincare
