module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsGenerator
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
@[expose] public section
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem correspondenceBrascampLieb_direction_contDiff {f : E → ℝ} {m : ℕ∞ω}
    (hf : ContDiff ℝ (m + 1) f) (v : E) :
    ContDiff ℝ m (bakryEmeryGibbsDirectional f v) := by
  exact (hf.fderiv_right le_rfl).clm_apply contDiff_const

 theorem correspondenceBrascampLieb_direction_commute {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (v w : E) :
    bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f v) w =
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f w) v := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have he (a b : E) :
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f a) b x =
        fderiv ℝ (fderiv ℝ f) x b a := by
    unfold bakryEmeryGibbsDirectional
    rw [fderiv_clm_apply hd (differentiableAt_const a)]
    simp
  rw [he, he]
  exact hf.contDiffAt.isSymmSndFDerivAt (by norm_num) w v

theorem correspondenceBrascampLieb_direction_mul {f g : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v : E) (x : E) :
    bakryEmeryGibbsDirectional (fun y => f y * g y) v x =
      bakryEmeryGibbsDirectional f v x * g x +
        f x * bakryEmeryGibbsDirectional g v x := by
  unfold bakryEmeryGibbsDirectional
  change (fderiv ℝ (f * g) x) v = _
  rw [fderiv_mul (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x)]
  simp
  ring

 theorem correspondenceBrascampLieb_direction_sub {f g : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v : E) (x : E) :
    bakryEmeryGibbsDirectional (fun y => f y - g y) v x =
      bakryEmeryGibbsDirectional f v x - bakryEmeryGibbsDirectional g v x := by
  unfold bakryEmeryGibbsDirectional
  change (fderiv ℝ (f - g) x) v = _
  rw [fderiv_sub (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x)]
  simp

#print axioms correspondenceBrascampLieb_direction_mul
#print axioms correspondenceBrascampLieb_direction_sub
#print axioms correspondenceBrascampLieb_direction_commute
end
end GinibrePoincare
