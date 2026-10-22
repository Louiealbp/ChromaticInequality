import BrascampLieb.BoxPenalty
import Mathlib.Algebra.Order.Star.Real
import GinibrePoincare.Analysis.CorrespondenceBrascampLiebHessian

/-!
# Actual Hessians of the separable approximating potentials

The matrix entries are computed from Fréchet derivatives in an actual
orthonormal basis. This connects the one-dimensional constructions to the
Hessian consumed by the verified whole-space Brascamp–Lieb theorem.
-/

namespace TheoremA2.BrascampLieb

open MeasureTheory Measure Set Filter GinibrePoincare
open scoped Topology ContDiff BigOperators Matrix RealInnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actualHessian_add (b : OrthonormalBasis ι ℝ E)
    {W P : E → ℝ} (hW : ContDiff ℝ 2 W) (hP : ContDiff ℝ 2 P) (x : E) :
    correspondenceBrascampLiebHessian (fun y => W y + P y) b x =
      correspondenceBrascampLiebHessian W b x +
        correspondenceBrascampLiebHessian P b x := by
  have hd (i : ι) : bakryEmeryGibbsDirectional (fun y => W y + P y) (b i) =
      fun y => bakryEmeryGibbsDirectional W (b i) y +
        bakryEmeryGibbsDirectional P (b i) y := by
    funext y
    simp only [bakryEmeryGibbsDirectional,
      fderiv_fun_add (hW.differentiable (by norm_num) y) (hP.differentiable (by norm_num) y),
      ContinuousLinearMap.add_apply]
  ext i j
  simp only [correspondenceBrascampLiebHessian, hd, Matrix.add_apply]
  change (fderiv ℝ (fun y => bakryEmeryGibbsDirectional W (b i) y +
    bakryEmeryGibbsDirectional P (b i) y) x) (b j) =
    (fderiv ℝ (bakryEmeryGibbsDirectional W (b i)) x) (b j) +
      (fderiv ℝ (bakryEmeryGibbsDirectional P (b i)) x) (b j)
  rw [fderiv_fun_add
    ((correspondenceBrascampLieb_direction_contDiff (m := 1) hW (b i)).differentiable
      (by norm_num) x)
    ((correspondenceBrascampLieb_direction_contDiff (m := 1) hP (b i)).differentiable
      (by norm_num) x)]
  rfl

theorem actualHessian_const_mul (b : OrthonormalBasis ι ℝ E)
    {P : E → ℝ} (hP : ContDiff ℝ 2 P) (c : ℝ) (x : E) :
    correspondenceBrascampLiebHessian (fun y => c * P y) b x =
      c • correspondenceBrascampLiebHessian P b x := by
  have hd (i : ι) : bakryEmeryGibbsDirectional (fun y => c * P y) (b i) =
      fun y => c * bakryEmeryGibbsDirectional P (b i) y := by
    funext y
    simp only [bakryEmeryGibbsDirectional,
      fderiv_const_mul (hP.differentiable (by norm_num) y),
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  ext i j
  simp only [correspondenceBrascampLiebHessian, hd, Matrix.smul_apply, smul_eq_mul]
  change (fderiv ℝ (fun y => c * bakryEmeryGibbsDirectional P (b i) y) x) (b j) =
    c * (fderiv ℝ (bakryEmeryGibbsDirectional P (b i)) x) (b j)
  rw [fderiv_const_mul
    ((correspondenceBrascampLieb_direction_contDiff (m := 1) hP (b i)).differentiable
      (by norm_num) x)]
  rfl

def separablePotential (b : OrthonormalBasis ι ℝ E) (φ : ι → ℝ → ℝ) (x : E) : ℝ :=
  ∑ i, φ i ⟪b i, x⟫

theorem separablePotential_contDiff (b : OrthonormalBasis ι ℝ E)
    {φ : ι → ℝ → ℝ} (hφ : ∀ i, ContDiff ℝ 2 (φ i)) :
    ContDiff ℝ 2 (separablePotential b φ) := by
  apply ContDiff.sum
  intro i _
  exact (hφ i).comp (innerSL ℝ (b i)).contDiff

theorem separablePotential_directional (b : OrthonormalBasis ι ℝ E)
    {φ : ι → ℝ → ℝ} (hφ : ∀ i, Differentiable ℝ (φ i)) (i : ι) (x : E) :
    bakryEmeryGibbsDirectional (separablePotential b φ) (b i) x =
      deriv (φ i) ⟪b i, x⟫ := by
  have hd : HasFDerivAt (separablePotential b φ)
      (∑ j, (deriv (φ j) ⟪b j, x⟫) • innerSL ℝ (b j)) x := by
    apply HasFDerivAt.fun_sum
    intro j _
    exact ((hφ j ⟪b j, x⟫).hasDerivAt).comp_hasFDerivAt x (innerSL ℝ (b j)).hasFDerivAt
  unfold bakryEmeryGibbsDirectional
  rw [hd.fderiv]
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, b.inner_eq_ite]

theorem separablePotential_hessian (b : OrthonormalBasis ι ℝ E)
    {φ : ι → ℝ → ℝ} (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (x : E) :
    correspondenceBrascampLiebHessian (separablePotential b φ) b x =
      Matrix.diagonal (fun i => deriv (deriv (φ i)) ⟪b i, x⟫) := by
  have hd (i : ι) : Differentiable ℝ (φ i) := (hφ i).differentiable (by norm_num)
  ext i j
  unfold correspondenceBrascampLiebHessian
  have heq : bakryEmeryGibbsDirectional (separablePotential b φ) (b i) =
      fun y => deriv (φ i) ⟪b i, y⟫ :=
    funext (separablePotential_directional b hd i)
  rw [heq]
  have hsecond := (((hφ i).differentiable_deriv_two ⟪b i, x⟫).hasDerivAt).comp_hasFDerivAt x
    (innerSL ℝ (b i)).hasFDerivAt
  change HasFDerivAt (fun y => deriv (φ i) ⟪b i, y⟫)
    (deriv (deriv (φ i)) ⟪b i, x⟫ • innerSL ℝ (b i)) x at hsecond
  change (fderiv ℝ (fun y => deriv (φ i) ⟪b i, y⟫) x) (b j) = _
  calc
    _ = deriv (deriv (φ i)) ⟪b i, x⟫ * ⟪b i, b j⟫ := by
      exact congrArg (fun L : E →L[ℝ] ℝ => L (b j)) hsecond.fderiv
    _ = _ := by simp [b.inner_eq_ite, Matrix.diagonal_apply]


/-- The actual finite-dimensional hard-box penalty. -/
def finiteBoxPenalty (b : OrthonormalBasis ι ℝ E) (r : ℝ) : E → ℝ :=
  separablePotential b (fun _ => boxPenalty r)

theorem finiteBoxPenalty_contDiff (b : OrthonormalBasis ι ℝ E) (r : ℝ) :
    ContDiff ℝ 2 (finiteBoxPenalty b r) :=
  separablePotential_contDiff b (fun _ => boxPenalty_contDiff r)

theorem finiteBoxPenalty_nonneg (b : OrthonormalBasis ι ℝ E) (r : ℝ) (x : E) :
    0 ≤ finiteBoxPenalty b r x :=
  Finset.sum_nonneg (fun i _ => boxPenalty_nonneg r ⟪b i, x⟫)

theorem finiteBoxPenalty_eq_zero_iff (b : OrthonormalBasis ι ℝ E)
    {r : ℝ} (hr : 0 ≤ r) (x : E) :
    finiteBoxPenalty b r x = 0 ↔ ∀ i, |⟪b i, x⟫| ≤ r := by
  unfold finiteBoxPenalty separablePotential
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => boxPenalty_nonneg r ⟪b i, x⟫)]
  simp only [Finset.mem_univ, forall_true_left, boxPenalty_eq_zero_iff hr]

theorem finiteBoxPenalty_hessian_posSemidef (b : OrthonormalBasis ι ℝ E)
    (r : ℝ) (x : E) :
    (correspondenceBrascampLiebHessian (finiteBoxPenalty b r) b x).PosSemidef := by
  rw [finiteBoxPenalty, separablePotential_hessian b (fun _ => boxPenalty_contDiff r)]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact boxPenalty_curvature_nonneg r ⟪b i, x⟫

theorem penalized_hessian_posDef (b : OrthonormalBasis ι ℝ E)
    {W : E → ℝ} (hW : ContDiff ℝ 2 W)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (r : ℝ) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    (correspondenceBrascampLiebHessian
      (fun y => W y + c * finiteBoxPenalty b r y) b x).PosDef := by
  rw [actualHessian_add b hW (contDiff_const.mul (finiteBoxPenalty_contDiff b r)),
    actualHessian_const_mul b (finiteBoxPenalty_contDiff b r)]
  exact (hpos x).add_posSemidef ((finiteBoxPenalty_hessian_posSemidef b r x).smul hc)

end
end TheoremA2.BrascampLieb
