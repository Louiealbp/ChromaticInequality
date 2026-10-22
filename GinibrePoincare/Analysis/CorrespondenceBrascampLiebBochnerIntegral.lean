module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebBochner
@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- Literal weighted generator-square identity, with every analytic
integration input supplied by smoothness and compact support. -/
theorem correspondenceBrascampLieb_bochner_integral
    {ι : Type*} [Fintype ι] (W f : E → ℝ) (b : ι → E)
    (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    (∫ x, bakryEmeryGibbsGenerator W b f x ^ 2 * bakryEmeryGibbsWeight W x) =
    (∑ i, ∑ j, ∫ x,
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b j) x ^ 2 *
      bakryEmeryGibbsWeight W x) +
    ∑ i, ∑ j, ∫ x,
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W (b i)) (b j) x *
      bakryEmeryGibbsDirectional f (b i) x * bakryEmeryGibbsDirectional f (b j) x *
      bakryEmeryGibbsWeight W x := by
  let A (i : ι) := correspondenceBrascampLiebAdjoint W
    (bakryEmeryGibbsDirectional f (b i)) (b i)
  have hdf (i : ι) : ContDiff ℝ 2 (bakryEmeryGibbsDirectional f (b i)) :=
    correspondenceBrascampLieb_direction_contDiff (m := 2) hf (b i)
  have hA (i : ι) : Continuous (A i) :=
    (correspondenceBrascampLieb_adjoint_contDiff W _ _ hW (hdf i)).continuous
  have hAc (i : ι) : HasCompactSupport (A i) := by
    exact ((hc.fderiv_apply ℝ (b i)).mul_left).sub
      ((hc.fderiv_apply ℝ (b i)).fderiv_apply ℝ (b i))
  have hweight : Continuous (bakryEmeryGibbsWeight W) :=
    Real.continuous_exp.comp hW.continuous.neg
  have hi (i j : ι) : Integrable (fun x => A i x * A j x * bakryEmeryGibbsWeight W x) :=
    (((hA i).mul (hA j)).mul hweight).integrable_of_hasCompactSupport
      ((hAc i).mul_right.mul_right)
  have hp (x : E) : bakryEmeryGibbsGenerator W b f x ^ 2 * bakryEmeryGibbsWeight W x =
      ∑ i, ∑ j, A i x * A j x * bakryEmeryGibbsWeight W x := by
    have hL : bakryEmeryGibbsGenerator W b f x = -(∑ i, A i x) := by
      simp only [bakryEmeryGibbsGenerator, A, correspondenceBrascampLiebAdjoint]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hL]
    calc
      _ = (∑ i, A i x) * ((∑ j, A j x) * bakryEmeryGibbsWeight W x) := by ring
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
  calc
    _ = ∫ x, ∑ i, ∑ j, A i x * A j x * bakryEmeryGibbsWeight W x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hp x
    _ = ∑ i, ∑ j, ∫ x, A i x * A j x * bakryEmeryGibbsWeight W x := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        exact integral_finsetSum _ (fun j _ => hi i j)
      · intro i _
        exact integrable_finsetSum _ (fun j _ => hi i j)
    _ = _ := correspondenceBrascampLieb_bochner_sum W f b hW hf hc

#print axioms correspondenceBrascampLieb_bochner_integral
end
end GinibrePoincare
