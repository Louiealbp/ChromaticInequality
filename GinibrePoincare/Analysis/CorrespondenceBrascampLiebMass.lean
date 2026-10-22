module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebGibbs
@[expose] public section
open MeasureTheory Measure
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

 theorem correspondenceBrascampLieb_mass
    (W : E → ℝ) (hi : Integrable (bakryEmeryGibbsWeight W)) :
    correspondenceBrascampLiebMeasure W Set.univ =
      ENNReal.ofReal (∫ x, bakryEmeryGibbsWeight W x) := by
  unfold correspondenceBrascampLiebMeasure correspondenceWeightedEllipticMeasure
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all volume fun x => (Real.exp_pos _).le)).symm

 theorem correspondenceBrascampLieb_finite_measure
    (W : E → ℝ) (hi : Integrable (bakryEmeryGibbsWeight W)) :
    IsFiniteMeasure (correspondenceBrascampLiebMeasure W) := by
  refine ⟨?_⟩
  rw [correspondenceBrascampLieb_mass W hi]
  exact ENNReal.ofReal_lt_top

 theorem correspondenceBrascampLieb_positive_mass
    (W : E → ℝ) (hi : Integrable (bakryEmeryGibbsWeight W)) :
    0 < ∫ x, bakryEmeryGibbsWeight W x := by
  exact integral_exp_pos hi

theorem correspondenceBrascampLieb_probability_measure
    (W : E → ℝ) (hi : Integrable (bakryEmeryGibbsWeight W))
    (hm : (∫ x, bakryEmeryGibbsWeight W x) = 1) :
    IsProbabilityMeasure (correspondenceBrascampLiebMeasure W) := by
  refine ⟨?_⟩
  rw [correspondenceBrascampLieb_mass W hi, hm]
  norm_num

#print axioms correspondenceBrascampLieb_probability_measure
#print axioms correspondenceBrascampLieb_mass
#print axioms correspondenceBrascampLieb_positive_mass
end
end GinibrePoincare
