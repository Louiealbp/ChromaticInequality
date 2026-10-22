module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebCompactEnergy
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

abbrev correspondenceBrascampLiebMeasure (W : E → ℝ) : Measure E :=
  correspondenceWeightedEllipticMeasure (bakryEmeryGibbsWeight W)

theorem correspondenceBrascampLieb_integral_density
    (W g : E → ℝ) (hW : Continuous W) :
    (∫ x, g x ∂correspondenceBrascampLiebMeasure W) =
      ∫ x, g x * bakryEmeryGibbsWeight W x := by
  unfold correspondenceBrascampLiebMeasure correspondenceWeightedEllipticMeasure
  have hw : Continuous (bakryEmeryGibbsWeight W) := Real.continuous_exp.comp hW.neg
  rw [integral_withDensity_eq_integral_toReal_smul
    hw.measurable.ennreal_ofReal
    (ae_of_all volume fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal (show 0 ≤ bakryEmeryGibbsWeight W x from (Real.exp_pos _).le), smul_eq_mul]
  exact mul_comm _ _

theorem correspondenceBrascampLieb_integrable_compact
    (W g : E → ℝ) (hW : Continuous W) (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable g (correspondenceBrascampLiebMeasure W) := by
  apply (correspondenceWeightedElliptic_integrable_density
    (bakryEmeryGibbsWeight W) g (Real.continuous_exp.comp hW.neg)
    (fun _ => Real.exp_pos _)).mpr
  exact ((Real.continuous_exp.comp hW.neg).mul hg).integrable_of_hasCompactSupport hc.mul_left

#print axioms correspondenceBrascampLieb_integral_density
end
end GinibrePoincare
