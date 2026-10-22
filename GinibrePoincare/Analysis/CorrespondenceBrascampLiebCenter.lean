module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebConstants
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebMass
@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

 def correspondenceBrascampLiebMean (W g : E → ℝ) : ℝ :=
  (∫ x, g x ∂correspondenceBrascampLiebMeasure W) / (∫ x, bakryEmeryGibbsWeight W x)

 def correspondenceBrascampLiebCenter (W g : E → ℝ) (x : E) : ℝ :=
  g x - correspondenceBrascampLiebMean W g

 theorem correspondenceBrascampLieb_center_memLp
    (W g : E → ℝ) [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hg : MemLp g 2 (correspondenceBrascampLiebMeasure W)) :
    MemLp (correspondenceBrascampLiebCenter W g) 2 (correspondenceBrascampLiebMeasure W) :=
  hg.sub (memLp_const (correspondenceBrascampLiebMean W g))

 theorem correspondenceBrascampLieb_center_integral
    (W g : E → ℝ) [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hi : Integrable (bakryEmeryGibbsWeight W))
    (hg : MemLp g 2 (correspondenceBrascampLiebMeasure W)) :
    (∫ x, correspondenceBrascampLiebCenter W g x ∂correspondenceBrascampLiebMeasure W) = 0 := by
  have hig : Integrable g (correspondenceBrascampLiebMeasure W) :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (by norm_num))
  have hm : (correspondenceBrascampLiebMeasure W).real Set.univ =
      ∫ x, bakryEmeryGibbsWeight W x := by
    rw [Measure.real, correspondenceBrascampLieb_mass W hi,
      ENNReal.toReal_ofReal (correspondenceBrascampLieb_positive_mass W hi).le]
  unfold correspondenceBrascampLiebCenter
  rw [integral_sub hig (integrable_const _), integral_const, hm]
  simp only [smul_eq_mul, correspondenceBrascampLiebMean]
  field_simp [(correspondenceBrascampLieb_positive_mass W hi).ne']
  ring

 theorem correspondenceBrascampLieb_center_orthogonal
    (W g : E → ℝ) [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hi : Integrable (bakryEmeryGibbsWeight W))
    (hg : MemLp g 2 (correspondenceBrascampLiebMeasure W)) :
    (correspondenceBrascampLieb_center_memLp W g hg).toLp
      (correspondenceBrascampLiebCenter W g) ∈ (ℝ ∙ correspondenceBrascampLiebOneL2 W)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  unfold correspondenceBrascampLiebOneL2
  rw [correspondenceBrascampLieb_toLp_inner]
  simp only [mul_one]
  exact correspondenceBrascampLieb_center_integral W g hi hg

 theorem correspondenceBrascampLieb_center_gradient
    {ι : Type*} [Fintype ι] (W g : E → ℝ) (b : ι → E) :
    correspondenceBrascampLiebGradient (correspondenceBrascampLiebCenter W g) b =
      correspondenceBrascampLiebGradient g b := by
  funext x i
  unfold correspondenceBrascampLiebGradient bakryEmeryGibbsDirectional correspondenceBrascampLiebCenter
  rw [fderiv_sub_const]

#print axioms correspondenceBrascampLieb_center_orthogonal
#print axioms correspondenceBrascampLieb_center_gradient
end
end GinibrePoincare
