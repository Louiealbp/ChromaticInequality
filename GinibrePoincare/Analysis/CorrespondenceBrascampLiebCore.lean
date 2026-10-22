module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebCompactBound
public import Mathlib.MeasureTheory.Function.L2Space
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

structure CorrespondenceBrascampLiebCompactTest (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  val : E → ℝ
  smooth : ContDiff ℝ ∞ val
  compact : HasCompactSupport val

 theorem correspondenceBrascampLieb_generator_continuous
    (W f : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 3 f) :
    Continuous (bakryEmeryGibbsGenerator W b f) := by
  apply continuous_finsetSum
  intro i _
  have hdf : ContDiff ℝ 2 (bakryEmeryGibbsDirectional f (b i)) :=
    correspondenceBrascampLieb_direction_contDiff (m := 2) hf (b i)
  have hddf : ContDiff ℝ 1
      (bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i)) :=
    correspondenceBrascampLieb_direction_contDiff (m := 1) hdf (b i)
  have hdW : ContDiff ℝ 1 (bakryEmeryGibbsDirectional W (b i)) :=
    correspondenceBrascampLieb_direction_contDiff (m := 1) hW (b i)
  exact hddf.continuous.sub (hdW.continuous.mul hdf.continuous)

 theorem correspondenceBrascampLieb_generator_compact
    (W f : E → ℝ) (b : ι → E) (hc : HasCompactSupport f) :
    HasCompactSupport (bakryEmeryGibbsGenerator W b f) := by
  have hs : HasCompactSupport (∑ i, fun x =>
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i) x -
      bakryEmeryGibbsDirectional W (b i) x * bakryEmeryGibbsDirectional f (b i) x) := by
    apply HasCompactSupport.finset_sum
    intro i _
    exact ((hc.fderiv_apply ℝ (b i)).fderiv_apply ℝ (b i)).sub
      ((hc.fderiv_apply ℝ (b i)).mul_left)
  have he : (∑ i, fun x =>
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i) x -
      bakryEmeryGibbsDirectional W (b i) x * bakryEmeryGibbsDirectional f (b i) x) =
      bakryEmeryGibbsGenerator W b f := by
    funext x
    simp only [Finset.sum_apply, bakryEmeryGibbsGenerator]
  rw [he] at hs
  exact hs

 theorem correspondenceBrascampLieb_generator_memLp
    (W f : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    MemLp (bakryEmeryGibbsGenerator W b f) 2 (correspondenceBrascampLiebMeasure W) := by
  have hL := correspondenceBrascampLieb_generator_continuous W f b hW hf
  have hLc := correspondenceBrascampLieb_generator_compact W f b hc
  apply (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mpr
  exact correspondenceBrascampLieb_integrable_compact W _ hW.continuous
    (hL.norm.pow 2) (by
      apply hLc.mono
      intro x hx hz
      apply hx
      simp [hz])

def correspondenceBrascampLiebCoreL2 (W : E → ℝ) (b : ι → E)
    (hW : ContDiff ℝ 2 W) (f : CorrespondenceBrascampLiebCompactTest E) :
    Lp ℝ 2 (correspondenceBrascampLiebMeasure W) :=
  (correspondenceBrascampLieb_generator_memLp W f.val b hW
    (f.smooth.of_le (by norm_num)) f.compact).toLp _

#print axioms correspondenceBrascampLieb_generator_memLp
end
end GinibrePoincare
