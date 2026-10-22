module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebLinear
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
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

 theorem correspondenceBrascampLieb_core_ae
    (W : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (f : CorrespondenceBrascampLiebCompactTest E) :
    correspondenceBrascampLiebCoreL2 W b hW f =ᵐ[correspondenceBrascampLiebMeasure W]
      bakryEmeryGibbsGenerator W b f.val := by
  exact (correspondenceBrascampLieb_generator_memLp W f.val b hW
    (f.smooth.of_le (by norm_num)) f.compact).coeFn_toLp

/-- The genuine linear range of the compact smooth Gibbs generator. -/
def correspondenceBrascampLiebCoreRange
    (W : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W) :
    Submodule ℝ (Lp ℝ 2 (correspondenceBrascampLiebMeasure W)) where
  carrier := Set.range (correspondenceBrascampLiebCoreL2 W b hW)
  zero_mem' := by
    refine ⟨⟨fun _ => 0, contDiff_const, HasCompactSupport.zero⟩, ?_⟩
    apply Lp.ext
    filter_upwards [correspondenceBrascampLieb_core_ae W b hW
      ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero⟩, Lp.coeFn_zero ℝ 2 (correspondenceBrascampLiebMeasure W)] with x hx hz
    rw [hz, hx]
    have hd (v : E) : bakryEmeryGibbsDirectional (fun _ : E => (0 : ℝ)) v =
        (fun _ => 0) := by
      funext y
      simp [bakryEmeryGibbsDirectional]
    simp only [bakryEmeryGibbsGenerator, hd]
    simp
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    let fg : CorrespondenceBrascampLiebCompactTest E :=
      ⟨f.val+g.val, f.smooth.add g.smooth, f.compact.add g.compact⟩
    refine ⟨fg, ?_⟩
    apply Lp.ext
    filter_upwards [correspondenceBrascampLieb_core_ae W b hW fg,
      correspondenceBrascampLieb_core_ae W b hW f,
      correspondenceBrascampLieb_core_ae W b hW g,
      Lp.coeFn_add (correspondenceBrascampLiebCoreL2 W b hW f)
        (correspondenceBrascampLiebCoreL2 W b hW g)] with x hfg hfx hgx ha
    rw [hfg, ha]
    simp only [Pi.add_apply, hfx, hgx]
    exact congrFun (correspondenceBrascampLieb_generator_add W f.val g.val b
      (f.smooth.of_le (by norm_num)) (g.smooth.of_le (by norm_num))) x
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    let cf : CorrespondenceBrascampLiebCompactTest E :=
      ⟨c • f.val, f.smooth.const_smul c, f.compact.smul_left⟩
    refine ⟨cf, ?_⟩
    apply Lp.ext
    filter_upwards [correspondenceBrascampLieb_core_ae W b hW cf,
      correspondenceBrascampLieb_core_ae W b hW f,
      Lp.coeFn_smul c (correspondenceBrascampLiebCoreL2 W b hW f)] with x hcf hfx hs
    rw [hcf, hs]
    simp only [Pi.smul_apply, hfx, smul_eq_mul]
    exact congrFun (correspondenceBrascampLieb_generator_smul W f.val b
      (f.smooth.of_le (by norm_num)) c) x

#print axioms correspondenceBrascampLiebCoreRange
end
end GinibrePoincare
