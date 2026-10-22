module
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticSobolevApproximation
@[expose] public section
open MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_form_test_H1
    {ι : Type*} [Fintype ι] (v : ι→E)
    (f : E→ℝ) (hf : MemLp f 2 (volume : Measure E)) (hfc : HasCompactSupport f)
    (g : ι→E→ℝ) (hg : ∀i, MemLp (g i) 2 (volume : Measure E)) (hgc : ∀i, HasCompactSupport (g i))
    (hw : ∀i (θ : E→ℝ), ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g i x)= -(∫x, fderiv ℝ θ x (v i)*f x))
    (A B : ι→Lp ℝ 2 (volume : Measure E))
    (hA : ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∑i, ((∫x, fderiv ℝ θ x (v i)*A i x)+(∫x, θ x*B i x)))=0) :
    (∑i, ((∫x, g i x*A i x)+(∫x, f x*B i x)))=0 := by
  classical
  let φ := lsiMollifier E
  let V := fun m=>correspondenceWeighted_lebesgueSmoothCompactMollification (φ m) f hf hfc
  let H := fun m i=>(correspondenceWeightedElliptic_mollified_derivative_memLp f (g i) hf (hg i) (hgc i) (v i) (hw i) (φ m)).toLp
    (fun x=>fderiv ℝ ((φ m).normed volume ⋆[lsmul ℝ ℝ, volume] f) x (v i))
  have hV := correspondenceWeighted_lebesgueSmoothCompactMollification_tendsto φ (lsiMollifier_radius_tendsto E) f hf hfc
  have hH (i) := correspondenceWeightedElliptic_mollified_derivative_tendsto f (g i) hf (hg i) (hgc i) (v i) (hw i)
  have he (m) : (∑i, (inner ℝ (A i) (H m i)+inner ℝ (B i) (V m)))=0 := by
    let θ := (φ m).normed volume ⋆[lsmul ℝ ℝ, volume] f
    have hθ : ContDiff ℝ ∞ θ := (φ m).hasCompactSupport_normed.contDiff_convolution_left
      _ ((φ m).contDiff_normed (n:=⊤)) (hf.locallyIntegrable (by norm_num))
    have hcθ : HasCompactSupport θ := (φ m).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hfc
    have hh := hA θ hθ hcθ
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [H, V, correspondenceWeighted_lebesgueSmoothCompactMollification]
    rw [correspondenceWeightedElliptic_pair_toLp, correspondenceWeightedElliptic_pair_toLp]
  have hl : Tendsto (fun m=>∑i, (inner ℝ (A i) (H m i)+inner ℝ (B i) (V m))) atTop
      (𝓝 (∑i, (inner ℝ (A i) ((hg i).toLp (g i))+inner ℝ (B i) (hf.toLp f)))) := by
    apply tendsto_finsetSum
    intro i hi
    exact (tendsto_const_nhds.inner (hH i)).add (tendsto_const_nhds.inner hV)
  have hz : (∑i, (inner ℝ (A i) ((hg i).toLp (g i))+inner ℝ (B i) (hf.toLp f)))=0 :=
    tendsto_nhds_unique hl (by simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0 : ℝ)) atTop (𝓝 0)))
  simpa only [correspondenceWeightedElliptic_pair_toLp] using hz
#print axioms correspondenceWeightedElliptic_form_test_H1
end
end GinibrePoincare
