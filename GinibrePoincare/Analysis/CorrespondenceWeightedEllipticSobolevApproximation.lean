module
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticC1Tests
@[expose] public section
open MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_mollified_derivative
    (f g : E→ℝ) (hf : MemLp f 2 (volume : Measure E)) (v : E)
    (hw : ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*f x))
    (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x v=
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) x := by
  apply weakDirectionalDerivative_convolution volume f g _ v (hf.locallyIntegrable (by norm_num))
    (φ.contDiff_normed (n:=⊤)) φ.hasCompactSupport_normed
  intro θ hθ hc
  have he := hw θ hθ hc
  simpa only [mul_comm] using he

theorem correspondenceWeightedElliptic_mollified_derivative_memLp
    (f g : E→ℝ) (hf : MemLp f 2 (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E)) (hc : HasCompactSupport g) (v : E)
    (hw : ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*f x)) (φ : ContDiffBump (0 : E)) :
    MemLp (fun x=>fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x v) 2 volume := by
  have he : (fun x=>fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x v)=
      φ.normed volume ⋆[lsmul ℝ ℝ, volume] g := by
    funext x
    exact correspondenceWeightedElliptic_mollified_derivative f g hf v hw φ x
  rw [he]
  exact correspondenceWeighted_memLp_bump_convolution_compact φ g hg hc

theorem correspondenceWeightedElliptic_mollified_derivative_toLp
    (f g : E→ℝ) (hf : MemLp f 2 (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E)) (hc : HasCompactSupport g) (v : E)
    (hw : ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*f x)) (φ : ContDiffBump (0 : E)) :
    (correspondenceWeightedElliptic_mollified_derivative_memLp f g hf hg hc v hw φ).toLp
      (fun x=>fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x v)=
      correspondenceWeighted_lebesgueSmoothCompactMollification φ g hg hc := by
  unfold correspondenceWeighted_lebesgueSmoothCompactMollification
  apply Lp.ext
  filter_upwards [(correspondenceWeightedElliptic_mollified_derivative_memLp f g hf hg hc v hw φ).coeFn_toLp,
    (correspondenceWeighted_memLp_bump_convolution_compact φ g hg hc).coeFn_toLp] with x hx hy
  rw [hx, hy]
  exact correspondenceWeightedElliptic_mollified_derivative f g hf v hw φ x

theorem correspondenceWeightedElliptic_mollified_derivative_tendsto
    (f g : E→ℝ) (hf : MemLp f 2 (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E)) (hc : HasCompactSupport g) (v : E)
    (hw : ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*f x)) :
    Tendsto (fun m=>(correspondenceWeightedElliptic_mollified_derivative_memLp f g hf hg hc v hw (lsiMollifier E m)).toLp
      (fun x=>fderiv ℝ ((lsiMollifier E m).normed volume ⋆[lsmul ℝ ℝ, volume] f) x v)) atTop (𝓝 (hg.toLp g)) := by
  have hh := correspondenceWeighted_lebesgueSmoothCompactMollification_tendsto _ (lsiMollifier_radius_tendsto E) g hg hc
  apply hh.congr
  intro m
  exact (correspondenceWeightedElliptic_mollified_derivative_toLp f g hf hg hc v hw (lsiMollifier E m)).symm
#print axioms correspondenceWeightedElliptic_mollified_derivative
#print axioms correspondenceWeightedElliptic_mollified_derivative_tendsto
end
end GinibrePoincare
