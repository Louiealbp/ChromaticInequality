module
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticConvolution
public import GinibrePoincare.Analysis.WeakDerivativeMollification
public import GinibrePoincare.Analysis.LipschitzMollification
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
@[expose] public section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_pair_toLp (u : Lp ℝ 2 (volume : Measure E))
    (f : E→ℝ) (hf : MemLp f 2 volume) :
    inner ℝ u (hf.toLp f)=∫x, f x*u x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

/-- Actual L² weak derivatives can be tested against every compact C¹ test,
proved by simultaneous genuine value-and-derivative mollification. -/
theorem correspondenceWeightedElliptic_weak_test_C1
    (u g : Lp ℝ 2 (volume : Measure E)) (v : E)
    (hw : ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*u x))
    (θ : E→ℝ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*u x) := by
  let d : E→ℝ := fun x=>fderiv ℝ θ x v
  have hd : Continuous d := (hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdc : HasCompactSupport d := hc.fderiv_apply ℝ v
  have hθLp : MemLp θ 2 volume := hθ.continuous.memLp_of_hasCompactSupport hc
  have hdLp : MemLp d 2 volume := hd.memLp_of_hasCompactSupport hdc
  have hweak : ∀ψ : E→ℝ, ContDiff ℝ ∞ ψ→HasCompactSupport ψ→
      (∫x, d x*ψ x)= -(∫x, θ x*fderiv ℝ ψ x v) := by
    intro ψ hψ hψc
    have hDψ : Continuous (fun x=>fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=(volume : Measure E))
      ((hd.mul hψ.continuous).integrable_of_hasCompactSupport (hdc.mul_right))
      ((hθ.continuous.mul hDψ).integrable_of_hasCompactSupport (hc.mul_right))
      ((hθ.continuous.mul hψ.continuous).integrable_of_hasCompactSupport (hc.mul_right))
      (fun _ _=>hθ.differentiable (by norm_num) _)
      (fun _ _=>hψ.differentiable (by simp) _)
    change (∫x, θ x*fderiv ℝ ψ x v)= -(∫x, d x*ψ x) at hi
    linarith
  let φ := lsiMollifier E
  let A := fun m=>correspondenceWeighted_lebesgueSmoothCompactMollification (φ m) θ hθLp hc
  let B := fun m=>correspondenceWeighted_lebesgueSmoothCompactMollification (φ m) d hdLp hdc
  have hA := correspondenceWeighted_lebesgueSmoothCompactMollification_tendsto φ
    (lsiMollifier_radius_tendsto E) θ hθLp hc
  have hB := correspondenceWeighted_lebesgueSmoothCompactMollification_tendsto φ
    (lsiMollifier_radius_tendsto E) d hdLp hdc
  have hm (m : ℕ) : inner ℝ g (A m)+inner ℝ u (B m)=0 := by
    let θm := (φ m).normed volume ⋆[lsmul ℝ ℝ, volume] θ
    have hsm : ContDiff ℝ ∞ θm := (φ m).hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) ((φ m).contDiff_normed (n:=⊤)) (hθLp.locallyIntegrable (by norm_num))
    have hcm : HasCompactSupport θm := (φ m).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hc
    have he := hw θm hsm hcm
    have hder := weakDirectionalDerivative_convolution volume θ d ((φ m).normed volume) v
      (hθLp.locallyIntegrable (by norm_num)) ((φ m).contDiff_normed (n:=⊤))
      (φ m).hasCompactSupport_normed hweak
    dsimp only [θm] at he
    simp_rw [hder] at he
    dsimp only [A, B, correspondenceWeighted_lebesgueSmoothCompactMollification]
    rw [correspondenceWeightedElliptic_pair_toLp, correspondenceWeightedElliptic_pair_toLp]
    linarith
  have hl : Tendsto (fun m=>inner ℝ g (A m)+inner ℝ u (B m)) atTop
      (𝓝 (inner ℝ g (hθLp.toLp θ)+inner ℝ u (hdLp.toLp d))) :=
    (tendsto_const_nhds.inner hA).add (tendsto_const_nhds.inner hB)
  have he : inner ℝ g (hθLp.toLp θ)+inner ℝ u (hdLp.toLp d)=0 :=
    tendsto_nhds_unique hl (by simpa only [hm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0 : ℝ)) atTop (𝓝 0)))
  rw [correspondenceWeightedElliptic_pair_toLp, correspondenceWeightedElliptic_pair_toLp] at he
  linarith
#print axioms correspondenceWeightedElliptic_pair_toLp
#print axioms correspondenceWeightedElliptic_weak_test_C1
end
end GinibrePoincare
