module
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticC1Tests
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.MeanValue
@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A locally integrable function with every genuine ordinary directional
weak derivative zero is a.e. constant on the full real Euclidean space. -/
theorem correspondenceWeightedElliptic_zero_gradient_constant
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (u : E→ℝ)
    (hu : LocallyIntegrable u (volume : Measure E))
    (hw : ∀i (θ : E→ℝ), ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, u x*fderiv ℝ θ x (b i))=0) :
    ∃c : ℝ, u=ᵐ[volume](fun _=>c) := by
  let φ := lsiMollifier E
  let U := fun m=>(φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u
  have hUs (m) : ContDiff ℝ ∞ (U m) := (φ m).hasCompactSupport_normed.contDiff_convolution_left
    _ ((φ m).contDiff_normed (n:=⊤)) hu
  have hUd (m) (x : E) : fderiv ℝ (U m) x=0 := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    have hh := weakDirectionalDerivative_convolution volume u (fun _=>(0 : ℝ))
      ((φ m).normed volume) (b i) hu ((φ m).contDiff_normed (n:=⊤))
      (φ m).hasCompactSupport_normed
      (by intro θ hθ hc; rw [hw i θ hθ hc]; simp) x
    have hh0 : (fun _ : E=>(0 : ℝ))=(0 : E→ℝ) := rfl
    rw [hh0, convolution_zero] at hh
    simpa [U] using hh
  have hconst (m) (x y : E) : U m x=U m y :=
    is_const_of_fderiv_eq_zero ((hUs m).differentiable (by simp)) (hUd m) x y
  have hlim := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ:=(volume : Measure E)) (lsiMollifier_radius_tendsto E)
    (K:=2) (Filter.Eventually.of_forall (fun m=>by dsimp [lsiMollifier]; linarith)) hu
  obtain ⟨x, hx⟩ := Filter.Eventually.exists hlim
  refine ⟨u x,?_⟩
  filter_upwards [hlim] with y hy
  have he : Tendsto (fun m=>U m y) atTop (𝓝 (u x)) := hx.congr (fun m=>hconst m x y)
  exact tendsto_nhds_unique hy he
#print axioms correspondenceWeightedElliptic_zero_gradient_constant
end
end GinibrePoincare
