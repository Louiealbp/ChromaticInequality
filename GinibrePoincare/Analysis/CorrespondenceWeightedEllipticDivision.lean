module
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticProduct
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticDensity
@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual localized density H¹ regularity gives actual localized ordinary
H¹ regularity, even when the positive density is only C¹. -/
theorem correspondenceWeightedElliptic_divide_density
    {ι : Type*} [Fintype ι] (v : ι→E) (ρ : E→ℝ) (hρ : ContDiff ℝ 1 ρ)
    (hp : ∀x, 0<ρ x) (f η : E→ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (u : Lp ℝ 2 (volume : Measure E))
    (hu : (u : E→ℝ)=ᵐ[volume](fun x=>η x*(ρ x*f x)))
    (g : ι→Lp ℝ 2 (volume : Measure E))
    (hg : ∀i (θ : E→ℝ), ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g i x)= -(∫x, fderiv ℝ θ x (v i)*u x)) :
    ∃G : ι→Lp ℝ 2 (volume : Measure E),
      ∀i (θ : E→ℝ), ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*G i x)= -(∫x, fderiv ℝ θ x (v i)*(η x*f x)) := by
  obtain ⟨χ, hχ, hχc, hχone⟩ := ginibreLocalRegularity_exists_compact_cutoff (tsupport η) hc
  let q : E→ℝ := fun x=>χ x/(ρ x)
  have hq : ContDiff ℝ 1 q := (hχ.of_le (by norm_num)).div hρ (fun x=>(hp x).ne')
  have hqc : HasCompactSupport q := by
    change HasCompactSupport (χ*(fun x=>(ρ x)⁻¹))
    exact hχc.mul_right
  have hrep (U : Lp ℝ 2 (volume : Measure E))
      (hU : (U : E→ℝ)=ᵐ[volume](fun x=>q x*u x)) :
      (U : E→ℝ)=ᵐ[volume](fun x=>η x*f x) := by
    filter_upwards [hU, hu] with x hUx hux
    rw [hUx, hux]
    dsimp [q]
    by_cases hx : x∈tsupport η
    · rw [(hχone x hx).eq_of_nhds]
      field_simp [(hp x).ne']
      simp
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hex (i) : ∃G : Lp ℝ 2 (volume : Measure E),
      ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*G x)= -(∫x, fderiv ℝ θ x (v i)*(η x*f x)) := by
    obtain ⟨U, G, hU, hG, hweak⟩ := correspondenceWeightedElliptic_compact_C1_product u (g i) (v i)
      (hg i) q hq hqc
    refine ⟨G,?_⟩
    intro θ hθ hθc
    rw [hweak θ hθ hθc]
    congr 1
    apply integral_congr_ae
    filter_upwards [hrep U hU] with x hx
    rw [hx]
  choose G hG using hex
  exact ⟨G, hG⟩
#print axioms correspondenceWeightedElliptic_divide_density
end
end GinibrePoincare
