module
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticLocalSobolev
@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_cutoff_gradient
    {ι : Type*} [Fintype ι] (v : ι→E) (f χ η : E→ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hχ : ∀x∈tsupport η, χ x=1)
    (u : Lp ℝ 2 (volume : Measure E)) (hu : (u : E→ℝ)=ᵐ[volume](fun x=>χ x*f x))
    (J : ι→Lp ℝ 2 (volume : Measure E))
    (hJ : ∀i (θ : E→ℝ), ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*J i x)= -(∫x, fderiv ℝ θ x (v i)*u x)) :
    ∀i, MemLp (fun x=>η x*J i x+fderiv ℝ η x (v i)*f x) 2 volume ∧
      HasCompactSupport (fun x=>η x*J i x+fderiv ℝ η x (v i)*f x) ∧
      ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*(η x*J i x+fderiv ℝ η x (v i)*f x))=
          -(∫x, fderiv ℝ θ x (v i)*(η x*f x)) := by
  intro i
  obtain ⟨U, G, hU, hG, hw⟩ := correspondenceWeightedElliptic_compact_C1_product u (J i) (v i) (hJ i)
    η (hη.of_le (by norm_num)) hc
  have hV : (U : E→ℝ)=ᵐ[volume](fun x=>η x*f x) := by
    filter_upwards [hU, hu] with x hUx hux
    rw [hUx, hux]
    by_cases hx : x∈tsupport η
    · rw [hχ x hx]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hR : (G : E→ℝ)=ᵐ[volume](fun x=>η x*J i x+fderiv ℝ η x (v i)*f x) := by
    filter_upwards [hG, hu] with x hGx hux
    rw [hGx, hux]
    by_cases hx : x∈tsupport η
    · rw [hχ x hx]
      ring
    · have hd : fderiv ℝ η x (v i)=0 := by
        rw [fderiv_of_notMem_tsupport (𝕜:=ℝ) hx]
        rfl
      simp [hd]
  refine ⟨(Lp.memLp G).ae_eq hR,?_,?_⟩
  · exact (hc.mul_right).add ((hc.fderiv_apply ℝ (v i)).mul_right)
  · intro θ hθ hθc
    have he := hw θ hθ hθc
    have hl : (∫x, θ x*G x)=∫x, θ x*(η x*J i x+fderiv ℝ η x (v i)*f x) := by
      apply integral_congr_ae
      filter_upwards [hR] with x hx
      rw [hx]
    have hr : (∫x, fderiv ℝ θ x (v i)*U x)=∫x, fderiv ℝ θ x (v i)*(η x*f x) := by
      apply integral_congr_ae
      filter_upwards [hV] with x hx
      rw [hx]
    rwa [hl, hr] at he
#print axioms correspondenceWeightedElliptic_cutoff_gradient
end
end GinibrePoincare
