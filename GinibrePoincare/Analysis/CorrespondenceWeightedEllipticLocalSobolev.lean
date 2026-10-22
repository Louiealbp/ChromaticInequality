module
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticEquation
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticDivision
@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every literal weighted-generator L² annihilator has actual ordinary local
H¹ regularity, proved internally from its elliptic equation. -/
theorem correspondenceWeightedElliptic_annihilator_local_H1
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ρ : E→ℝ) (hρ : ContDiff ℝ 1 ρ) (hp : ∀x, 0<ρ x)
    [IsFiniteMeasure (correspondenceWeightedEllipticMeasure ρ)]
    (f : E→ℝ) (hf : MemLp f 2 (correspondenceWeightedEllipticMeasure ρ))
    (hA : ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, f x*correspondenceWeightedEllipticGenerator b ρ θ x∂correspondenceWeightedEllipticMeasure ρ)=0)
    (η : E→ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ∃G : ι→Lp ℝ 2 (volume : Measure E),
      ∀i (θ : E→ℝ), ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*G i x)= -(∫x, fderiv ℝ θ x (b i)*(η x*f x)) := by
  let K := tsupport η
  have hρf := correspondenceWeightedElliptic_compact_multiplier_memLp ρ hρ.continuous hp f ρ hf hρ.continuous K hc
  have hF (i) : MemLp (fun x=>f x*fderiv ℝ ρ x (b i)) 2 (volume.restrict K) := by
    have hd : Continuous (fun x=>fderiv ℝ ρ x (b i)) :=
      (hρ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    simpa only [mul_comm] using correspondenceWeightedElliptic_compact_multiplier_memLp ρ hρ.continuous hp
      f _ hf hd K hc
  obtain ⟨g, hgm, hge⟩ := correspondenceWeightedElliptic_local_real_derivatives b K hc.measurableSet
    (fun x=>ρ x*f x) (fun _=>0) (fun i x=>f x*fderiv ℝ ρ x (b i)) hρf (by simp) hF
    η hη hc (Subset.refl _)
    (by intro θ hθ hθc hs; simpa using correspondenceWeightedElliptic_annihilator_equation b ρ hρ hp f hf hA θ hθ hθc)
  have hmK := correspondenceWeightedElliptic_compact_multiplier_memLp ρ hρ.continuous hp f (η*ρ) hf
    (hη.continuous.mul hρ.continuous) K hc
  have hmI := (memLp_indicator_iff_restrict hc.measurableSet).mpr hmK
  have hw : MemLp (fun x=>η x*(ρ x*f x)) 2 (volume : Measure E) := by
    apply hmI.ae_eq
    exact ae_of_all volume fun x=>by
      by_cases hx : x∈tsupport η
      · simp [Set.indicator_of_mem hx, Pi.mul_apply, mul_assoc]
      · have hz : η x=0 := image_eq_zero_of_notMem_tsupport hx
        simp [Set.indicator_of_notMem hx, hz, Pi.mul_apply]
  let w := hw.toLp (fun x=>η x*(ρ x*f x))
  let G := fun i=>(hgm i).toLp (g i)
  have hweak (i) (θ : E→ℝ) (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) :
      (∫x, θ x*G i x)= -(∫x, fderiv ℝ θ x (b i)*w x) := by
    have hl : (∫x, θ x*G i x)=∫x, θ x*g i x := by
      apply integral_congr_ae
      filter_upwards [(hgm i).coeFn_toLp] with x hx
      rw [hx]
    have hr : (∫x, fderiv ℝ θ x (b i)*w x)=∫x, fderiv ℝ θ x (b i)*(η x*(ρ x*f x)) := by
      apply integral_congr_ae
      filter_upwards [hw.coeFn_toLp] with x hx
      rw [hx]
    rw [hl, hr]
    exact hge i θ hθ hθc
  exact correspondenceWeightedElliptic_divide_density (fun i=>b i) ρ hρ hp f η hη hc w hw.coeFn_toLp G hweak
#print axioms correspondenceWeightedElliptic_annihilator_local_H1
end
end GinibrePoincare
