module
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticGreen
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticFormTesting
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticCutoffGradient
@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_cutoff_form_identity
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ρ : E→ℝ) (hρ : ContDiff ℝ 1 ρ) (hp : ∀x, 0<ρ x)
    [IsFiniteMeasure (correspondenceWeightedEllipticMeasure ρ)]
    (f : E→ℝ) (hf : MemLp f 2 (correspondenceWeightedEllipticMeasure ρ))
    (hAnn : ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, f x*correspondenceWeightedEllipticGenerator b ρ θ x∂correspondenceWeightedEllipticMeasure ρ)=0)
    (χ η : E→ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hχ : ∀x∈tsupport η, χ x=1)
    (u : Lp ℝ 2 (volume : Measure E)) (hu : (u : E→ℝ)=ᵐ[volume](fun x=>χ x*f x))
    (J : ι→Lp ℝ 2 (volume : Measure E))
    (hJ : ∀i (θ : E→ℝ), ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*J i x)= -(∫x, fderiv ℝ θ x (b i)*u x)) :
    (∑i,∫x, ρ x*((η x*J i x+fderiv ℝ η x (b i)*f x)^2-
      f x^2*(fderiv ℝ η x (b i))^2))=0 ∧
    ∀i, Integrable (fun x=>ρ x*((η x*J i x+fderiv ℝ η x (b i)*f x)^2-
      f x^2*(fderiv ℝ η x (b i))^2)) volume := by
  classical
  let d := fun i x=>fderiv ℝ η x (b i)
  let g := fun i x=>η x*J i x+d i x*f x
  have hd (i) : Continuous (d i) := (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc (i) : HasCompactSupport (d i) := hc.fderiv_apply ℝ (b i)
  have hGrad := correspondenceWeightedElliptic_cutoff_gradient (fun i=>b i) f χ η hη hc hχ u hu J hJ
  have hF : MemLp (fun x=>η x*f x) 2 (volume : Measure E) :=
    correspondenceWeightedElliptic_compact_value_memLp ρ hρ.continuous hp f η hf hη.continuous hc
  have hAt (i : ι) : MemLp (fun x=>ρ x*η x) ⊤ (volume : Measure E) :=
    (hρ.continuous.mul hη.continuous).memLp_top_of_hasCompactSupport (hc.mul_left) volume
  have hBt (i) : MemLp (fun x=>ρ x*d i x) ⊤ (volume : Measure E) :=
    (hρ.continuous.mul (hd i)).memLp_top_of_hasCompactSupport ((hdc i).mul_left) volume
  have hALp (i) : MemLp (fun x=>(ρ x*η x)*J i x) 2 volume := (hAt i).fun_mul (r:=2) (Lp.memLp (J i))
  have hBLp (i) : MemLp (fun x=>(ρ x*d i x)*J i x) 2 volume := (hBt i).fun_mul (r:=2) (Lp.memLp (J i))
  let A := fun i=>(hALp i).toLp (fun x=>(ρ x*η x)*J i x)
  let B := fun i=>(hBLp i).toLp (fun x=>(ρ x*d i x)*J i x)
  have hA : ∀ψ : E→ℝ, ContDiff ℝ ∞ ψ→HasCompactSupport ψ→
      (∑i, ((∫x, fderiv ℝ ψ x (b i)*A i x)+(∫x, ψ x*B i x)))=0 := by
    intro ψ hψ hψc
    have he := correspondenceWeightedElliptic_annihilator_local_green b ρ hρ hp f hf hAnn χ u hu J hJ
      (η*ψ) (hη.mul hψ) (hc.mul_right) (fun x hx=>hχ x (tsupport_mul_subset_left hx))
    convert he using 1
    apply Finset.sum_congr rfl
    intro i hi
    have hDP : MemLp (fun x=>fderiv ℝ ψ x (b i)) 2 volume :=
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hψc.fderiv_apply ℝ (b i))
    have hP : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
    have hIA : Integrable (fun x=>fderiv ℝ ψ x (b i)*A i x) volume := hDP.integrable_mul (Lp.memLp (A i))
    have hIB : Integrable (fun x=>ψ x*B i x) volume := hP.integrable_mul (Lp.memLp (B i))
    rw [← integral_add hIA hIB]
    apply integral_congr_ae
    filter_upwards [(hALp i).coeFn_toLp, (hBLp i).coeFn_toLp] with x hAx hBx
    rw [hAx, hBx, fderiv_mul (hη.differentiable (by simp) x) (hψ.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    dsimp [d]
    ring
  have he := correspondenceWeightedElliptic_form_test_H1 (fun i=>b i) (fun x=>η x*f x) hF
    (hc.mul_right) g (fun i=>(hGrad i).1) (fun i=>(hGrad i).2.1)
    (fun i=>(hGrad i).2.2) A B hA
  have hI1 (i) : Integrable (fun x=>g i x*A i x) volume := (hGrad i).1.integrable_mul (Lp.memLp (A i))
  have hI2 (i) : Integrable (fun x=>(η x*f x)*B i x) volume := hF.integrable_mul (Lp.memLp (B i))
  have hrep (i) : (fun x=>g i x*A i x+(η x*f x)*B i x)=ᵐ[volume]
      (fun x=>ρ x*((g i x)^2-f x^2*(d i x)^2)) := by
    filter_upwards [(hALp i).coeFn_toLp, (hBLp i).coeFn_toLp] with x hAx hBx
    rw [hAx, hBx]
    dsimp [g]
    ring
  have hInt (i) : Integrable (fun x=>ρ x*((g i x)^2-f x^2*(d i x)^2)) volume :=
    ((hI1 i).add (hI2 i)).congr (hrep i)
  refine ⟨?_, hInt⟩
  convert he using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← integral_add (hI1 i) (hI2 i), integral_congr_ae (hrep i)]
#print axioms correspondenceWeightedElliptic_cutoff_form_identity
end
end GinibrePoincare
