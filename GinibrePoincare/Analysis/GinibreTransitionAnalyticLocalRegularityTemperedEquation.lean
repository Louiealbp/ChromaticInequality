module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCompactTests

@[expose] public section

/-! The actual compact-test elliptic equation for compact L² data is an actual
tempered-distribution equation, without an extra distributional certificate. -/
open MeasureTheory Filter TemperedDistribution
open scoped Topology ContDiff SchwartzMap LineDeriv Laplacian
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ginibreLocalRegularity_toLp_tempered_apply
    (f : E → ℂ) (hf : MemLp f 2 (volume : Measure E)) (θ : 𝓢(E, ℂ)) :
    (hf.toLp f : 𝓢'(E, ℂ)) θ = ∫ x, θ x*f x := by
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [smul_eq_mul, hx]

theorem ginibreLocalRegularity_compact_tests_tempered_equation
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (u h : E → ℂ) (F : ι → E → ℂ)
    (hu : HasCompactSupport u) (hh : HasCompactSupport h) (hF : ∀ i, HasCompactSupport (F i))
    (hui : MemLp u 2 (volume : Measure E)) (hhi : MemLp h 2 (volume : Measure E))
    (hFi : ∀ i, MemLp (F i) 2 (volume : Measure E))
    (heq : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (b i)) x (b i))) =
        (∫ x, h x*θ x)-∑ i, ∫ x, F i x*fderiv ℝ θ x (b i)) :
    Δ (hui.toLp u : 𝓢'(E, ℂ)) = (hhi.toLp h : 𝓢'(E, ℂ))+
      ∑ i, ∂_{b i} ((hFi i).toLp (F i) : 𝓢'(E, ℂ)) := by
  classical
  ext θ
  have he := ginibreLocalRegularity_compact_equation_all_smooth_tests u h F (fun i => b i)
    hu hh hF heq θ (θ.smooth ⊤)
  rw [TemperedDistribution.laplacian_apply_apply, ginibreLocalRegularity_toLp_tempered_apply]
  have hleft : (∫ x, (Δ θ) x*u x) =
      ∫ x, u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ (θ : E → ℂ) y (b i)) x (b i)) := by
    apply integral_congr_ae
    apply ae_of_all
    intro x
    rw [SchwartzMap.laplacian_eq_sum b]
    simp only [sum_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [mul_comm]
    congr 1
  rw [hleft, he]
  simp only [add_apply, sum_apply, TemperedDistribution.lineDerivOp_apply_apply,
    ginibreLocalRegularity_toLp_tempered_apply, SchwartzMap.neg_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, neg_mul, integral_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 1
  · apply integral_congr_ae
    exact ae_of_all volume (fun x => mul_comm _ _)
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    exact ae_of_all volume (fun x => mul_comm _ _)

#print axioms ginibreLocalRegularity_compact_tests_tempered_equation
end
end GinibrePoincare
