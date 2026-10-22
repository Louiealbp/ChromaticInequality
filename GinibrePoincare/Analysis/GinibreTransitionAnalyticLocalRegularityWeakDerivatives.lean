module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityBessel

@[expose] public section

/-! A genuine L² elliptic divergence equation produces actual ordinary L²
weak derivatives against every compact smooth test. -/
open TemperedDistribution FourierTransform MeasureTheory
open scoped SchwartzMap LineDeriv Laplacian ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ginibreLocalRegularity_elliptic_exists_weak_derivatives
    {ι : Type*} [Fintype ι] (u h : Lp ℂ 2 (volume : Measure E))
    (F : ι → Lp ℂ 2 (volume : Measure E)) (v : ι → E)
    (heq : Δ (u : 𝓢'(E, ℂ)) = (h : 𝓢'(E, ℂ))+∑ i, ∂_{v i} (F i : 𝓢'(E, ℂ))) :
    ∃ g : ι → Lp ℂ 2 (volume : Measure E), ∀ i (θ : E → ℂ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g i x) = -(∫ x, fderiv ℝ θ x (v i)*u x) := by
  have hu : MemSobolev 0 2 (u : 𝓢'(E, ℂ)) := memSobolev_zero_iff.mpr ⟨u, rfl⟩
  have hh : MemSobolev 0 2 (h : 𝓢'(E, ℂ)) := memSobolev_zero_iff.mpr ⟨h, rfl⟩
  have hF (i : ι) : MemSobolev 0 2 (F i : 𝓢'(E, ℂ)) := memSobolev_zero_iff.mpr ⟨F i, rfl⟩
  have hr := ginibreLocalRegularity_elliptic_divergence_memSobolev (u : 𝓢'(E, ℂ)) (h : 𝓢'(E, ℂ))
    (fun i => (F i : 𝓢'(E, ℂ))) v hu hh hF heq
  have hder (i : ι) : ∃ gi : Lp ℂ 2 (volume : Measure E),
      ∂_{v i} (u : 𝓢'(E, ℂ)) = (gi : 𝓢'(E, ℂ)) := by
    apply memSobolev_zero_iff.mp
    simpa using hr.lineDerivOp (m := v i)
  choose g hg using hder
  refine ⟨g,?_⟩
  intro i θ hθ hc
  have ht := congrArg (fun f : 𝓢'(E, ℂ) => f (hc.toSchwartzMap hθ)) (hg i)
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    smul_eq_mul, neg_mul, integral_neg] at ht
  exact ht.symm

#print axioms ginibreLocalRegularity_elliptic_exists_weak_derivatives
end
end GinibrePoincare
