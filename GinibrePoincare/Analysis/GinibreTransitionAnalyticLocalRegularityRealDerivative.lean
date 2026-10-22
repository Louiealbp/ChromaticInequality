module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityInterior
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]

theorem ginibreLocalRegularity_complex_weak_derivative_real
    (u : E → ℝ) (hu : MemLp u 2 (volume : Measure E))
    (g : Lp ℂ 2 (volume : Measure E)) (v : E)
    (hg : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x v*(u x : ℂ))) :
    ∃ gr : E → ℝ, MemLp gr 2 (volume : Measure E) ∧
      ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        (∫ x, θ x*gr x) = -(∫ x, fderiv ℝ θ x v*u x) := by
  refine ⟨fun x => (g x).re, Complex.reCLM.comp_memLp g, ?_⟩
  intro θ hθ hc
  let ψ := fun x => (θ x : ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hθ
  have hψc : HasCompactSupport ψ := hc.comp_left Complex.ofReal_zero
  have hd (x : E) : fderiv ℝ ψ x v = (fderiv ℝ θ x v : ℂ) := by
    have hh := Complex.ofRealCLM.hasFDerivAt.comp x ((hθ.differentiable (by simp)).differentiableAt.hasFDerivAt)
    exact congrArg (fun L => L v) hh.fderiv
  have he := congrArg Complex.re (hg ψ hψ hψc)
  have hi : Integrable (fun x => ψ x*g x) volume := by
    simpa only [smul_eq_mul, mul_comm] using
      ((MeasureTheory.Lp.memLp g).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport hψ.continuous hψc
  have hr : Integrable (fun x => fderiv ℝ ψ x v*(u x : ℂ)) volume := by
    have hq : ContDiff ℝ ∞ (fun x => fderiv ℝ ψ x v) :=
      (hψ.fderiv_right (by simp)).clm_apply contDiff_const
    have hqc := hψc.fderiv_apply ℝ v
    have hh := ((hu.ofReal (K := ℂ)).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport hq.continuous hqc
    apply hh.congr
    exact ae_of_all volume fun x => by dsimp only; simp only [smul_eq_mul]; exact mul_comm _ _
  have hil := Complex.reCLM.integral_comp_comm hi
  have hrl := Complex.reCLM.integral_comp_comm hr
  change (∫ x, (ψ x*g x).re) = (∫ x, ψ x*g x).re at hil
  change (∫ x, (fderiv ℝ ψ x v*(u x : ℂ)).re) = (∫ x, fderiv ℝ ψ x v*(u x : ℂ)).re at hrl
  rw [← hil, Complex.neg_re, ← hrl] at he
  simpa only [ψ, hd, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using he

#print axioms ginibreLocalRegularity_complex_weak_derivative_real
end
end GinibrePoincare
