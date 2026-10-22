import TheoremA2.GaussianDomination
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Cramér–Rao from actual integration by parts

All integrations by parts below are theorems about the actual derivatives
of the specified potential. Gaussian domination proves every integrability
condition in mathlib's global integration-by-parts theorem. No boundary,
score-identity or covariance certificate is taken as a hypothesis.
-/

namespace TheoremA2.CramerRao

open MeasureTheory Measure Filter
open TheoremA2.BrascampLieb
open scoped Topology RealInnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

def weight (V : E → ℝ) (x : E) : ℝ := Real.exp (-V x)

def score (V : E → ℝ) (v x : E) : ℝ := fderiv ℝ V x v

theorem continuous_weight {V : E → ℝ} (hV : Continuous V) : Continuous (weight V) :=
  Real.continuous_exp.comp hV.neg

theorem score_contDiff {V : E → ℝ} (hV : ContDiff ℝ 2 V) (v : E) :
    ContDiff ℝ 1 (score V v) :=
  (hV.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem fderiv_weight {V : E → ℝ} (hV : Differentiable ℝ V) (v x : E) :
    fderiv ℝ (weight V) x v = -score V v x * weight V x := by
  have hd := (Real.hasDerivAt_exp (-V x)).comp_hasFDerivAt x (hV x).hasFDerivAt.neg
  rw [show fderiv ℝ (weight V) x = _ from hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
  simp only [score, weight]
  ring

theorem integrable_weighted_growth {V f : E → ℝ} {a C : ℝ}
    (hV : Continuous V) (ha : 0 < a) (hC : 0 ≤ C)
    (hlower : ∀ x, a * ‖x‖ ^ 2 ≤ V x) (hf : Continuous f)
    (hbound : ∀ x, |f x| ≤ C * (1 + ‖x‖ ^ 2)) :
    Integrable (fun x => f x * weight V x) := by
  apply integrable_of_quadratic_gaussian_bound ha (0 : E)
    (hf.mul (continuous_weight hV)).aestronglyMeasurable (C := C)
  intro x
  change |f x * weight V x| ≤ _
  rw [abs_mul, abs_of_pos (show 0 < weight V x from Real.exp_pos _)]
  simp only [inner_zero_left, add_zero]
  have hw : weight V x ≤ Real.exp (-a * ‖x‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    linarith [hlower x]
  exact mul_le_mul (hbound x) hw (Real.exp_pos _).le
    (mul_nonneg hC (by positivity))

theorem integrable_weight {V : E → ℝ} {a : ℝ}
    (hV : Continuous V) (ha : 0 < a) (hlower : ∀ x, a * ‖x‖ ^ 2 ≤ V x) :
    Integrable (weight V) := by
  have h := integrable_weighted_growth hV ha (by norm_num : (0 : ℝ) ≤ 1)
    hlower (continuous_const : Continuous (fun _ : E => (1 : ℝ)))
    (fun x => by
      simpa only [abs_one, one_mul] using le_add_of_nonneg_right (sq_nonneg ‖x‖))
  simpa only [one_mul] using h

theorem integrable_weighted_linear_growth {V f : E → ℝ} {a C : ℝ}
    (hV : Continuous V) (ha : 0 < a) (hC : 0 ≤ C)
    (hlower : ∀ x, a * ‖x‖ ^ 2 ≤ V x) (hf : Continuous f)
    (hbound : ∀ x, |f x| ≤ C * ‖x‖) :
    Integrable (fun x => f x * weight V x) := by
  apply integrable_weighted_growth hV ha hC hlower hf
  intro x
  apply (hbound x).trans
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith [sq_nonneg (‖x‖ - 1)]

theorem integrable_weighted_product_growth {V f g : E → ℝ} {a C D : ℝ}
    (hV : Continuous V) (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hlower : ∀ x, a * ‖x‖ ^ 2 ≤ V x) (hf : Continuous f) (hg : Continuous g)
    (hfbound : ∀ x, |f x| ≤ C * ‖x‖) (hgbound : ∀ x, |g x| ≤ D * ‖x‖) :
    Integrable (fun x => (f x * g x) * weight V x) := by
  apply integrable_weighted_growth hV ha (mul_nonneg hC hD) hlower (hf.mul hg)
  intro x
  simp only [Pi.mul_apply]
  rw [abs_mul]
  calc
    _ ≤ (C * ‖x‖) * (D * ‖x‖) :=
      mul_le_mul (hfbound x) (hgbound x) (abs_nonneg _) (mul_nonneg hC (norm_nonneg _))
    _ ≤ (C * D) * (1 + ‖x‖ ^ 2) := by nlinarith [mul_nonneg hC hD]

/-- Fixed-direction Cramér–Rao variational inequality. Its score and
second directional derivative are the actual Fréchet derivatives of `V`. -/
theorem raw_secondMoment_lower
    (V : E → ℝ) (u v : E) {a C k : ℝ}
    (hV : ContDiff ℝ 2 V) (ha : 0 < a) (hC : 0 ≤ C) (hk : 0 ≤ k)
    (hlower : ∀ x, a * ‖x‖ ^ 2 ≤ V x)
    (hscore : ∀ x, |score V v x| ≤ C * ‖x‖)
    (hH0 : ∀ x, 0 ≤ fderiv ℝ (score V v) x v)
    (hH : ∀ x, fderiv ℝ (score V v) x v ≤ k) :
    (2 * ⟪u, v⟫ - k) * (∫ x, weight V x) ≤
      ∫ x, ⟪u, x⟫ ^ 2 * weight V x := by
  let l : E → ℝ := fun x => ⟪u, x⟫
  let s : E → ℝ := score V v
  let H : E → ℝ := fun x => fderiv ℝ s x v
  have hlc : Continuous l := (innerSL ℝ u).continuous
  have hsc : ContDiff ℝ 1 s := score_contDiff hV v
  have hHc : Continuous H :=
    ((hsc.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const)
  have hlb (x : E) : |l x| ≤ ‖u‖ * ‖x‖ := abs_real_inner_le_norm u x
  have hwi := integrable_weight hV.continuous ha hlower
  have hli := integrable_weighted_linear_growth hV.continuous ha (norm_nonneg u) hlower hlc hlb
  have hsi := integrable_weighted_linear_growth hV.continuous ha hC hlower hsc.continuous hscore
  have hlsi := integrable_weighted_product_growth hV.continuous ha (norm_nonneg u) hC
    hlower hlc hsc.continuous hlb hscore
  have hl2i : Integrable (fun x => l x ^ 2 * weight V x) := by
    simpa only [pow_two] using integrable_weighted_product_growth hV.continuous ha
      (norm_nonneg u) (norm_nonneg u) hlower hlc hlc hlb hlb
  have hs2i : Integrable (fun x => s x ^ 2 * weight V x) := by
    simpa only [pow_two] using integrable_weighted_product_growth hV.continuous ha
      hC hC hlower hsc.continuous hsc.continuous hscore hscore
  have hHi : Integrable (fun x => H x * weight V x) := by
    apply integrable_weighted_growth hV.continuous ha hk hlower hHc
    intro x
    rw [abs_of_nonneg (hH0 x)]
    exact (hH x).trans (by nlinarith [sq_nonneg ‖x‖])
  have hld (x : E) : fderiv ℝ l x v = ⟪u, v⟫ :=
    congrArg (fun L : E →L[ℝ] ℝ => L v) (innerSL ℝ u).hasFDerivAt.fderiv
  have hwd (x : E) : fderiv ℝ (weight V) x v = -s x * weight V x :=
    fderiv_weight (hV.differentiable (by norm_num)) v x
  have hlwdi : Integrable (fun x => l x * fderiv ℝ (weight V) x v) := by
    simp_rw [hwd]
    have he : (fun x => l x * (-s x * weight V x)) =
        (fun x => -((l x * s x) * weight V x)) := by funext x; ring
    rw [he]
    exact hlsi.neg
  have hswdi : Integrable (fun x => s x * fderiv ℝ (weight V) x v) := by
    simp_rw [hwd]
    have he : (fun x => s x * (-s x * weight V x)) =
        (fun x => -(s x ^ 2 * weight V x)) := by funext x; ring
    rw [he]
    exact hs2i.neg
  have hibp1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := l) (g := weight V) (v := v)
    (by simpa only [hld] using hwi.const_mul ⟪u, v⟫) hlwdi hli
    (fun x _ => (innerSL ℝ u).differentiableAt)
    (fun x _ => ((hV.differentiable (by norm_num) x).neg.exp))
  have hibp2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := s) (g := weight V) (v := v) hHi hswdi hsi
    (fun x _ => hsc.differentiable (by norm_num) x)
    (fun x _ => ((hV.differentiable (by norm_num) x).neg.exp))
  have hcross : (∫ x, (l x * s x) * weight V x) = ⟪u, v⟫ * ∫ x, weight V x := by
    simp only [hld, hwd] at hibp1
    have he : (fun x => l x * (-s x * weight V x)) =
        (fun x => -((l x * s x) * weight V x)) := by funext x; ring
    rw [he, integral_neg, integral_const_mul] at hibp1
    linarith
  have hsquare : (∫ x, s x ^ 2 * weight V x) = ∫ x, H x * weight V x := by
    simp only [hwd] at hibp2
    have he : (fun x => s x * (-s x * weight V x)) =
        (fun x => -(s x ^ 2 * weight V x)) := by funext x; ring
    rw [he, integral_neg] at hibp2
    exact neg_injective hibp2
  have hsb : (∫ x, s x ^ 2 * weight V x) ≤ k * ∫ x, weight V x := by
    rw [hsquare, ← integral_const_mul]
    exact integral_mono hHi (hwi.const_mul k) (fun x =>
      mul_le_mul_of_nonneg_right (hH x) (Real.exp_pos _).le)
  have hnonneg : 0 ≤ ∫ x, (l x - s x) ^ 2 * weight V x :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have he : (fun x => (l x - s x) ^ 2 * weight V x) =
      (fun x => (l x ^ 2 * weight V x - 2 * ((l x * s x) * weight V x)) +
        s x ^ 2 * weight V x) := by funext x; ring
  have hsubi : Integrable (fun x => l x ^ 2 * weight V x -
      2 * ((l x * s x) * weight V x)) := hl2i.sub (hlsi.const_mul 2)
  rw [he, integral_add hsubi hs2i,
    integral_sub hl2i (hlsi.const_mul 2), integral_const_mul, hcross] at hnonneg
  dsimp [l] at hnonneg
  nlinarith

end
end TheoremA2.CramerRao
