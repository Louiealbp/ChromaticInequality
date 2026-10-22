import TheoremA2.EnvelopeCramerRao
import BrascampLieb.NormalizedVariance

/-!
# Actual Hessians and domination for the envelope under all linear fields

The precision comparisons below are computed from the actual Fréchet
Hessian. Gaussian domination supplies the global integrability assumptions
used in whole-space and box Brascamp–Lieb, including every linear tilt.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory Measure ProbabilityTheory GinibrePoincare
open TheoremA2.PrincipalInverse TheoremA2.CosineEnvelope TheoremA2.CramerRao
open TheoremA2.BrascampLieb
open scoped Topology RealInnerProductSpace Matrix MatrixOrder BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tiltedEnvelopePotential (T : Matrix ι ι ℝ) (h x : EuclideanSpace ℝ ι) : ℝ :=
  euclideanEnvelopePotential T x - ⟪h, x⟫

theorem tiltedEnvelopePotential_contDiff (T : Matrix ι ι ℝ)
    (h : EuclideanSpace ℝ ι) : ContDiff ℝ 2 (tiltedEnvelopePotential T h) :=
  (euclideanEnvelopePotential_contDiff T).sub (innerSL ℝ h).contDiff

theorem inner_toLp (u : ι → ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪WithLp.toLp 2 u, x⟫ = u ⬝ᵥ WithLp.ofLp x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [WithLp.ofLp_toLp, Pi.star_apply, star_trivial]
  exact dotProduct_comm _ _

theorem inner_toLp_right (u : EuclideanSpace ℝ ι) (x : ι → ℝ) :
    ⟪u, WithLp.toLp 2 x⟫ = WithLp.ofLp u ⬝ᵥ x := by
  simpa only [WithLp.toLp_ofLp, WithLp.ofLp_toLp] using
    inner_toLp (WithLp.ofLp u) (WithLp.toLp 2 x)

theorem actualHessian_euclideanEnvelopePotential {T : Matrix ι ι ℝ}
    (hT : T.PosDef) (x : EuclideanSpace ℝ ι) :
    correspondenceBrascampLiebHessian (euclideanEnvelopePotential T)
        (EuclideanSpace.basisFun ι ℝ) x =
      T⁻¹ + Matrix.diagonal (fun i => deriv (deriv envelope) (x i)) := by
  ext i j
  change fderiv ℝ (score (euclideanEnvelopePotential T) (EuclideanSpace.basisFun ι ℝ i))
    x (EuclideanSpace.basisFun ι ℝ j) = _
  rw [second_mixed_euclideanEnvelopePotential]
  have hsym : T⁻¹ j i = T⁻¹ i j := by
    simpa only [star_trivial] using hT.inv.isHermitian.apply i j
  simp only [EuclideanSpace.inner_basisFun_real, EuclideanSpace.basisFun_inner]
  have hp (a c : ι) : (precisionMap T (EuclideanSpace.basisFun ι ℝ a)) c = T⁻¹ c a := by
    change (WithLp.ofLp (precisionMap T (EuclideanSpace.basisFun ι ℝ a))) c = _
    rw [precisionMap, Matrix.ofLp_toEuclideanCLM]
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.ofLp_single,
      Matrix.mulVec_single_one]
    rfl
  rw [hp, hp, hsym]
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.toLp_apply,
    Pi.single_apply, Matrix.add_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

theorem actualHessian_linear (u x : EuclideanSpace ℝ ι) :
    correspondenceBrascampLiebHessian (fun y => ⟪u, y⟫)
      (EuclideanSpace.basisFun ι ℝ) x = 0 := by
  ext i j
  have hd : bakryEmeryGibbsDirectional (fun y => ⟪u, y⟫)
      (EuclideanSpace.basisFun ι ℝ i) =
      fun _ => ⟪u, EuclideanSpace.basisFun ι ℝ i⟫ := by
    funext y
    exact congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun ι ℝ i)) (innerSL ℝ u).hasFDerivAt.fderiv
  simp only [correspondenceBrascampLiebHessian, hd, bakryEmeryGibbsDirectional,
    fderiv_const_apply, ContinuousLinearMap.zero_apply, Matrix.zero_apply]

theorem actualHessian_tiltedEnvelopePotential {T : Matrix ι ι ℝ}
    (hT : T.PosDef) (h x : EuclideanSpace ℝ ι) :
    correspondenceBrascampLiebHessian (tiltedEnvelopePotential T h)
        (EuclideanSpace.basisFun ι ℝ) x =
      T⁻¹ + Matrix.diagonal (fun i => deriv (deriv envelope) (x i)) := by
  have he : tiltedEnvelopePotential T h =
      fun y => euclideanEnvelopePotential T y + ⟪-h, y⟫ := by
    funext y
    simp only [tiltedEnvelopePotential, inner_neg_left, sub_eq_add_neg]
  have hlin : ContDiff ℝ 2 (fun y => ⟪-h, y⟫) := (innerSL ℝ (-h)).contDiff
  rw [he, actualHessian_add (EuclideanSpace.basisFun ι ℝ)
    (euclideanEnvelopePotential_contDiff T) hlin,
    actualHessian_linear, add_zero, actualHessian_euclideanEnvelopePotential hT]

def envelopePrecision (T : Matrix ι ι ℝ) (κ : ℝ) : Matrix ι ι ℝ :=
  T⁻¹ + Matrix.diagonal (fun _ => κ)

theorem envelopePrecision_posDef {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {κ : ℝ} (hκ : 0 ≤ κ) : (envelopePrecision T κ).PosDef :=
  hT.inv.add_posSemidef (Matrix.PosSemidef.diagonal fun _ => hκ)

theorem envelope_hessian_difference_posSemidef {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {κ : ℝ} (hκ : κ ≤ 1) (h x : EuclideanSpace ℝ ι) :
    (correspondenceBrascampLiebHessian (tiltedEnvelopePotential T h)
      (EuclideanSpace.basisFun ι ℝ) x - envelopePrecision T κ).PosSemidef := by
  rw [actualHessian_tiltedEnvelopePotential hT]
  have he : T⁻¹ + Matrix.diagonal (fun i => deriv (deriv envelope) (x i)) -
      envelopePrecision T κ = Matrix.diagonal (fun i => deriv (deriv envelope) (x i) - κ) := by
    unfold envelopePrecision
    rw [add_sub_add_left_eq_sub, ← Matrix.diagonal_sub]
  rw [he]
  exact Matrix.PosSemidef.diagonal fun i => sub_nonneg.mpr (hκ.trans (envelope_curvature_lower (x i)))

theorem actualGradient_linear (u x : EuclideanSpace ℝ ι) :
    correspondenceBrascampLiebGradient (fun y => ⟪u, y⟫)
      (EuclideanSpace.basisFun ι ℝ) x = WithLp.ofLp u := by
  funext i
  have hd := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun ι ℝ i)) ((innerSL ℝ u).hasFDerivAt (x := x)).fderiv
  have hb : ⟪u, EuclideanSpace.basisFun ι ℝ i⟫ = u i := by
    simp only [EuclideanSpace.inner_basisFun_real]
  exact hd.trans hb

theorem actualGradient_linear_sq (u x : EuclideanSpace ℝ ι) :
    correspondenceBrascampLiebGradient (fun y => ⟪u, y⟫ ^ 2)
      (EuclideanSpace.basisFun ι ℝ) x = (2 * ⟪u, x⟫) • WithLp.ofLp u := by
  funext i
  have hd := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ =>
    L (EuclideanSpace.basisFun ι ℝ i)) (((innerSL ℝ u).hasFDerivAt (x := x)).pow 2).fderiv
  simp only [nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
    EuclideanSpace.inner_basisFun_real, Pi.smul_apply] at hd
  exact hd

theorem integrable_tiltedEnvelope_weighted_growth {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (h : EuclideanSpace ℝ ι) {f : EuclideanSpace ℝ ι → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C * (1 + ‖x‖ ^ 2)) :
    Integrable (fun x => f x * bakryEmeryGibbsWeight (tiltedEnvelopePotential T h) x) := by
  apply integrable_of_quadratic_gaussian_bound (by norm_num : (0 : ℝ) < 1 / 2) h
    (hf.mul (Real.continuous_exp.comp (tiltedEnvelopePotential_contDiff T h).continuous.neg)).aestronglyMeasurable
  intro x
  change |f x * Real.exp (-tiltedEnvelopePotential T h x)| ≤ _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hw : Real.exp (-tiltedEnvelopePotential T h x) ≤
      Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2 + ⟪h, x⟫) := by
    apply Real.exp_le_exp.mpr
    unfold tiltedEnvelopePotential
    linarith [euclideanEnvelopePotential_quadratic_lower hT x]
  exact mul_le_mul (hbound x) hw (Real.exp_pos _).le
    (mul_nonneg hC (by positivity))

theorem integrable_tiltedEnvelope_weight {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (h : EuclideanSpace ℝ ι) :
    Integrable (bakryEmeryGibbsWeight (tiltedEnvelopePotential T h)) := by
  have hi := integrable_tiltedEnvelope_weighted_growth hT h (by norm_num : (0 : ℝ) ≤ 1)
    (continuous_const : Continuous (fun _ : EuclideanSpace ℝ ι => (1 : ℝ)))
    (fun x => by simp only [abs_one, one_mul]; nlinarith [sq_nonneg ‖x‖])
  simpa only [one_mul] using hi

theorem integrable_tiltedEnvelope_linear {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (h u : EuclideanSpace ℝ ι) :
    Integrable (fun x => ⟪u, x⟫ * bakryEmeryGibbsWeight (tiltedEnvelopePotential T h) x) := by
  apply integrable_tiltedEnvelope_weighted_growth hT h (norm_nonneg u) (innerSL ℝ u).continuous
  intro x
  apply (abs_real_inner_le_norm u x).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg u)
  nlinarith [sq_nonneg (‖x‖ - 1)]

theorem integrable_tiltedEnvelope_linear_sq {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (h u : EuclideanSpace ℝ ι) :
    Integrable (fun x => ⟪u, x⟫ ^ 2 * bakryEmeryGibbsWeight (tiltedEnvelopePotential T h) x) := by
  apply integrable_tiltedEnvelope_weighted_growth hT h (sq_nonneg ‖u‖)
    ((innerSL ℝ u).continuous.pow 2)
  intro x
  rw [abs_of_nonneg (sq_nonneg _)]
  change ⟪u, x⟫ ^ 2 ≤ ‖u‖ ^ 2 * (1 + ‖x‖ ^ 2)
  have hi := (sq_le_sq₀ (abs_nonneg ⟪u, x⟫)
    (mul_nonneg (norm_nonneg u) (norm_nonneg x))).mpr (abs_real_inner_le_norm u x)
  rw [sq_abs, mul_pow] at hi
  nlinarith [mul_nonneg (sq_nonneg ‖u‖) (sq_nonneg ‖x‖)]

theorem euclideanEnvelopeLaw_tilted {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (h : EuclideanSpace ℝ ι) :
    (euclideanEnvelopeLaw T).tilted (fun x => ⟪h, x⟫) =
      volume.tilted (fun x => -tiltedEnvelopePotential T h x) := by
  rw [euclideanEnvelopeLaw_eq_volume_tilted hT]
  have hi : Integrable (fun x => Real.exp (-euclideanEnvelopePotential T x)) :=
    integrable_weight (euclideanEnvelopePotential_contDiff T).continuous
      (by norm_num : (0 : ℝ) < 1 / 2) (euclideanEnvelopePotential_quadratic_lower hT)
  rw [tilted_tilted hi]
  congr 1
  funext x
  simp only [Pi.add_apply, tiltedEnvelopePotential]
  ring

end
end TheoremA2.GaussianCovariance
