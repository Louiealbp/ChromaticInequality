import GinibrePoincare.Analysis.CorrespondenceBrascampLieb
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# The concrete Brascamp–Lieb inequality in a form suitable for limits

The whole-space result is rewritten using ordinary weighted Lebesgue moments.
The final elementary limit lemma preserves the normalizing constant. It is
a limit-passage lemma, not an assumed box-domain Brascamp–Lieb theorem.
-/

namespace TheoremA2.BrascampLieb

open MeasureTheory Measure Filter GinibrePoincare
open scoped Topology ContDiff BigOperators Matrix

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

theorem centered_variance_identity (W g : E → ℝ)
    (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hg : MemLp g 2 (correspondenceBrascampLiebMeasure W)) :
    (∫ x, correspondenceBrascampLiebCenter W g x ^ 2
      ∂correspondenceBrascampLiebMeasure W) =
    (∫ x, g x ^ 2 ∂correspondenceBrascampLiebMeasure W) -
      (∫ x, g x ∂correspondenceBrascampLiebMeasure W) ^ 2 /
        (∫ x, bakryEmeryGibbsWeight W x) := by
  letI := correspondenceBrascampLieb_finite_measure W hWi
  have hi : Integrable g (correspondenceBrascampLiebMeasure W) :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (by norm_num))
  have hi2 : Integrable (fun x => g x ^ 2) (correspondenceBrascampLiebMeasure W) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg
  have hZ := correspondenceBrascampLieb_positive_mass W hWi
  have hm : (correspondenceBrascampLiebMeasure W).real Set.univ =
      ∫ x, bakryEmeryGibbsWeight W x := by
    rw [Measure.real, correspondenceBrascampLieb_mass W hWi,
      ENNReal.toReal_ofReal hZ.le]
  let c := correspondenceBrascampLiebMean W g
  have heq : (fun x => correspondenceBrascampLiebCenter W g x ^ 2) =
      (fun x => (g x ^ 2 - (2 * c) * g x) + c ^ 2) := by
    funext x
    dsimp [correspondenceBrascampLiebCenter, c]
    ring
  have hsubi : Integrable (fun x => g x ^ 2 - (2 * c) * g x)
      (correspondenceBrascampLiebMeasure W) := hi2.sub (hi.const_mul (2 * c))
  rw [heq, integral_add hsubi (integrable_const _),
    integral_sub hi2 (hi.const_mul (2 * c)), integral_const_mul, integral_const, hm]
  dsimp [c, correspondenceBrascampLiebMean]
  field_simp [ne_of_gt hZ] <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inversion reverses the positive-semidefinite order, proved on actual
quadratic forms using the verified inverse Cauchy–Schwarz inequality. -/
theorem inverse_quadratic_mono {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : (B - A).PosSemidef) (z : ι → ℝ) :
    z ⬝ᵥ B⁻¹ *ᵥ z ≤ z ⬝ᵥ A⁻¹ *ᵥ z := by
  let y := B⁻¹ *ᵥ z
  have hBy : B *ᵥ y = z := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B (B.isUnit_iff_isUnit_det.mp hB.isUnit),
      Matrix.one_mulVec]
  have hnonneg : 0 ≤ z ⬝ᵥ A⁻¹ *ᵥ z := by
    simpa only [star_trivial] using hA.posSemidef.inv.dotProduct_mulVec_nonneg z
  have hdiff : 0 ≤ y ⬝ᵥ B *ᵥ y - y ⬝ᵥ A *ᵥ y := by
    simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] using
      hAB.dotProduct_mulVec_nonneg y
  have hyB : y ⬝ᵥ B *ᵥ y = z ⬝ᵥ B⁻¹ *ᵥ z := by
    rw [hBy]
    exact dotProduct_comm _ _
  have hyle : y ⬝ᵥ A *ᵥ y ≤ z ⬝ᵥ B⁻¹ *ᵥ z := by
    rw [hyB] at hdiff
    linarith
  have hcs := correspondenceBrascampLieb_inverse_cauchy_schwarz A hA z y
  have hineq : (z ⬝ᵥ B⁻¹ *ᵥ z) ^ 2 ≤
      (z ⬝ᵥ A⁻¹ *ᵥ z) * (z ⬝ᵥ B⁻¹ *ᵥ z) :=
    hcs.trans (mul_le_mul_of_nonneg_left hyle hnonneg)
  by_contra! hlt
  have hp : 0 < z ⬝ᵥ B⁻¹ *ᵥ z := hnonneg.trans_lt hlt
  nlinarith

/-- The actual inverse-Hessian inequality expressed in unnormalized Lebesgue moments. -/
theorem wholeSpace_weighted_variance
    (W g : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2 * bakryEmeryGibbsWeight W x))
    (hgE : Integrable (fun x => correspondenceBrascampLiebInverseEnergy W g b x *
      bakryEmeryGibbsWeight W x)) :
    (∫ x, g x ^ 2 * bakryEmeryGibbsWeight W x) -
      (∫ x, g x * bakryEmeryGibbsWeight W x) ^ 2 /
        (∫ x, bakryEmeryGibbsWeight W x) ≤
      ∫ x, correspondenceBrascampLiebInverseEnergy W g b x * bakryEmeryGibbsWeight W x := by
  have hw : Continuous (bakryEmeryGibbsWeight W) := Real.continuous_exp.comp hW.continuous.neg
  have hwpos (x : E) : 0 < bakryEmeryGibbsWeight W x := Real.exp_pos _
  have hL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W) := by
    apply (memLp_two_iff_integrable_sq hg.continuous.aestronglyMeasurable).mpr
    apply (correspondenceWeightedElliptic_integrable_density
      (bakryEmeryGibbsWeight W) (fun x => g x ^ 2) hw hwpos).mpr
    simpa only [mul_comm] using hg2
  have hE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W) := by
    apply (correspondenceWeightedElliptic_integrable_density
      (bakryEmeryGibbsWeight W) (correspondenceBrascampLiebInverseEnergy W g b) hw hwpos).mpr
    simpa only [mul_comm] using hgE
  have h := correspondenceBrascampLieb_variance W g b hW hWi hpos hg hL2 hE
  rw [centered_variance_identity W g hWi hL2] at h
  simpa only [correspondenceBrascampLieb_integral_density W _ hW.continuous] using h

/-- A pointwise bound on the actual inverse-Hessian energy supplies its
integrability as well as the resulting variance bound. -/
theorem wholeSpace_weighted_variance_of_majorant
    (W g r : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2 * bakryEmeryGibbsWeight W x))
    (hr : Integrable (fun x => r x * bakryEmeryGibbsWeight W x))
    (hbound : ∀ x, correspondenceBrascampLiebInverseEnergy W g b x ≤ r x) :
    (∫ x, g x ^ 2 * bakryEmeryGibbsWeight W x) -
      (∫ x, g x * bakryEmeryGibbsWeight W x) ^ 2 /
        (∫ x, bakryEmeryGibbsWeight W x) ≤
      ∫ x, r x * bakryEmeryGibbsWeight W x := by
  have hnonneg (x : E) : 0 ≤ correspondenceBrascampLiebInverseEnergy W g b x := by
    simpa only [correspondenceBrascampLiebInverseEnergy, star_trivial] using
      (hpos x).posSemidef.inv.dotProduct_mulVec_nonneg
        (correspondenceBrascampLiebGradient g b x)
  have hweight (x : E) : 0 ≤ bakryEmeryGibbsWeight W x := (Real.exp_pos _).le
  have hEi : Integrable (fun x => correspondenceBrascampLiebInverseEnergy W g b x *
      bakryEmeryGibbsWeight W x) := by
    apply hr.mono'
    · exact ((correspondenceBrascampLieb_inverse_energy_continuous W g b hW hg hpos).mul
        (Real.continuous_exp.comp hW.continuous.neg)).aestronglyMeasurable
    · exact Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnonneg x) (hweight x))]
        exact mul_le_mul_of_nonneg_right (hbound x) (hweight x))
  exact (wholeSpace_weighted_variance W g b hW hWi hpos hg hg2 hEi).trans
    (integral_mono hEi hr (fun x => mul_le_mul_of_nonneg_right (hbound x) (hweight x)))

/-- The actual Hessian may be replaced by any smaller positive definite
matrix field, with the precise inverse-gradient quadratic form retained. -/
theorem wholeSpace_weighted_variance_hessian_bound
    (W g : E → ℝ) (b : OrthonormalBasis ι ℝ E) (D : E → Matrix ι ι ℝ)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hD : ∀ x, (D x).PosDef)
    (hHD : ∀ x, (correspondenceBrascampLiebHessian W b x - D x).PosSemidef)
    (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2 * bakryEmeryGibbsWeight W x))
    (hR : Integrable (fun x =>
      (correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
        correspondenceBrascampLiebGradient g b x) * bakryEmeryGibbsWeight W x)) :
    (∫ x, g x ^ 2 * bakryEmeryGibbsWeight W x) -
      (∫ x, g x * bakryEmeryGibbsWeight W x) ^ 2 /
        (∫ x, bakryEmeryGibbsWeight W x) ≤
      ∫ x, (correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
        correspondenceBrascampLiebGradient g b x) * bakryEmeryGibbsWeight W x := by
  have hpos (x : E) : (correspondenceBrascampLiebHessian W b x).PosDef := by
    have heq : correspondenceBrascampLiebHessian W b x =
        D x + (correspondenceBrascampLiebHessian W b x - D x) := by abel
    rw [heq]
    exact (hD x).add_posSemidef (hHD x)
  apply wholeSpace_weighted_variance_of_majorant W g _ b hW hWi hpos hg hg2 hR
  intro x
  exact inverse_quadratic_mono (hD x) (hpos x) (hHD x)
    (correspondenceBrascampLiebGradient g b x)

theorem continuous_matrix_inverse {D : E → Matrix ι ι ℝ} (hDc : Continuous D)
    (hD : ∀ x, (D x).PosDef) : Continuous (fun x => (D x)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hd : (D x).det ≠ 0 := ((D x).isUnit_iff_isUnit_det.mp (hD x).isUnit).ne_zero
  have hi : ContinuousAt Ring.inverse (D x).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  exact (continuousAt_matrix_inv _ hi).comp hDc.continuousAt

/-- A uniform bound on the sum of conditional variance and the comparison
inverse-Hessian energy gives the corresponding total-variance bound. All
energy and conditional-variance integrability is derived here. -/
theorem wholeSpace_totalVariance_bound
    (W g cvar : E → ℝ) (b : OrthonormalBasis ι ℝ E) (D : E → Matrix ι ι ℝ)
    (C : ℝ) (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hDc : Continuous D) (hD : ∀ x, (D x).PosDef)
    (hHD : ∀ x, (correspondenceBrascampLiebHessian W b x - D x).PosSemidef)
    (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2 * bakryEmeryGibbsWeight W x))
    (hcv : Continuous cvar) (hcv0 : ∀ x, 0 ≤ cvar x)
    (htotal : ∀ x, cvar x +
      correspondenceBrascampLiebGradient g b x ⬝ᵥ (D x)⁻¹ *ᵥ
        correspondenceBrascampLiebGradient g b x ≤ C) :
    (∫ x, g x ^ 2 * bakryEmeryGibbsWeight W x) -
      (∫ x, g x * bakryEmeryGibbsWeight W x) ^ 2 /
        (∫ x, bakryEmeryGibbsWeight W x) +
      (∫ x, cvar x * bakryEmeryGibbsWeight W x) ≤
      C * (∫ x, bakryEmeryGibbsWeight W x) := by
  let R : E → ℝ := fun x => correspondenceBrascampLiebGradient g b x ⬝ᵥ
    (D x)⁻¹ *ᵥ correspondenceBrascampLiebGradient g b x
  have hR0 (x : E) : 0 ≤ R x := by
    simpa only [R, star_trivial] using (hD x).posSemidef.inv.dotProduct_mulVec_nonneg
      (correspondenceBrascampLiebGradient g b x)
  have hRc : Continuous R := by
    have hG : Continuous (correspondenceBrascampLiebGradient g b) := by
      apply continuous_pi
      intro i
      exact (hg.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
    exact hG.dotProduct ((continuous_matrix_inverse hDc hD).matrix_mulVec hG)
  have hw : Continuous (bakryEmeryGibbsWeight W) := Real.continuous_exp.comp hW.continuous.neg
  have hw0 (x : E) : 0 ≤ bakryEmeryGibbsWeight W x := (Real.exp_pos _).le
  have hRb (x : E) : R x ≤ C := by have h := htotal x; dsimp [R]; linarith [hcv0 x]
  have hcvb (x : E) : cvar x ≤ C := by have h := htotal x; change cvar x + R x ≤ C at h; linarith [hR0 x]
  have hRi : Integrable (fun x => R x * bakryEmeryGibbsWeight W x) := by
    apply (hWi.const_mul C).mono' (hRc.mul hw).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      change |R x * bakryEmeryGibbsWeight W x| ≤ _
      rw [abs_of_nonneg (mul_nonneg (hR0 x) (hw0 x))]
      exact mul_le_mul_of_nonneg_right (hRb x) (hw0 x))
  have hcvi : Integrable (fun x => cvar x * bakryEmeryGibbsWeight W x) := by
    apply (hWi.const_mul C).mono' (hcv.mul hw).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      change |cvar x * bakryEmeryGibbsWeight W x| ≤ _
      rw [abs_of_nonneg (mul_nonneg (hcv0 x) (hw0 x))]
      exact mul_le_mul_of_nonneg_right (hcvb x) (hw0 x))
  have hv := wholeSpace_weighted_variance_hessian_bound W g b D hW hWi hD hHD hg hg2 hRi
  have hib : (∫ x, R x * bakryEmeryGibbsWeight W x) +
      (∫ x, cvar x * bakryEmeryGibbsWeight W x) ≤ C * (∫ x, bakryEmeryGibbsWeight W x) := by
    rw [← integral_add hRi hcvi, ← integral_const_mul]
    apply integral_mono (hRi.add hcvi) (hWi.const_mul C)
    intro x
    have h := mul_le_mul_of_nonneg_right (htotal x) (hw0 x)
    dsimp [R] at *
    nlinarith
  dsimp [R] at hib
  linarith

/-- Passing the unnormalized variance inequality to a limit retains its exact mass factor. -/
theorem weighted_variance_limit
    (Z M S R : ℕ → ℝ) {z m s r : ℝ}
    (hZ : Tendsto Z atTop (𝓝 z)) (hM : Tendsto M atTop (𝓝 m))
    (hS : Tendsto S atTop (𝓝 s)) (hR : Tendsto R atTop (𝓝 r))
    (hz : 0 < z) (hbound : ∀ n, S n - M n ^ 2 / Z n ≤ R n) :
    s - m ^ 2 / z ≤ r := by
  exact le_of_tendsto_of_tendsto (hS.sub ((hM.pow 2).div hZ (ne_of_gt hz))) hR
    (Eventually.of_forall hbound)

/-- A uniform variance bound survives normalization and a positive-mass limit. -/
theorem normalized_variance_limit
    (Z M S : ℕ → ℝ) {z m s C : ℝ}
    (hZ : Tendsto Z atTop (𝓝 z)) (hM : Tendsto M atTop (𝓝 m))
    (hS : Tendsto S atTop (𝓝 s)) (hz : 0 < z)
    (hbound : ∀ n, S n - M n ^ 2 / Z n ≤ C * Z n) :
    s / z - (m / z) ^ 2 ≤ C := by
  have h := weighted_variance_limit Z M S (fun n => C * Z n)
    hZ hM hS (hZ.const_mul C) hz hbound
  have heq : s / z - (m / z) ^ 2 = (s - m ^ 2 / z) / z := by
    field_simp <;> ring
  rw [heq]
  exact (div_le_iff₀ hz).mpr h

end

end TheoremA2.BrascampLieb
