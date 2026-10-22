import TheoremA2.ConvexSupport

/-!
# Convex-support estimates for arbitrary probability laws

This module removes the finite sample-space restriction from the isotropic
convex-support bound. Every exponential moment used as an expectation is
explicitly required to be integrable, so the proof does not exploit Lean's
convention that a nonintegrable Bochner integral has value zero.
-/

namespace TheoremA2.ConvexSupport

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Lemma A.22 with identity covariance proxy, for an arbitrary probability law.
The source vector, convex set, and optimizing point are all genuine geometric
objects. Integrability is included explicitly in the hypotheses. -/
theorem measurable_isotropic_with_maximizer
    (X : Ω → E) (hX : Measurable X)
    (hint : ∀ u : E, Integrable (fun ω => Real.exp (inner ℝ u (X ω))) μ)
    (hmgf : ∀ u : E,
      (∫ ω, Real.exp (inner ℝ u (X ω)) ∂μ) ≤ Real.exp (‖u‖ ^ 2 / 2))
    (K : Set E) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (h : E) :
    ∃ xstar ∈ K,
      (∀ x ∈ K, objective h x ≤ objective h xstar) ∧
      (∫ ω, K.indicator (fun x => Real.exp (inner ℝ h x)) (X ω) ∂μ) ≤
        Real.exp (objective h xstar) := by
  classical
  obtain ⟨xstar, hxstar, hmax, hsupport⟩ :=
    exists_maximizer_and_support K hne hclosed hconvex h
  refine ⟨xstar, hxstar, hmax, ?_⟩
  have hrestriction : Integrable
      (fun ω => if X ω ∈ K then Real.exp (inner ℝ h (X ω)) else 0) μ := by
    convert (hint h).indicator (hclosed.measurableSet.preimage hX) using 1
    ext ω
    simp [Set.indicator]
  calc
    (∫ ω, K.indicator (fun x => Real.exp (inner ℝ h x)) (X ω) ∂μ) ≤
      ∫ ω, Real.exp (inner ℝ (h - xstar) xstar) *
        Real.exp (inner ℝ xstar (X ω)) ∂μ := by
      apply integral_mono hrestriction ((hint xstar).const_mul _)
      intro ω
      by_cases hx : X ω ∈ K
      · simp only [if_pos hx]
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (hsupport (X ω) hx)
      · simp only [if_neg hx]
        positivity
    _ = Real.exp (inner ℝ (h - xstar) xstar) *
        (∫ ω, Real.exp (inner ℝ xstar (X ω)) ∂μ) := by
      rw [integral_const_mul]
    _ ≤ Real.exp (inner ℝ (h - xstar) xstar) *
        Real.exp (‖xstar‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (hmgf xstar) (Real.exp_pos _).le
    _ = Real.exp (objective h xstar) := by
      rw [← Real.exp_add]
      congr 1
      simp only [objective, inner_sub_left, real_inner_self_eq_norm_sq]
      ring

/-- Supremum formulation of the arbitrary-law isotropic estimate. -/
theorem measurable_isotropic
    (X : Ω → E) (hX : Measurable X)
    (hint : ∀ u : E, Integrable (fun ω => Real.exp (inner ℝ u (X ω))) μ)
    (hmgf : ∀ u : E,
      (∫ ω, Real.exp (inner ℝ u (X ω)) ∂μ) ≤ Real.exp (‖u‖ ^ 2 / 2))
    (K : Set E) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (h : E) :
    (∫ ω, K.indicator (fun x => Real.exp (inner ℝ h x)) (X ω) ∂μ) ≤
      Real.exp (sSup (objective h '' K)) := by
  obtain ⟨xstar, hxstar, hmax, hbound⟩ :=
    measurable_isotropic_with_maximizer μ X hX hint hmgf K hne hclosed hconvex h
  have hbdd : BddAbove (objective h '' K) := by
    refine ⟨objective h xstar, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hmax x hx
  exact hbound.trans (Real.exp_le_exp.mpr
    (le_csSup hbdd ⟨xstar, hxstar, rfl⟩))

/-- Quadratic energy after an explicitly supplied invertible linear change of coordinates. -/
def transformedObjective (W : E ≃L[ℝ] E) (h x : E) : ℝ :=
  inner ℝ h x - ‖W x‖ ^ 2 / 2

omit [MeasurableSpace E] [BorelSpace E] in
theorem inverse_adjoint_apply (W : E ≃L[ℝ] E) (u : E) :
    W.symm.toContinuousLinearMap.adjoint (W.toContinuousLinearMap.adjoint u) = u := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
theorem transformed_source (W : E ≃L[ℝ] E) (h x : E) :
    inner ℝ (W.symm.toContinuousLinearMap.adjoint h) (W x) = inner ℝ h x := by
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

/-- Anisotropic convex-support estimate with an explicit whitening map.

For a positive-definite matrix `D`, the paper's statement is obtained by
taking `W = D^(-1/2)`: the MGF proxy is then `D`, and `‖W x‖²` is
`xᵀ D⁻¹ x`. This theorem proves the entire change-of-coordinates argument;
the matrix-square-root identification is not asserted in this module.
-/
theorem measurable_transformed_with_maximizer
    (W : E ≃L[ℝ] E) (X : Ω → E) (hX : Measurable X)
    (hint : ∀ u : E, Integrable (fun ω => Real.exp (inner ℝ u (X ω))) μ)
    (hmgf : ∀ u : E,
      (∫ ω, Real.exp (inner ℝ u (X ω)) ∂μ) ≤
        Real.exp (‖W.symm.toContinuousLinearMap.adjoint u‖ ^ 2 / 2))
    (K : Set E) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (h : E) :
    ∃ xstar ∈ K,
      (∀ x ∈ K, transformedObjective W h x ≤ transformedObjective W h xstar) ∧
      (∫ ω, K.indicator (fun x => Real.exp (inner ℝ h x)) (X ω) ∂μ) ≤
        Real.exp (transformedObjective W h xstar) := by
  classical
  have hintY (u : E) : Integrable (fun ω => Real.exp (inner ℝ u (W (X ω)))) μ := by
    simpa only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearEquiv.coe_coe] using
      hint (W.toContinuousLinearMap.adjoint u)
  have hmgfY (u : E) :
      (∫ ω, Real.exp (inner ℝ u (W (X ω))) ∂μ) ≤ Real.exp (‖u‖ ^ 2 / 2) := by
    simpa only [ContinuousLinearMap.adjoint_inner_left, inverse_adjoint_apply,
      ContinuousLinearEquiv.coe_coe] using
      hmgf (W.toContinuousLinearMap.adjoint u)
  have hY : Measurable (fun ω => W (X ω)) := W.continuous.measurable.comp hX
  have hKclosed : IsClosed (W '' K) := W.toHomeomorph.isClosed_image.mpr hclosed
  have hKconvex : Convex ℝ (W '' K) := hconvex.linear_image W.toLinearMap
  obtain ⟨ystar, hystar, hmax, hbound⟩ :=
    measurable_isotropic_with_maximizer μ (fun ω => W (X ω)) hY hintY hmgfY
      (W '' K) (hne.image W) hKclosed hKconvex (W.symm.toContinuousLinearMap.adjoint h)
  rcases hystar with ⟨xstar, hxstar, rfl⟩
  refine ⟨xstar, hxstar, ?_, ?_⟩
  · intro x hx
    have hm := hmax (W x) ⟨x, hx, rfl⟩
    simpa only [objective, transformedObjective, transformed_source] using hm
  · have hindicator (ω : Ω) :
        (W '' K).indicator
          (fun y => Real.exp (inner ℝ (W.symm.toContinuousLinearMap.adjoint h) y))
          (W (X ω)) =
        K.indicator (fun x => Real.exp (inner ℝ h x)) (X ω) := by
      by_cases hx : X ω ∈ K
      · have hWx : W (X ω) ∈ W '' K := ⟨X ω, hx, rfl⟩
        simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hWx, transformed_source]
      · have hWx : W (X ω) ∉ W '' K := by
          rintro ⟨x, hxK, heq⟩
          exact hx (W.injective heq ▸ hxK)
        simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hWx]
    simpa only [hindicator, objective, transformedObjective, transformed_source] using hbound

/-- Supremum version of the anisotropic estimate with a supplied invertible map. -/
theorem measurable_transformed
    (W : E ≃L[ℝ] E) (X : Ω → E) (hX : Measurable X)
    (hint : ∀ u : E, Integrable (fun ω => Real.exp (inner ℝ u (X ω))) μ)
    (hmgf : ∀ u : E,
      (∫ ω, Real.exp (inner ℝ u (X ω)) ∂μ) ≤
        Real.exp (‖W.symm.toContinuousLinearMap.adjoint u‖ ^ 2 / 2))
    (K : Set E) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (h : E) :
    (∫ ω, K.indicator (fun x => Real.exp (inner ℝ h x)) (X ω) ∂μ) ≤
      Real.exp (sSup (transformedObjective W h '' K)) := by
  obtain ⟨xstar, hxstar, hmax, hbound⟩ :=
    measurable_transformed_with_maximizer μ W X hX hint hmgf K hne hclosed hconvex h
  have hbdd : BddAbove (transformedObjective W h '' K) := by
    refine ⟨transformedObjective W h xstar, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hmax x hx
  exact hbound.trans (Real.exp_le_exp.mpr
    (le_csSup hbdd ⟨xstar, hxstar, rfl⟩))

end

end TheoremA2.ConvexSupport
