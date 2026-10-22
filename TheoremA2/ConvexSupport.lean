import TheoremA2.Imports

/-!
# A finite-law, isotropic case of Lemma A.22

This file proves the convex-support exponential-moment bound for a finite
probability space and covariance proxy equal to the identity. The ambient space
can be any complete real inner product space, in particular `EuclideanSpace ℝ
(Fin d)` for arbitrary finite `d`. Both the maximizing point and its supporting
inequality are proved to exist from nonemptiness, closedness and convexity.

This file does **not** claim the paper's arbitrary positive-definite matrix
version of A.22, or a proof of Theorem A.2. No analytic estimate from the paper
is added as an axiom or hidden in the definition of a probability law.
-/

namespace TheoremA2.ConvexSupport

open scoped BigOperators

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- An actual finite probability law: nonnegative masses with total mass one. -/
structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

/-- The ordinary finite expectation with respect to the displayed masses. -/
def FiniteProbability.expectation (p : FiniteProbability Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, p.mass ω * f ω

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The exponent in Lemma A.22 when the covariance proxy is the identity. -/
def objective (h x : E) : ℝ := inner ℝ h x - ‖x‖ ^ 2 / 2

/-- A closed convex set has an optimizer for the isotropic quadratic objective.
The supporting inequality is derived from the Hilbert projection theorem. -/
theorem exists_maximizer_and_support
    (K : Set E) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (h : E) :
    ∃ xstar ∈ K,
      (∀ x ∈ K, objective h x ≤ objective h xstar) ∧
      (∀ x ∈ K, inner ℝ h x ≤
        inner ℝ (h - xstar) xstar + inner ℝ xstar x) := by
  obtain ⟨xstar, hxstar, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvex h
  have hsupport :=
    (norm_eq_iInf_iff_real_inner_le_zero hconvex hxstar).mp hmin
  refine ⟨xstar, hxstar, ?_, ?_⟩
  · intro x hx
    have hs := hsupport x hx
    have hn := sq_nonneg ‖x - xstar‖
    rw [norm_sub_sq_real] at hn
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at hs
    have hc := real_inner_comm x xstar
    unfold objective
    nlinarith
  · intro x hx
    have hs := hsupport x hx
    simp only [inner_sub_left, inner_sub_right] at hs ⊢
    linarith

/-- The finite-law identity-covariance case of A.22, with the maximizer explicit.
The only distributional hypothesis is the stated exponential-moment inequality.
The law is allowed to be supported in a proper affine subspace. -/
theorem finite_isotropic_with_maximizer
    (p : FiniteProbability Ω) (X : Ω → E)
    (hmgf : ∀ u : E,
      p.expectation (fun ω => Real.exp (inner ℝ u (X ω))) ≤
        Real.exp (‖u‖ ^ 2 / 2))
    (K : Set E) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (h : E) :
    ∃ xstar ∈ K,
      (∀ x ∈ K, objective h x ≤ objective h xstar) ∧
      p.expectation (fun ω =>
        K.indicator (fun x => Real.exp (inner ℝ h x)) (X ω)) ≤
          Real.exp (objective h xstar) := by
  classical
  obtain ⟨xstar, hxstar, hmax, hsupport⟩ :=
    exists_maximizer_and_support K hne hclosed hconvex h
  refine ⟨xstar, hxstar, hmax, ?_⟩
  unfold FiniteProbability.expectation
  calc
    (∑ ω, p.mass ω *
        (if X ω ∈ K then Real.exp (inner ℝ h (X ω)) else 0)) ≤
      ∑ ω, p.mass ω *
        (Real.exp (inner ℝ (h - xstar) xstar) *
          Real.exp (inner ℝ xstar (X ω))) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (p.nonneg ω)
      by_cases hx : X ω ∈ K
      · simp only [if_pos hx]
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (hsupport (X ω) hx)
      · simp only [if_neg hx]
        positivity
    _ = Real.exp (inner ℝ (h - xstar) xstar) *
        (∑ ω, p.mass ω * Real.exp (inner ℝ xstar (X ω))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ Real.exp (inner ℝ (h - xstar) xstar) *
        Real.exp (‖xstar‖ ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left (hmgf xstar) (Real.exp_pos _).le
    _ = Real.exp (objective h xstar) := by
      rw [← Real.exp_add]
      congr 1
      simp only [objective, inner_sub_left, real_inner_self_eq_norm_sq]
      ring

/-- The supremum form of the same finite-law isotropic bound. The supremum is
over the actual image of the closed convex set under the quadratic objective. -/
theorem finite_isotropic
    (p : FiniteProbability Ω) (X : Ω → E)
    (hmgf : ∀ u : E,
      p.expectation (fun ω => Real.exp (inner ℝ u (X ω))) ≤
        Real.exp (‖u‖ ^ 2 / 2))
    (K : Set E) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (h : E) :
    p.expectation (fun ω =>
      K.indicator (fun x => Real.exp (inner ℝ h x)) (X ω)) ≤
        Real.exp (sSup (objective h '' K)) := by
  classical
  obtain ⟨xstar, hxstar, hmax, hbound⟩ :=
    finite_isotropic_with_maximizer p X hmgf K hne hclosed hconvex h
  have hbdd : BddAbove (objective h '' K) := by
    refine ⟨objective h xstar, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hmax x hx
  exact hbound.trans (Real.exp_le_exp.mpr
    (le_csSup hbdd ⟨xstar, hxstar, rfl⟩))

#print axioms exists_maximizer_and_support
#print axioms finite_isotropic_with_maximizer
#print axioms finite_isotropic

end

end TheoremA2.ConvexSupport
