import TheoremA2.ConvexSupportMeasure

/-!
# The positive-definite matrix version of the convex-support estimate

Vectors are indexed by an arbitrary finite type, including a disjoint union of
spin and auxiliary coordinates. `quadratic D x` is exactly `xᵀ D x`.
-/

namespace TheoremA2.ConvexSupport

open MeasureTheory
open scoped BigOperators MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordinary matrix quadratic form `xᵀ D x` on a finite real vector. -/
def quadratic (D : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  inner ℝ x ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) D x)

theorem quadratic_eq_sum (D : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    quadratic D x = ∑ i, ∑ j, x i * D i j * x j := by
  simp only [quadratic, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanCLM, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (D i j * x j) * x i = x i * D i j * x j
  ring

/-- An invertible matrix acts as a continuous linear equivalence on Euclidean space. -/
def matrixEquiv (C : Matrix ι ι ℝ) (hC : IsUnit C) :
    EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι where
  toLinearEquiv :=
    { toLinearMap := ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C).toLinearMap
      invFun := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C⁻¹
      left_inv := by
        intro x
        change ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C⁻¹ * (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C) x = x
        rw [← map_mul, C.nonsing_inv_mul (C.isUnit_iff_isUnit_det.mp hC), map_one]
        rfl
      right_inv := by
        intro x
        change ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C * (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C⁻¹) x = x
        rw [← map_mul, C.mul_nonsing_inv (C.isUnit_iff_isUnit_det.mp hC), map_one]
        rfl }
  continuous_toFun := ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C).continuous
  continuous_invFun := ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C⁻¹).continuous

@[simp] theorem matrixEquiv_toContinuousLinearMap
    (C : Matrix ι ι ℝ) (hC : IsUnit C) :
    (matrixEquiv C hC).toContinuousLinearMap = (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C := rfl

@[simp] theorem matrixEquiv_symm_toContinuousLinearMap
    (C : Matrix ι ι ℝ) (hC : IsUnit C) :
    (matrixEquiv C hC).symm.toContinuousLinearMap = (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C⁻¹ := rfl

theorem toEuclideanCLM_adjoint (C : Matrix ι ι ℝ) :
    ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C).adjoint = (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C.conjTranspose := by
  exact (map_star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C).symm

theorem norm_matrix_sq (C : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C x‖ ^ 2 = quadratic (C.conjTranspose * C) x := by
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  simp only [toEuclideanCLM_adjoint, quadratic, map_mul]
  rfl

/-- Every positive-definite covariance matrix has an actual whitening map.
Both the covariance and inverse-covariance identities are proved from the
positive-definite square root supplied by mathlib. -/
theorem exists_matrix_whitening (D : Matrix ι ι ℝ) (hD : D.PosDef) :
    ∃ W : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι,
      (∀ x, ‖W x‖ ^ 2 = quadratic D⁻¹ x) ∧
      (∀ u, ‖W.symm.toContinuousLinearMap.adjoint u‖ ^ 2 = quadratic D u) := by
  let C : Matrix ι ι ℝ := CFC.sqrt D
  have hC : C.PosDef := Matrix.IsStrictlyPositive.posDef
    (IsStrictlyPositive.sqrt D hD.isStrictlyPositive)
  have hCsq : C * C = D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  have hCinv_sq : C⁻¹ * C⁻¹ = D⁻¹ := by
    rw [← Matrix.mul_inv_rev, hCsq]
  let W := (matrixEquiv C hC.isUnit).symm
  refine ⟨W, ?_, ?_⟩
  · intro x
    change ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C⁻¹ x‖ ^ 2 = quadratic D⁻¹ x
    rw [norm_matrix_sq, hC.inv.isHermitian.eq, hCinv_sq]
  · intro u
    change ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) C).adjoint u‖ ^ 2 =
      quadratic D u
    rw [toEuclideanCLM_adjoint, hC.isHermitian.eq, norm_matrix_sq,
      hC.isHermitian.eq, hCsq]

/-- The exponent `hᵀx - xᵀD⁻¹x/2` in Lemma A.22. -/
def matrixObjective (D : Matrix ι ι ℝ)
    (h x : EuclideanSpace ℝ ι) : ℝ :=
  inner ℝ h x - quadratic D⁻¹ x / 2

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- The full positive-definite-matrix form of Lemma A.22, with an attained
maximizer. The law may be discrete, continuous, or singular. -/
theorem matrix_convex_support_with_maximizer
    (D : Matrix ι ι ℝ) (hD : D.PosDef)
    (X : Ω → EuclideanSpace ℝ ι) (hX : Measurable X)
    (hint : ∀ u, Integrable (fun ω => Real.exp (inner ℝ u (X ω))) μ)
    (hmgf : ∀ u,
      (∫ ω, Real.exp (inner ℝ u (X ω)) ∂μ) ≤ Real.exp (quadratic D u / 2))
    (K : Set (EuclideanSpace ℝ ι)) (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K)
    (h : EuclideanSpace ℝ ι) :
    ∃ xstar ∈ K,
      (∀ x ∈ K, matrixObjective D h x ≤ matrixObjective D h xstar) ∧
      (∫ ω, K.indicator (fun x => Real.exp (inner ℝ h x)) (X ω) ∂μ) ≤
        Real.exp (matrixObjective D h xstar) := by
  obtain ⟨W, henergy, hproxy⟩ := exists_matrix_whitening D hD
  have hmgfW (u : EuclideanSpace ℝ ι) :
      (∫ ω, Real.exp (inner ℝ u (X ω)) ∂μ) ≤
        Real.exp (‖W.symm.toContinuousLinearMap.adjoint u‖ ^ 2 / 2) := by
    rw [hproxy]
    exact hmgf u
  have hobj : transformedObjective W h = matrixObjective D h := by
    funext x
    simp only [transformedObjective, matrixObjective, henergy]
  simpa only [hobj] using
    measurable_transformed_with_maximizer μ W X hX hint hmgfW K hne hclosed hconvex h

/-- Lemma A.22 in its exact supremum form for a positive-definite finite
real matrix. `quadratic_eq_sum` identifies every quadratic form with the usual
coordinate matrix expression. Finite exponential moments are explicit. -/
theorem matrix_convex_support
    (D : Matrix ι ι ℝ) (hD : D.PosDef)
    (X : Ω → EuclideanSpace ℝ ι) (hX : Measurable X)
    (hint : ∀ u, Integrable (fun ω => Real.exp (inner ℝ u (X ω))) μ)
    (hmgf : ∀ u,
      (∫ ω, Real.exp (inner ℝ u (X ω)) ∂μ) ≤ Real.exp (quadratic D u / 2))
    (K : Set (EuclideanSpace ℝ ι)) (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K)
    (h : EuclideanSpace ℝ ι) :
    (∫ ω, K.indicator (fun x => Real.exp (inner ℝ h x)) (X ω) ∂μ) ≤
      Real.exp (sSup (matrixObjective D h '' K)) := by
  obtain ⟨xstar, hxstar, hmax, hbound⟩ :=
    matrix_convex_support_with_maximizer μ D hD X hX hint hmgf K hne hclosed hconvex h
  have hbdd : BddAbove (matrixObjective D h '' K) := by
    refine ⟨matrixObjective D h xstar, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hmax x hx
  exact hbound.trans (Real.exp_le_exp.mpr
    (le_csSup hbdd ⟨xstar, hxstar, rfl⟩))

end

end TheoremA2.ConvexSupport
