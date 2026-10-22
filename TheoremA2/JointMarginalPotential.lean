import TheoremA2.JointMarginalDifferential

/-!
# The actual marginal potential and its Hessian

The scalar potential is an arbitrary C² function here. The concrete clamped
cosine-prior potentials will be substituted after the differential identities
are established. No Hessian identity is supplied as a hypothesis.
-/

namespace TheoremA2.JointMarginal

open TheoremA2.JointReference TheoremA2.PrincipalInverse
open TheoremA2.ConvexSupport TheoremA2.SpinCovariance
open scoped BigOperators Matrix MatrixOrder
noncomputable section

def potential {r s : ℕ} (U : ℝ → ℝ) (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ) (t : Auxiliary s) : ℝ :=
  (∑ j, U (t j)) - fieldLinear k t - logPartition B lam h t

theorem contDiff_potential {r s : ℕ} {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ) :
    ContDiff ℝ 2 (potential U B lam h k) := by
  apply ContDiff.sub
  · apply ContDiff.sub
    · exact ContDiff.sum fun j _ => hU.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin s => ℝ) j).contDiff
    · exact (fieldLinear k).contDiff
  · exact (contDiff_logPartition B lam h).of_le (by norm_num)

theorem hasFDerivAt_separable {s : ℕ} {U : ℝ → ℝ} (hU : Differentiable ℝ U)
    (t : Auxiliary s) :
    HasFDerivAt (fun x : Auxiliary s => ∑ j, U (x j))
      (∑ j, deriv U (t j) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin s => ℝ) j) t := by
  apply HasFDerivAt.fun_sum
  intro j _
  exact (hU (t j)).hasDerivAt.comp_hasFDerivAt t
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin s => ℝ) j).hasFDerivAt

theorem fderiv_potential {r s : ℕ} {U : ℝ → ℝ} (hU : Differentiable ℝ U)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ)
    (t v : Auxiliary s) :
    fderiv ℝ (potential U B lam h k) t v =
      (∑ j, deriv U (t j) * v j) - fieldLinear k v -
        (conditional B lam h t).expectation (fun σ => spinLinear B σ v) := by
  have hd := ((hasFDerivAt_separable hU t).sub (fieldLinear k).hasFDerivAt).sub
    (FiniteExponential.hasFDerivAt_logPartition (spinConstant B lam h) (spinLinear B) t)
  change HasFDerivAt (potential U B lam h k) _ t at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, PiLp.proj_apply,
    FiniteExponential.logGradient_apply]
  rfl

theorem second_direction_potential {r s : ℕ} {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ)
    (t v w : Auxiliary s) :
    fderiv ℝ (fun x => fderiv ℝ (potential U B lam h k) x v) t w =
      (∑ j, deriv (deriv U) (t j) * v j * w j) -
        (B *ᵥ WithLp.ofLp v) ⬝ᵥ
          (covariance B lam h t *ᵥ (B *ᵥ WithLp.ofLp w)) := by
  have hU' : ContDiff ℝ 1 (deriv U) := hU.deriv'
  have hdU := hU.differentiable (by norm_num)
  have hdU' := hU'.differentiable (by norm_num)
  simp_rw [fderiv_potential hdU]
  have hs : HasFDerivAt (fun x : Auxiliary s => ∑ j, deriv U (x j) * v j)
      (∑ j, (deriv (deriv U) (t j) * v j) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin s => ℝ) j) t := by
    convert HasFDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) =>
      ((hdU' (t j)).hasDerivAt.comp_hasFDerivAt t
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin s => ℝ) j).hasFDerivAt).mul_const (v j)) using 1
    · rfl
    · simp only [smul_smul, mul_comm (v _)]
  have hd := (hs.sub_const (fieldLinear k v)).sub
    (FiniteExponential.hasFDerivAt_expectation (spinConstant B lam h) (spinLinear B)
      (fun σ => spinLinear B σ v) t)
  change HasFDerivAt (fun x : Auxiliary s => (∑ j, deriv U (x j) * v j) -
    fieldLinear k v - (conditional B lam h x).expectation (fun σ => spinLinear B σ v)) _ t at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, PiLp.proj_apply,
    FiniteExponential.expectationGradient_apply]
  simp_rw [spinLinear_apply]
  rw [covariance_bilinear]
  rfl

def hessian {s : ℕ} (W : Auxiliary s → ℝ) (t : Auxiliary s) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j => fderiv ℝ (fun x => fderiv ℝ W x (EuclideanSpace.basisFun (Fin s) ℝ i))
    t (EuclideanSpace.basisFun (Fin s) ℝ j)

def gradient {s : ℕ} (g : Auxiliary s → ℝ) (t : Auxiliary s) : Fin s → ℝ :=
  fun i => fderiv ℝ g t (EuclideanSpace.basisFun (Fin s) ℝ i)

/-- The exact matrix Hessian, with the paper's covariance matrix and signs. -/
theorem hessian_potential {r s : ℕ} {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ)
    (t : Auxiliary s) :
    hessian (potential U B lam h k) t =
      Matrix.diagonal (fun j => deriv (deriv U) (t j)) -
        B.transpose * covariance B lam h t * B := by
  ext i j
  rw [hessian, second_direction_potential hU]
  have hbi (i : Fin s) : WithLp.ofLp (EuclideanSpace.basisFun (Fin s) ℝ i) =
      (Pi.single i 1 : Fin s → ℝ) := by
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.ofLp_single, WithLp.ofLp_toLp]
  rw [hbi i, hbi j, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single,
    PiLp.ofLp_single, WithLp.ofLp_toLp, PiLp.toLp_apply]
  have hdiag : (∑ x, deriv (deriv U) (t x) * ((Pi.single i (1 : ℝ) : Fin s → ℝ) x) * ((Pi.single j (1 : ℝ) : Fin s → ℝ) x)) =
      Matrix.diagonal (fun j => deriv (deriv U) (t j)) i j := by
    by_cases hij : i = j
    · subst j
      simp [Pi.single_apply, Matrix.diagonal_apply]
    · simp [Pi.single_apply, Matrix.diagonal_apply, hij, Ne.symm hij]
  rw [hdiag]
  congr 1
  rw [Matrix.mul_assoc]
  rfl

theorem gradient_conditionalLinearMean {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h u : Fin r → ℝ)
    (v : Fin s → ℝ) (t : Auxiliary s) :
    gradient (conditionalLinearMean B lam h u v) t =
      v + B.transpose *ᵥ (covariance B lam h t *ᵥ u) := by
  funext j
  rw [gradient, fderiv_conditionalLinearMean]
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single,
    PiLp.ofLp_single, WithLp.ofLp_toLp, Matrix.mulVec_single_one, mul_one, dotProduct_single]
  rw [symmetric_bilinear (covariance_posSemidef B lam h t).isHermitian, add_comm]
  rfl

theorem exp_neg_potential {r s : ℕ} (U : ℝ → ℝ) (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ) (t : Auxiliary s) :
    Real.exp (-potential U B lam h k t) =
      Real.exp (fieldLinear k t - ∑ j, U (t j)) *
        FiniteExponential.partition (spinConstant B lam h) (spinLinear B) t := by
  have he : -potential U B lam h k t =
      (fieldLinear k t - ∑ j, U (t j)) + logPartition B lam h t := by
    unfold potential
    ring
  rw [he, Real.exp_add, logPartition, FiniteExponential.logPartition,
    Real.exp_log (FiniteExponential.partition_pos _ _ _)]

/-- The precise all-field spin estimate used in A.33. It will be obtained
from the proved zero-field estimate and the exact two-copy reduction. -/
def SpinCovarianceBound {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam c : ℝ) : Prop :=
  ∀ h : Fin r → ℝ,
    ((JointPrecision.spinPrecision B lam c)⁻¹ -
      SpinCovariance.covariance
        (spinLaw ((2 * lam) • (B * B.transpose)) h) spinVector).PosSemidef

theorem conditional_covariance_le {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam c : ℝ} (hspin : SpinCovarianceBound B lam c)
    (h : Fin r → ℝ) (t : Auxiliary s) :
    covariance B lam h t ≤ (JointPrecision.spinPrecision B lam c)⁻¹ := by
  apply Matrix.le_iff.2
  rw [covariance, conditional_eq_spinLaw]
  exact hspin _

theorem hessian_difference_posSemidef {r s : ℕ} {U : ℝ → ℝ}
    (hU : ContDiff ℝ 2 U) {H : ℝ} (hcurv : ∀ x, H ≤ deriv (deriv U) x)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ) (k : Fin s → ℝ)
    (t : Auxiliary s) :
    (hessian (potential U B lam h k) t -
      JointPrecision.conditionalSchur B H (covariance B lam h t)).PosSemidef := by
  rw [hessian_potential hU]
  have he : Matrix.diagonal (fun j => deriv (deriv U) (t j)) -
      B.transpose * covariance B lam h t * B -
        JointPrecision.conditionalSchur B H (covariance B lam h t) =
      Matrix.diagonal (fun j => deriv (deriv U) (t j) - H) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [JointPrecision.conditionalSchur, Matrix.sub_apply, Matrix.diagonal_apply_eq]
      ring
    · simp only [JointPrecision.conditionalSchur, Matrix.sub_apply,
        Matrix.diagonal_apply_ne _ hij]
      ring
  rw [he]
  exact Matrix.PosSemidef.diagonal (fun j => sub_nonneg.2 (hcurv (t j)))

theorem comparisonSchur_posDef {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam c H : ℝ} (hlam : 0 < lam) (hc : 0 < c) (hH : 1 / (2 * lam) < H)
    (hspin : SpinCovarianceBound B lam c) (h : Fin r → ℝ) (t : Auxiliary s) :
    (JointPrecision.conditionalSchur B H (covariance B lam h t)).PosDef :=
  JointPrecision.conditionalSchur_posDef B hlam hc hH
    (covariance_posSemidef B lam h t).isHermitian (conditional_covariance_le B hspin h t)

/-- The entire conditional-variance expression is bounded at once, exactly
as required by the variational argument in (71). -/
theorem total_variance_integrand_le {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam c H : ℝ} (hlam : 0 < lam) (hc : 0 < c) (hH : 0 < H)
    (hH' : 1 / (2 * lam) < H) (hkappa : 0 ≤ 2 * lam - 1 / H)
    (hspin : SpinCovarianceBound B lam c)
    (h u : Fin r → ℝ) (v : Fin s → ℝ) (t : Auxiliary s) :
    quadratic (covariance B lam h t) u +
      quadratic (JointPrecision.conditionalSchur B H (covariance B lam h t))⁻¹
        (gradient (conditionalLinearMean B lam h u v) t) ≤
      quadratic (JointPrecision.precision B lam c H)⁻¹ (Sum.elim u v) := by
  rw [gradient_conditionalLinearMean]
  exact JointPrecision.conditional_variance_expression_le B
    (JointPrecision.spinPrecision_posDef B hlam.le hc)
    (JointPrecision.precision_posDef B hlam.le hc hH hkappa)
    (covariance_posSemidef B lam h t).isHermitian
    (conditional_covariance_le B hspin h t)
    (comparisonSchur_posDef B hlam hc hH' hspin h t) u v

end
end TheoremA2.JointMarginal
