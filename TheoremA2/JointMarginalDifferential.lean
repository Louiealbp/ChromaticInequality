import TheoremA2.JointReference
import TheoremA2.SpinCovarianceMoments

/-!
# Exact derivatives of the continuous marginal in the joint reference law

The conditional spin law is identified with the literal negative-quadratic
Gibbs law. Its covariance, the log-partition Hessian, and the derivative of the
conditional mean are related by differentiating the finite exponential sums.
-/

namespace TheoremA2.JointMarginal

open TheoremA2.JointReference TheoremA2.PeriodicCells TheoremA2.ConvexSupport
open TheoremA2.PrincipalInverse TheoremA2.SpinCovariance
open scoped BigOperators Matrix
noncomputable section

def fieldLinear {s : ℕ} (v : Fin s → ℝ) : Auxiliary s →L[ℝ] ℝ :=
  ∑ j, v j • PiLp.proj 2 (fun _ : Fin s => ℝ) j

@[simp] theorem fieldLinear_apply {s : ℕ} (v : Fin s → ℝ) (t : Auxiliary s) :
    fieldLinear v t = v ⬝ᵥ WithLp.ofLp t := by
  simp [fieldLinear, dotProduct, PiLp.proj, PiLp.projₗ]

def spinConstant {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (σ : Spin r) : ℝ :=
  -lam * projectedEnergy B σ + h ⬝ᵥ spinVector σ

def spinLinear {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (σ : Spin r) : Auxiliary s →L[ℝ] ℝ := fieldLinear (projection B σ)

def conditional {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (t : Auxiliary s) : FiniteProbability (Spin r) :=
  FiniteExponential.law (spinConstant B lam h) (spinLinear B) t

def logPartition {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) : Auxiliary s → ℝ :=
  FiniteExponential.logPartition (spinConstant B lam h) (spinLinear B)

def covariance {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (t : Auxiliary s) : Matrix (Fin r) (Fin r) ℝ :=
  SpinCovariance.covariance (conditional B lam h t) spinVector

theorem spinLinear_apply {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (σ : Spin r) (t : Auxiliary s) :
    spinLinear B σ t = (B *ᵥ WithLp.ofLp t) ⬝ᵥ spinVector σ := by
  rw [spinLinear, fieldLinear_apply, dotProduct_comm (B *ᵥ WithLp.ofLp t),
    JointPrecision.dot_transpose]
  rfl

theorem quadratic_spin_interaction {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (σ : Spin r) :
    quadratic ((2 * lam) • (B * B.transpose)) (spinVector σ) =
      2 * lam * projectedEnergy B σ := by
  unfold quadratic
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← Matrix.mulVec_mulVec, JointPrecision.dot_transpose, JointPrecision.dot_self]
  rfl

theorem conditional_weight_eq {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (t : Auxiliary s) (σ : Spin r) :
    FiniteExponential.weight (spinConstant B lam h) (spinLinear B) t σ =
      spinWeight ((2 * lam) • (B * B.transpose)) (h + B *ᵥ WithLp.ofLp t) σ := by
  rw [FiniteExponential.weight, spinConstant, spinLinear_apply,
    spinWeight, add_dotProduct, quadratic_spin_interaction]
  congr 1
  ring

/-- The precise matrix and field of the actual conditional law. -/
theorem conditional_eq_spinLaw {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (t : Auxiliary s) :
    conditional B lam h t =
      spinLaw ((2 * lam) • (B * B.transpose)) (h + B *ᵥ WithLp.ofLp t) := by
  unfold conditional FiniteExponential.law spinLaw
  congr 1
  funext σ
  simp only [FiniteExponential.partition, spinPartition, conditional_weight_eq]

theorem covariance_posSemidef {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (t : Auxiliary s) :
    (covariance B lam h t).PosSemidef := spin_covariance_posSemidef _

theorem contDiff_covariance_entry {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (i j : Fin r) :
    ContDiff ℝ ⊤ (fun t => covariance B lam h t i j) := by
  simp only [covariance, covariance_eq_second_moment, mean, conditional]
  exact (FiniteExponential.contDiff_expectation _ _ _).sub
    ((FiniteExponential.contDiff_expectation _ _ _).mul
      (FiniteExponential.contDiff_expectation _ _ _))

theorem continuous_covariance {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) : Continuous (covariance B lam h) := by
  exact continuous_pi fun i => continuous_pi fun j =>
    (contDiff_covariance_entry B lam h i j).continuous

theorem continuous_conditional_variance {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h u : Fin r → ℝ) :
    Continuous (fun t => quadratic (covariance B lam h t) u) := by
  exact continuous_const.dotProduct ((continuous_covariance B lam h).matrix_mulVec continuous_const)

theorem covariance_bilinear {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : FiniteProbability Ω) (X : Ω → ι → ℝ) (u v : ι → ℝ) :
    p.expectation (fun ω => (u ⬝ᵥ X ω) * (v ⬝ᵥ X ω)) -
      p.expectation (fun ω => u ⬝ᵥ X ω) *
        p.expectation (fun ω => v ⬝ᵥ X ω) =
      u ⬝ᵥ (SpinCovariance.covariance p X *ᵥ v) := by
  simp only [Matrix.mulVec, dotProduct, covariance_eq_second_moment,
    Finset.mul_sum, Finset.sum_mul, expectation_sum,
    expectation_const_mul, Finset.sum_sub_distrib,
    mul_sub, sub_mul, mean]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show (fun ω => u i * X ω i * (v j * X ω j)) =
      (fun ω => u i * v j * (X ω i * X ω j)) by funext ω; ring]
    rw [expectation_const_mul]
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The log-partition Hessian is the projected actual conditional covariance. -/
theorem second_direction_logPartition {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) (t v w : Auxiliary s) :
    fderiv ℝ (fun x => fderiv ℝ (logPartition B lam h) x v) t w =
      (B *ᵥ WithLp.ofLp v) ⬝ᵥ
        (covariance B lam h t *ᵥ (B *ᵥ WithLp.ofLp w)) := by
  rw [logPartition, FiniteExponential.second_direction_logPartition]
  simp_rw [spinLinear_apply]
  exact covariance_bilinear _ _ _ _

def conditionalLinearMean {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h u : Fin r → ℝ) (v : Fin s → ℝ) (t : Auxiliary s) : ℝ :=
  (conditional B lam h t).expectation (fun σ => u ⬝ᵥ spinVector σ) + fieldLinear v t

theorem contDiff_logPartition {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h : Fin r → ℝ) : ContDiff ℝ ⊤ (logPartition B lam h) :=
  FiniteExponential.contDiff_logPartition _ _

theorem contDiff_conditionalLinearMean {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h u : Fin r → ℝ) (v : Fin s → ℝ) :
    ContDiff ℝ ⊤ (conditionalLinearMean B lam h u v) :=
  (FiniteExponential.contDiff_expectation _ _ _).add (fieldLinear v).contDiff

/-- Differentiating the literal conditional mean gives the covariance term. -/
theorem fderiv_conditionalLinearMean {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (h u : Fin r → ℝ) (v : Fin s → ℝ) (t w : Auxiliary s) :
    fderiv ℝ (conditionalLinearMean B lam h u v) t w =
      u ⬝ᵥ (covariance B lam h t *ᵥ (B *ᵥ WithLp.ofLp w)) +
        v ⬝ᵥ WithLp.ofLp w := by
  have hd := (FiniteExponential.hasFDerivAt_expectation
    (spinConstant B lam h) (spinLinear B) (fun σ => u ⬝ᵥ spinVector σ) t).add
      (fieldLinear v).hasFDerivAt
  change HasFDerivAt (conditionalLinearMean B lam h u v) _ t at hd
  rw [hd.fderiv, ContinuousLinearMap.add_apply, fieldLinear_apply,
    FiniteExponential.expectationGradient_apply]
  simp_rw [spinLinear_apply]
  rw [covariance_bilinear]
  rfl

end
end TheoremA2.JointMarginal
