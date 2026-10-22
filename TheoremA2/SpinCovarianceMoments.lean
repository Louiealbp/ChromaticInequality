import TheoremA2.SpinCovarianceBasic

/-!
# Quadratic covariance forms and zero-field symmetry

These are exact finite expectation identities. No covariance bound is assumed.
-/

namespace TheoremA2.SpinCovariance

open TheoremA2.ConvexSupport TheoremA2.PrincipalInverse
open scoped BigOperators Matrix

noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

def outerMatrix (x : ι → ℝ) : Matrix ι ι ℝ := fun i j => x i * x j

omit [DecidableEq ι] in
theorem quadratic_outerMatrix (x z : ι → ℝ) :
    quadratic (outerMatrix x) z = (z ⬝ᵥ x) ^ 2 := by
  rw [quadratic_eq_sum]
  simp only [outerMatrix, dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
theorem quadratic_sub (A B : Matrix ι ι ℝ) (z : ι → ℝ) :
    quadratic (A - B) z = quadratic A z - quadratic B z := by
  simp only [quadratic, Matrix.sub_mulVec, dotProduct_sub]

omit [Fintype ι] [DecidableEq ι] in
theorem covariance_matrix_moments (p : FiniteProbability Ω) (X : Ω → ι → ℝ) :
    covariance p X = meanMatrix p (fun ω => outerMatrix (X ω)) - outerMatrix (mean p X) := by
  ext i j
  exact covariance_eq_second_moment p X i j

omit [DecidableEq ι] in
theorem quadratic_covariance_moments (p : FiniteProbability Ω) (X : Ω → ι → ℝ)
    (z : ι → ℝ) :
    quadratic (covariance p X) z =
      p.expectation (fun ω => (z ⬝ᵥ X ω) ^ 2) - (z ⬝ᵥ mean p X) ^ 2 := by
  rw [covariance_matrix_moments, quadratic_sub, quadratic_meanMatrix, quadratic_outerMatrix]
  simp_rw [quadratic_outerMatrix]

omit [Fintype ι] [DecidableEq ι] in
theorem covariance_isHermitian (p : FiniteProbability Ω) (X : Ω → ι → ℝ) :
    (covariance p X).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, conj_trivial, covariance]
  apply expectation_congr
  intro ω
  ring

theorem covariance_matrix_two_difference (p : FiniteProbability (SpinConfig ι)) :
    covariance p spinVector =
      (2 : ℝ) • meanMatrix (independent p p) (fun x => outerMatrix (pairDifference x)) := by
  ext i j
  exact covariance_eq_two_difference_moment p i j

theorem quadratic_covariance_two_difference (p : FiniteProbability (SpinConfig ι))
    (z : ι → ℝ) :
    quadratic (covariance p spinVector) z =
      2 * (independent p p).expectation (fun x => (z ⬝ᵥ pairDifference x) ^ 2) := by
  rw [covariance_matrix_two_difference]
  simp only [quadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  change 2 * quadratic (meanMatrix (independent p p)
    (fun x => outerMatrix (pairDifference x))) z = _
  rw [quadratic_meanMatrix]
  simp_rw [quadratic_outerMatrix]

theorem spin_covariance_posSemidef (p : FiniteProbability (SpinConfig ι)) :
    (covariance p spinVector).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (covariance_isHermitian p spinVector)
  intro z
  change 0 ≤ quadratic (covariance p spinVector) z
  rw [quadratic_covariance_two_difference]
  exact mul_nonneg (by norm_num) (expectation_nonneg _ (fun _ => sq_nonneg _))

def negateSpin (σ : SpinConfig ι) : SpinConfig ι := fun i => !(σ i)

def negateSpinEquiv : SpinConfig ι ≃ SpinConfig ι where
  toFun := negateSpin
  invFun := negateSpin
  left_inv σ := by funext i; simp [negateSpin]
  right_inv σ := by funext i; simp [negateSpin]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem spinVector_negateSpin (σ : SpinConfig ι) :
    spinVector (negateSpin σ) = -spinVector σ := by
  funext i
  exact sign_not (σ i)

omit [DecidableEq ι] in
theorem quadratic_neg (N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadratic N (-x) = quadratic N x := by
  simp only [quadratic, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

omit [DecidableEq ι] in
theorem spinWeight_negate_zero (N : Matrix ι ι ℝ) (σ : SpinConfig ι) :
    spinWeight N 0 (negateSpin σ) = spinWeight N 0 σ := by
  simp only [spinWeight, zero_dotProduct, spinVector_negateSpin, quadratic_neg]

theorem spinLaw_mass_negate_zero (N : Matrix ι ι ℝ) (σ : SpinConfig ι) :
    (spinLaw N 0).mass (negateSpin σ) = (spinLaw N 0).mass σ := by
  simp only [spinLaw, spinWeight_negate_zero]

/-- Zero-field mean vanishes by an explicit sign-flip bijection of the sample space. -/
theorem spinLaw_zero_mean (N : Matrix ι ι ℝ) :
    mean (spinLaw N 0) spinVector = 0 := by
  funext i
  have hh := negateSpinEquiv.sum_comp
    (fun σ : SpinConfig ι => (spinLaw N 0).mass σ * spinVector σ i)
  change (∑ σ, (spinLaw N 0).mass (negateSpin σ) * spinVector (negateSpin σ) i) = _ at hh
  simp only [spinLaw_mass_negate_zero, spinVector_negateSpin, Pi.neg_apply,
    mul_neg, Finset.sum_neg_distrib] at hh
  change (∑ σ, (spinLaw N 0).mass σ * spinVector σ i) = 0
  linarith

theorem zero_field_quadratic_covariance (N : Matrix ι ι ℝ) (z : ι → ℝ) :
    quadratic (covariance (spinLaw N 0) spinVector) z =
      (spinLaw N 0).expectation (fun σ => (z ⬝ᵥ spinVector σ) ^ 2) := by
  rw [quadratic_covariance_moments, spinLaw_zero_mean]
  simp

/-- The empty coordinate type has no nonzero quadratic form; its zero-field
estimate is automatic and does not require a positive-dimensional analytic lemma. -/
theorem empty_zero_field_second_moment [IsEmpty ι]
    (N M : Matrix ι ι ℝ) (z : ι → ℝ) :
    (spinLaw N 0).expectation (fun σ => (z ⬝ᵥ spinVector σ) ^ 2) = quadratic M z := by
  simp [dotProduct, quadratic, expectation_const]

end

end TheoremA2.SpinCovariance
