import TheoremA2.Basic
import TheoremA2.PrincipalInverse

/-!
# Actual negative-quadratic spin laws and independent copies

All expectations below are literal finite sums. The Gibbs law is normalized
from its displayed exponential weights. The two-copy covariance identity and
the disagreement inclusion probability apply to every finite spin law.
-/

namespace TheoremA2.SpinCovariance

open TheoremA2.ConvexSupport TheoremA2.PrincipalInverse
open scoped BigOperators Matrix

noncomputable section

variable {Ω Ξ ι : Type*} [Fintype Ω] [Fintype Ξ] [Fintype ι]

/-- A sign configuration on an arbitrary finite coordinate type. -/
abbrev SpinConfig (ι : Type*) := ι → Bool

/-- Its actual real sign vector. -/
def spinVector (σ : SpinConfig ι) : ι → ℝ := fun i => sign (σ i)

/-- The product law of two independent finite random variables. -/
def independent (p : FiniteProbability Ω) (q : FiniteProbability Ξ) :
    FiniteProbability (Ω × Ξ) where
  mass x := p.mass x.1 * q.mass x.2
  nonneg x := mul_nonneg (p.nonneg x.1) (q.nonneg x.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, q.total, mul_one, p.total]

theorem expectation_independent (p : FiniteProbability Ω) (q : FiniteProbability Ξ)
    (f : Ω × Ξ → ℝ) :
    (independent p q).expectation f =
      p.expectation (fun ω => q.expectation (fun ξ => f (ω, ξ))) := by
  simp only [FiniteProbability.expectation, independent, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]

theorem independent_product_expectation (p : FiniteProbability Ω)
    (q : FiniteProbability Ξ) (f : Ω → ℝ) (g : Ξ → ℝ) :
    (independent p q).expectation (fun x => f x.1 * g x.2) =
      p.expectation f * q.expectation g := by
  rw [expectation_independent]
  simp_rw [expectation_const_mul, expectation_mul_const]

@[simp] theorem independent_first_expectation (p : FiniteProbability Ω)
    (q : FiniteProbability Ξ) (f : Ω → ℝ) :
    (independent p q).expectation (fun x => f x.1) = p.expectation f := by
  rw [expectation_independent]
  simp only [expectation_const]

@[simp] theorem independent_second_expectation (p : FiniteProbability Ω)
    (q : FiniteProbability Ξ) (f : Ξ → ℝ) :
    (independent p q).expectation (fun x => f x.2) = q.expectation f := by
  simp only [expectation_independent, expectation_const]

theorem expectation_congr (p : FiniteProbability Ω) {f g : Ω → ℝ}
    (h : ∀ ω, f ω = g ω) : p.expectation f = p.expectation g := by
  simp_rw [show f = g from funext h]

theorem expectation_mono (p : FiniteProbability Ω) {f g : Ω → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : p.expectation f ≤ p.expectation g := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω)

/-- Covariance is defined by centering the actual coordinate random variables. -/
def covariance (p : FiniteProbability Ω) (X : Ω → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => p.expectation (fun ω =>
    (X ω i - mean p X i) * (X ω j - mean p X j))

omit [Fintype ι] in
theorem covariance_eq_second_moment (p : FiniteProbability Ω) (X : Ω → ι → ℝ)
    (i j : ι) : covariance p X i j =
      p.expectation (fun ω => X ω i * X ω j) - mean p X i * mean p X j := by
  unfold covariance
  have hid (ω : Ω) :
      (X ω i - mean p X i) * (X ω j - mean p X j) =
        X ω i * X ω j - X ω i * mean p X j -
          mean p X i * X ω j + mean p X i * mean p X j := by ring
  simp_rw [hid, expectation_add, expectation_sub, expectation_const_mul,
    expectation_mul_const, expectation_const]
  dsimp only [mean]
  ring

omit [Fintype ι] in
theorem covariance_two_copy (p : FiniteProbability Ω) (X : Ω → ι → ℝ)
    (i j : ι) :
    covariance p X i j = (1 / 2 : ℝ) *
      (independent p p).expectation (fun x =>
        (X x.1 i - X x.2 i) * (X x.1 j - X x.2 j)) := by
  rw [covariance_eq_second_moment]
  have hid (x : Ω × Ω) :
      (X x.1 i - X x.2 i) * (X x.1 j - X x.2 j) =
        X x.1 i * X x.1 j - X x.1 i * X x.2 j -
          X x.2 i * X x.1 j + X x.2 i * X x.2 j := by ring
  simp_rw [hid, expectation_add, expectation_sub]
  rw [independent_first_expectation p p (fun ω => X ω i * X ω j),
    independent_second_expectation p p (fun ω => X ω i * X ω j),
    independent_product_expectation p p (fun ω => X ω i) (fun ω => X ω j)]
  have hm : (independent p p).expectation (fun x => X x.2 i * X x.1 j) =
      p.expectation (fun ω => X ω j) * p.expectation (fun ω => X ω i) := by
    simp_rw [mul_comm (X _ i)]
    exact independent_product_expectation p p (fun ω => X ω j) (fun ω => X ω i)
  rw [hm]
  dsimp only [mean]
  ring

variable [DecidableEq ι]

/-- The actual exponential weight from A.7. -/
def spinWeight (N : Matrix ι ι ℝ) (h : ι → ℝ) (σ : SpinConfig ι) : ℝ :=
  Real.exp (h ⬝ᵥ spinVector σ - quadratic N (spinVector σ) / 2)

def spinPartition (N : Matrix ι ι ℝ) (h : ι → ℝ) : ℝ :=
  ∑ σ : SpinConfig ι, spinWeight N h σ

omit [DecidableEq ι] in
theorem spinWeight_pos (N : Matrix ι ι ℝ) (h : ι → ℝ) (σ : SpinConfig ι) :
    0 < spinWeight N h σ := Real.exp_pos _

theorem spinPartition_pos (N : Matrix ι ι ℝ) (h : ι → ℝ) :
    0 < spinPartition N h := by
  apply Finset.sum_pos
  · intro σ _
    exact spinWeight_pos N h σ
  · exact Finset.univ_nonempty

/-- The normalized Gibbs law; the paper's common `2⁻ᵈ` factor cancels. -/
def spinLaw (N : Matrix ι ι ℝ) (h : ι → ℝ) :
    FiniteProbability (SpinConfig ι) where
  mass σ := spinWeight N h σ / spinPartition N h
  nonneg σ := (div_pos (spinWeight_pos N h σ) (spinPartition_pos N h)).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (spinPartition_pos N h))

theorem spinLaw_mass_pos (N : Matrix ι ι ℝ) (h : ι → ℝ) (σ : SpinConfig ι) :
    0 < (spinLaw N h).mass σ :=
  div_pos (spinWeight_pos N h σ) (spinPartition_pos N h)

/-- Coordinates where the two spins disagree. -/
def disagreement (x : SpinConfig ι × SpinConfig ι) : ι → Bool :=
  fun i => Bool.xor (x.1 i) (x.2 i)

def pairMidpoint (x : SpinConfig ι × SpinConfig ι) : ι → ℝ :=
  fun i => (spinVector x.1 i + spinVector x.2 i) / 2

def pairDifference (x : SpinConfig ι × SpinConfig ι) : ι → ℝ :=
  fun i => (spinVector x.1 i - spinVector x.2 i) / 2

omit [Fintype ι] [DecidableEq ι] in
theorem difference_supported (x : SpinConfig ι × SpinConfig ι) (i : ι)
    (hi : disagreement x i = false) : pairDifference x i = 0 := by
  cases hσ : x.1 i <;> cases hτ : x.2 i <;>
    simp_all [disagreement, pairDifference, spinVector, sign]

omit [Fintype ι] [DecidableEq ι] in
theorem midpoint_disagreement_zero (x : SpinConfig ι × SpinConfig ι) (i : ι)
    (hi : disagreement x i = true) : pairMidpoint x i = 0 := by
  cases hσ : x.1 i <;> cases hτ : x.2 i <;>
    simp_all [disagreement, pairMidpoint, spinVector, sign]

omit [Fintype ι] [DecidableEq ι] in
theorem disagreement_indicator_identity (x : SpinConfig ι × SpinConfig ι) (i : ι) :
    (if disagreement x i then (1 : ℝ) else 0) =
      (1 - spinVector x.1 i * spinVector x.2 i) / 2 := by
  cases hσ : x.1 i <;> cases hτ : x.2 i <;>
    norm_num [disagreement, spinVector, sign, hσ, hτ]

/-- Exact inclusion probability, including nonzero external fields. -/
theorem disagreement_probability (p : FiniteProbability (SpinConfig ι)) (i : ι) :
    (independent p p).expectation (fun x => if disagreement x i then 1 else 0) =
      (1 - mean p spinVector i ^ 2) / 2 := by
  simp_rw [disagreement_indicator_identity, div_eq_mul_inv, expectation_mul_const,
    expectation_sub, expectation_const]
  rw [independent_product_expectation p p (fun σ => spinVector σ i)
    (fun σ => spinVector σ i)]
  simp [mean, pow_two]

theorem disagreement_probability_le_half (p : FiniteProbability (SpinConfig ι)) (i : ι) :
    (independent p p).expectation (fun x => if disagreement x i then 1 else 0) ≤
      (1 / 2 : ℝ) := by
  rw [disagreement_probability]
  nlinarith [sq_nonneg (mean p spinVector i)]

/-- Exact two-copy covariance identity in the disagreement vector used in A.31. -/
theorem covariance_eq_two_difference_moment
    (p : FiniteProbability (SpinConfig ι)) (i j : ι) :
    covariance p spinVector i j = 2 *
      (independent p p).expectation (fun x => pairDifference x i * pairDifference x j) := by
  rw [covariance_two_copy]
  have hid (x : SpinConfig ι × SpinConfig ι) :
      pairDifference x i * pairDifference x j = (1 / 4 : ℝ) *
        ((spinVector x.1 i - spinVector x.2 i) *
          (spinVector x.1 j - spinVector x.2 j)) := by
    unfold pairDifference
    ring
  simp_rw [hid, expectation_const_mul]
  ring

end

end TheoremA2.SpinCovariance
