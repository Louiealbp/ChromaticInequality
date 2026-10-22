import TheoremA2.Imports
import TheoremA2.Basic

/-!
# The actual characteristic function and the cosine-product identity

These identities hold for every real matrix, with no sign, rank, or symmetry
assumption.  They identify the literal expectation of the complex exponential
with the real quantity to which the analytic proof in the paper applies.
-/

namespace TheoremA2

open scoped BigOperators

theorem complexAverage_congr {α : Type*} [Fintype α] {f g : α → ℂ}
    (h : ∀ a, f a = g a) : complexAverage f = complexAverage g := by
  unfold complexAverage
  congr 1
  exact Finset.sum_congr rfl fun a _ => h a

theorem complexAverage_ofReal {α : Type*} [Fintype α] (f : α → ℝ) :
    complexAverage (fun a => (f a : ℂ)) = (average f : ℂ) := by
  simp [complexAverage, average]

theorem complexAverage_re {α : Type*} [Fintype α] (f : α → ℂ) :
    (complexAverage f).re = average (fun a => (f a).re) := by
  simp [complexAverage, average, Complex.mul_re]

/-- Independence of all Boolean coordinates, proved as an identity of finite sums. -/
theorem complexAverage_prod {k : ℕ} (f : Fin k → Bool → ℂ) :
    complexAverage (fun τ : Spin k => ∏ j, f j (τ j)) =
      ∏ j, (f j false + f j true) / 2 := by
  unfold complexAverage
  rw [← Fintype.prod_sum]
  rw [Finset.prod_div_distrib]
  simp [div_eq_mul_inv, mul_comm, add_comm]

theorem sign_exponential_average (x : ℝ) :
    (Complex.exp (((x * sign false : ℝ) : ℂ) * Complex.I) +
      Complex.exp (((x * sign true : ℝ) : ℂ) * Complex.I)) / 2 =
        (Real.cos x : ℂ) := by
  simp only [sign_false, sign_true, mul_neg_one, mul_one, Complex.ofReal_neg]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

/-- Rearrange `σᵀ S τ` as the dot product of `Sᵀ σ` with `τ`. -/
theorem bilinear_eq_sum_columns {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (σ τ : Spin k) :
    bilinear S σ τ =
      ∑ j, (∑ i, sign (σ i) * S i j) * sign (τ j) := by
  unfold bilinear
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

theorem bilinear_exp_eq_prod {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) (σ τ : Spin k) :
    Complex.exp (((t * bilinear S σ τ : ℝ) : ℂ) * Complex.I) =
      ∏ j, Complex.exp
        ((((t * (∑ i, sign (σ i) * S i j)) * sign (τ j) : ℝ) : ℂ) * Complex.I) := by
  rw [bilinear_eq_sum_columns, Finset.mul_sum]
  simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, mul_assoc]

/-- Equation (4): average out the entire independent vector `τ`. -/
theorem characteristic_eq_cosine_product {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) :
    characteristic S t =
      (average (fun σ : Spin k =>
        ∏ j, Real.cos (t * ∑ i, sign (σ i) * S i j)) : ℂ) := by
  unfold characteristic
  calc
    complexAverage (fun σ : Spin k => complexAverage (fun τ : Spin k =>
      Complex.exp (((t * bilinear S σ τ : ℝ) : ℂ) * Complex.I))) =
        complexAverage (fun σ : Spin k =>
          ∏ j, (Real.cos (t * ∑ i, sign (σ i) * S i j) : ℂ)) := by
      apply complexAverage_congr
      intro σ
      simp_rw [bilinear_exp_eq_prod]
      rw [complexAverage_prod (fun j b =>
        Complex.exp
          ((((t * (∑ i, sign (σ i) * S i j)) * sign b : ℝ) : ℂ) * Complex.I))]
      apply Finset.prod_congr rfl
      intro j _
      exact sign_exponential_average _
    _ = _ := by
      simp only [← Complex.ofReal_prod]
      exact complexAverage_ofReal _

theorem characteristic_re {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) :
    (characteristic S t).re = realCharacteristic S t := by
  unfold characteristic realCharacteristic
  rw [complexAverage_re]
  apply average_congr
  intro σ
  rw [complexAverage_re]
  apply average_congr
  intro τ
  exact Complex.exp_ofReal_mul_I_re _

/-- Reality is a theorem about the complex exponential average, not a definition. -/
theorem characteristic_im {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) :
    (characteristic S t).im = 0 := by
  rw [characteristic_eq_cosine_product]
  exact Complex.ofReal_im _

theorem characteristic_eq_realCharacteristic {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) :
    characteristic S t = (realCharacteristic S t : ℂ) := by
  apply Complex.ext
  · simpa using characteristic_re S t
  · simpa using characteristic_im S t

theorem realCharacteristic_eq_cosine_product {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) :
    realCharacteristic S t =
      average (fun σ : Spin k =>
        ∏ j, Real.cos (t * ∑ i, sign (σ i) * S i j)) := by
  have h := congrArg Complex.re (characteristic_eq_cosine_product S t)
  simpa [characteristic_re] using h

end TheoremA2
