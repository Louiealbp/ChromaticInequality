import TheoremA2.GaussianFourierMoments

/-!
# Finite-product derivation of the Gaussian second Fourier moment

We integrate the actual coordinate factors, including each diagonal term.
This is the tensorization of the proved scalar Fourier moments, without an
assumed multivariate integration-by-parts identity.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fourier (b x : ι → ℝ) : ℂ := Complex.exp (Complex.I * (b ⬝ᵥ x : ℝ))

theorem fourier_eq_prod (b x : ι → ℝ) :
    fourier b x = ∏ i, scalarFourier (b i) (x i) := by
  simp only [fourier, dotProduct, Complex.ofReal_sum, Finset.mul_sum,
    Complex.exp_sum, scalarFourier]

theorem product_scalar_fourier_integrals (b : ι → ℝ) :
    (∏ i, Complex.exp (-(b i ^ 2 : ℝ) / 2)) = Complex.exp (-(normSq b : ℝ) / 2) := by
  rw [← Complex.exp_sum]
  congr 1
  simp only [normSq, Complex.ofReal_sum]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

def pairFactor (b : ι → ℝ) (i j k : ι) (t : ℝ) : ℂ :=
  (if k = i then (t : ℂ) else 1) *
    (if k = j then (t : ℂ) else 1) * scalarFourier (b k) t

theorem pairFactor_product (b x : ι → ℝ) (i j : ι) :
    (∏ k, pairFactor b i j k (x k)) = (x i : ℂ) * (x j : ℂ) * fourier b x := by
  simp only [pairFactor, Finset.prod_mul_distrib, Fintype.prod_ite_eq',
    ← fourier_eq_prod]

theorem integrable_pairFactor (b : ι → ℝ) (i j k : ι) :
    Integrable (pairFactor b i j k) (gaussianReal 0 1) := by
  change Integrable (fun t : ℝ =>
    (if k = i then (t : ℂ) else 1) *
      (if k = j then (t : ℂ) else 1) * scalarFourier (b k) t) _
  by_cases hki : k = i
  · by_cases hkj : k = j
    · simpa only [if_pos hki, if_pos hkj, pow_two] using
        integrable_scalar_fourier_pow 2 (b k)
    · simpa only [if_pos hki, if_neg hkj, mul_one, pow_one] using
        integrable_scalar_fourier_pow 1 (b k)
  · by_cases hkj : k = j
    · simpa only [if_neg hki, if_pos hkj, one_mul, pow_one] using
        integrable_scalar_fourier_pow 1 (b k)
    · simpa only [if_neg hki, if_neg hkj, one_mul, pow_zero] using
        integrable_scalar_fourier_pow 0 (b k)

theorem integrable_coordinate_pair_fourier (b : ι → ℝ) (i j : ι) :
    Integrable (fun x : ι → ℝ => (x i : ℂ) * (x j : ℂ) * fourier b x)
      (standardGaussian (ι := ι)) := by
  have hh := Integrable.fintype_prod (fun k => integrable_pairFactor b i j k)
  simpa only [pairFactor_product, standardGaussian] using hh

theorem integral_pairFactor_diag (b : ι → ℝ) (i k : ι) :
    (∫ t, pairFactor b i i k t ∂gaussianReal 0 1) =
      (if k = i then (1 - (b k ^ 2 : ℝ) : ℂ) else 1) *
        Complex.exp (-(b k ^ 2 : ℝ) / 2) := by
  by_cases hki : k = i
  · simpa only [pairFactor, hki, ite_true, pow_two] using scalar_second_fourier_integral (b k)
  · simpa only [pairFactor, hki, ite_false, one_mul] using scalar_fourier_integral (b k)

theorem integral_pairFactor_offdiag (b : ι → ℝ) {i j : ι} (hij : i ≠ j) (k : ι) :
    (∫ t, pairFactor b i j k t ∂gaussianReal 0 1) =
      (if k = i then Complex.I * b k else 1) *
        (if k = j then Complex.I * b k else 1) * Complex.exp (-(b k ^ 2 : ℝ) / 2) := by
  by_cases hki : k = i
  · have hkj : k ≠ j := hki ▸ hij
    simpa only [pairFactor, if_pos hki, if_neg hkj, mul_one] using
      scalar_first_fourier_integral (b k)
  · by_cases hkj : k = j
    · simpa only [pairFactor, if_neg hki, if_pos hkj, one_mul] using
        scalar_first_fourier_integral (b k)
    · simpa only [pairFactor, if_neg hki, if_neg hkj, one_mul] using
        scalar_fourier_integral (b k)

/-- Every coordinate-pair Fourier moment, with its Kronecker term retained. -/
theorem standard_coordinate_pair_fourier (b : ι → ℝ) (i j : ι) :
    (∫ x : ι → ℝ, (x i : ℂ) * (x j : ℂ) * fourier b x ∂standardGaussian) =
      ((if i = j then (1 : ℂ) else 0) - (b i : ℂ) * b j) *
        Complex.exp (-(normSq b : ℝ) / 2) := by
  have he := funext (fun x : ι → ℝ => (pairFactor_product b x i j).symm)
  rw [he, standardGaussian, integral_fintype_prod_eq_prod]
  by_cases hij : i = j
  · subst j
    simp_rw [integral_pairFactor_diag]
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', product_scalar_fourier_integrals]
    simp only [ite_true, pow_two, Complex.ofReal_mul]
  · simp_rw [integral_pairFactor_offdiag b hij]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Fintype.prod_ite_eq', Fintype.prod_ite_eq', product_scalar_fourier_integrals]
    simp only [hij, ite_false, zero_sub]
    have hi : (Complex.I * (b i : ℂ)) * (Complex.I * (b j : ℂ)) = -(b i : ℂ) * b j := by
      calc
        _ = Complex.I ^ 2 * (b i : ℂ) * b j := by ring
        _ = _ := by rw [Complex.I_sq]; ring
    rw [hi]
    ring

end

end TheoremA2.GaussianCovariance
