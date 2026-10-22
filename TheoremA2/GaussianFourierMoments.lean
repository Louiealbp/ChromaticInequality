import TheoremA2.GaussianCovarianceBasic
import TheoremA2.SpinCovarianceMoments
import TheoremA2.Characteristic

/-!
# Exact Gaussian Fourier moments

The scalar moments are actual derivatives of the Gaussian complex moment-
generating function. Finite product integration then yields the matrix Gaussian
second Fourier moment used in Lemma A.28.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

theorem standard_mgf (z : ℂ) :
    (∫ x : ℝ, Complex.exp (z * x) ∂gaussianReal 0 1) = Complex.exp (z ^ 2 / 2) := by
  simpa [complexMGF] using (complexMGF_id_gaussianReal (μ := 0) (v := 1) z)

theorem standard_exp_interior (z : ℂ) :
    z.re ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
  simp only [integrableExpSet_id_gaussianReal, interior_univ, mem_univ]

theorem integrable_standard_pow_exp (n : ℕ) (z : ℂ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * Complex.exp (z * x)) (gaussianReal 0 1) := by
  exact integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (standard_exp_interior z) n

/-- The first moment is obtained by genuine differentiation under the integral. -/
theorem standard_first_mgf (z : ℂ) :
    (∫ x : ℝ, (x : ℂ) * Complex.exp (z * x) ∂gaussianReal 0 1) =
      z * Complex.exp (z ^ 2 / 2) := by
  have h := hasDerivAt_integral_pow_mul_exp (standard_exp_interior z) 0
  simp only [id_eq, pow_zero, one_mul, zero_add, pow_one] at h
  have he : (fun z : ℂ => ∫ x : ℝ, Complex.exp (z * x) ∂gaussianReal 0 1) =
      (fun z => Complex.exp (z ^ 2 / 2)) := funext standard_mgf
  rw [he] at h
  have hd : HasDerivAt (fun z : ℂ => Complex.exp (z ^ 2 / 2))
      (z * Complex.exp (z ^ 2 / 2)) z := by
    convert (((hasDerivAt_id z).pow 2).div_const 2).cexp using 1 <;> simp only [Pi.pow_apply, id_eq] <;> ring
  exact h.unique hd

/-- The second moment is obtained by differentiating the actual first moment. -/
theorem standard_second_mgf (z : ℂ) :
    (∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp (z * x) ∂gaussianReal 0 1) =
      (1 + z ^ 2) * Complex.exp (z ^ 2 / 2) := by
  have h := hasDerivAt_integral_pow_mul_exp (standard_exp_interior z) 1
  simp only [id_eq, pow_one, show 1 + 1 = (2 : ℕ) from rfl] at h
  have he : (fun z : ℂ => ∫ x : ℝ, (x : ℂ) * Complex.exp (z * x) ∂gaussianReal 0 1) =
      (fun z => z * Complex.exp (z ^ 2 / 2)) := funext standard_first_mgf
  rw [he] at h
  have hd : HasDerivAt (fun z : ℂ => z * Complex.exp (z ^ 2 / 2))
      ((1 + z ^ 2) * Complex.exp (z ^ 2 / 2)) z := by
    convert (hasDerivAt_id z).mul (((hasDerivAt_id z).pow 2).div_const 2).cexp using 1 <;>
      simp only [Pi.mul_def, Pi.pow_apply, id_eq] <;> ring
  exact h.unique hd

def scalarFourier (b x : ℝ) : ℂ := Complex.exp (Complex.I * (b * x : ℝ))

theorem integrable_scalar_fourier_pow (n : ℕ) (b : ℝ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * scalarFourier b x) (gaussianReal 0 1) := by
  simpa only [scalarFourier, Complex.ofReal_mul, mul_assoc] using
    integrable_standard_pow_exp n (Complex.I * b)

theorem scalar_fourier_integral (b : ℝ) :
    (∫ x, scalarFourier b x ∂gaussianReal 0 1) = Complex.exp (-(b ^ 2 : ℝ) / 2) := by
  have h := standard_mgf (Complex.I * b)
  have he : (Complex.I * (b : ℂ)) ^ 2 / 2 = -(b ^ 2 : ℝ) / 2 := by
    simp only [mul_pow, Complex.I_sq, Complex.ofReal_pow]
    ring
  simpa only [scalarFourier, Complex.ofReal_mul, mul_assoc, he] using h

theorem scalar_first_fourier_integral (b : ℝ) :
    (∫ x : ℝ, (x : ℂ) * scalarFourier b x ∂gaussianReal 0 1) =
      (Complex.I * b) * Complex.exp (-(b ^ 2 : ℝ) / 2) := by
  have h := standard_first_mgf (Complex.I * b)
  have he : (Complex.I * (b : ℂ)) ^ 2 / 2 = -(b ^ 2 : ℝ) / 2 := by
    simp only [mul_pow, Complex.I_sq, Complex.ofReal_pow]
    ring
  simpa only [scalarFourier, Complex.ofReal_mul, mul_assoc, he] using h

theorem scalar_second_fourier_integral (b : ℝ) :
    (∫ x : ℝ, (x : ℂ) ^ 2 * scalarFourier b x ∂gaussianReal 0 1) =
      (1 - (b ^ 2 : ℝ)) * Complex.exp (-(b ^ 2 : ℝ) / 2) := by
  have h := standard_second_mgf (Complex.I * b)
  have he : (Complex.I * (b : ℂ)) ^ 2 = -(b ^ 2 : ℝ) := by
    simp only [mul_pow, Complex.I_sq, Complex.ofReal_pow]
    ring
  simpa only [scalarFourier, Complex.ofReal_mul, mul_assoc, he, sub_eq_add_neg] using h

end

end TheoremA2.GaussianCovariance
