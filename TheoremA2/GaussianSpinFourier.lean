import TheoremA2.GaussianFourierQuadratic
import TheoremA2.SpinCovarianceConditional
import TheoremA2.SpinCovarianceMoments
import TheoremA2.Characteristic

/-!
# Exact Gaussian Fourier transfer to the spin covariance

The cosine normalizer is the literal uniform average of positive spin weights.
The signed Gaussian second moment is computed from the actual Gaussian Fourier
moments. No positivity of the cosine density is asserted or needed.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse TheoremA2.SpinCovariance TheoremA2.ConvexSupport
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexAverage_prod_fintype (f : ι → Bool → ℂ) :
    complexAverage (fun σ : SpinConfig ι => ∏ i, f i (σ i)) =
      ∏ i, (f i false + f i true) / 2 := by
  unfold complexAverage
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp [div_eq_mul_inv, mul_comm, add_comm]

theorem spin_fourier_eq_cosine_product (x : ι → ℝ) :
    complexAverage (fun σ : SpinConfig ι => fourier (spinVector σ) x) =
      ((∏ i, Real.cos (x i) : ℝ) : ℂ) := by
  simp_rw [fourier_eq_prod, spinVector]
  rw [complexAverage_prod_fintype (fun i b => scalarFourier (sign b) (x i))]
  simp only [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  have hs (b : Bool) : scalarFourier (spinVector (fun _ : ι => b) i) (x i) =
      Complex.exp (((x i * sign b : ℝ) : ℂ) * Complex.I) := by
    unfold scalarFourier spinVector
    congr 1
    push_cast
    ring
  change (scalarFourier (sign false) (x i) + scalarFourier (sign true) (x i)) / 2 = _
  rw [show scalarFourier (sign false) (x i) = _ from hs false,
    show scalarFourier (sign true) (x i) = _ from hs true]
  exact sign_exponential_average _

theorem norm_fourier (b x : ι → ℝ) : ‖fourier b x‖ = 1 := by
  simp [fourier, Complex.norm_exp, Complex.mul_re]

theorem integrable_covariance_fourier (T : Matrix ι ι ℝ) (b : ι → ℝ) :
    Integrable (fourier b) (covarianceGaussian T) := by
  apply (integrable_const (1 : ℝ)).mono'
    (by unfold fourier; fun_prop)
  exact Filter.Eventually.of_forall (fun x => le_of_eq (norm_fourier b x))

theorem integrable_covariance_dot_sq_fourier {T : Matrix ι ι ℝ}
    (hT : T.PosSemidef) (v b : ι → ℝ) :
    Integrable (fun x => ((v ⬝ᵥ x : ℝ) : ℂ) ^ 2 * fourier b x)
      (covarianceGaussian T) := by
  apply (integrable_dot_sq hT v).mono'
    (by unfold fourier dotProduct; fun_prop)
  filter_upwards [] with x
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    norm_fourier, mul_one, sq_abs]
  exact le_rfl

theorem integral_complexAverage {α Ω : Type*} [Fintype α]
    [MeasurableSpace Ω] (μ : Measure Ω) (f : α → Ω → ℂ)
    (hf : ∀ a, Integrable (f a) μ) :
    (∫ x, complexAverage (fun a => f a x) ∂μ) =
      complexAverage (fun a => ∫ x, f a x ∂μ) := by
  unfold complexAverage
  rw [integral_const_mul, integral_finsetSum _ (fun a _ => hf a)]

def spinGaussianNormalizer (T : Matrix ι ι ℝ) : ℝ :=
  average (fun σ : SpinConfig ι => Real.exp (-quadratic T (spinVector σ) / 2))

theorem spinGaussianNormalizer_eq (T : Matrix ι ι ℝ) :
    spinGaussianNormalizer T =
      (Fintype.card (SpinConfig ι) : ℝ)⁻¹ * spinPartition T 0 := by
  simp only [spinGaussianNormalizer, average, spinPartition, spinWeight,
    zero_dotProduct, zero_sub, neg_div]

theorem spinGaussianNormalizer_pos (T : Matrix ι ι ℝ) :
    0 < spinGaussianNormalizer T := by
  rw [spinGaussianNormalizer_eq]
  exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)) (spinPartition_pos T 0)

theorem uniform_weighted_spin_identity (T : Matrix ι ι ℝ) (f : SpinConfig ι → ℝ) :
    average (fun σ => Real.exp (-quadratic T (spinVector σ) / 2) * f σ) =
      spinGaussianNormalizer T * (spinLaw T 0).expectation f := by
  rw [spinGaussianNormalizer_eq, spinLaw_expectation]
  unfold average
  simp only [spinWeight, zero_dotProduct, zero_sub, neg_div]
  field_simp [ne_of_gt (spinPartition_pos T 0)]

theorem covariance_fourier_integral {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (b : ι → ℝ) :
    (∫ x, fourier b x ∂covarianceGaussian T) =
      (Real.exp (-quadratic T b / 2) : ℂ) := by
  change (∫ x, Complex.exp (Complex.I * (b ⬝ᵥ x : ℝ)) ∂covarianceGaussian T) = _
  rw [integral_fourier_dot hT, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The cosine integral is positive because it equals an actual spin partition sum. -/
theorem integral_cosine_product {T : Matrix ι ι ℝ} (hT : T.PosSemidef) :
    (∫ x, ∏ i, Real.cos (x i) ∂covarianceGaussian T) = spinGaussianNormalizer T := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [← spin_fourier_eq_cosine_product]
  rw [integral_complexAverage _ _ (fun σ => integrable_covariance_fourier T (spinVector σ))]
  simp_rw [covariance_fourier_integral hT]
  exact complexAverage_ofReal _

theorem integral_cosine_product_pos {T : Matrix ι ι ℝ} (hT : T.PosSemidef) :
    0 < ∫ x, ∏ i, Real.cos (x i) ∂covarianceGaussian T := by
  rw [integral_cosine_product hT]
  exact spinGaussianNormalizer_pos T

theorem quadratic_cosine_eq_average (v x : ι → ℝ) :
    (((v ⬝ᵥ x) ^ 2 * ∏ i, Real.cos (x i) : ℝ) : ℂ) =
      complexAverage (fun σ : SpinConfig ι =>
        ((v ⬝ᵥ x : ℝ) : ℂ) ^ 2 * fourier (spinVector σ) x) := by
  rw [Complex.ofReal_mul, Complex.ofReal_pow, ← spin_fourier_eq_cosine_product]
  simp only [complexAverage, Finset.mul_sum]
  ring

theorem integral_quadratic_cosine_product {T : Matrix ι ι ℝ}
    (hT : T.PosSemidef) (v : ι → ℝ) :
    (∫ x, (v ⬝ᵥ x) ^ 2 * ∏ i, Real.cos (x i) ∂covarianceGaussian T) =
      spinGaussianNormalizer T *
        (quadratic T v - (spinLaw T 0).expectation
          (fun σ => (v ⬝ᵥ (T *ᵥ spinVector σ)) ^ 2)) := by
  have he (σ : SpinConfig ι) :
      (∫ x, ((v ⬝ᵥ x : ℝ) : ℂ) ^ 2 * fourier (spinVector σ) x
        ∂covarianceGaussian T) =
      ((Real.exp (-quadratic T (spinVector σ) / 2) *
        (quadratic T v - (v ⬝ᵥ (T *ᵥ spinVector σ)) ^ 2) : ℝ) : ℂ) := by
    have hex : Complex.exp (-(quadratic T (spinVector σ) : ℝ) / 2) =
        (Real.exp (-quadratic T (spinVector σ) / 2) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [covariance_dot_sq_fourier hT, hex, Complex.ofReal_mul, mul_comm]
  have hr : average (fun σ : SpinConfig ι =>
      Real.exp (-quadratic T (spinVector σ) / 2) *
        (quadratic T v - (v ⬝ᵥ (T *ᵥ spinVector σ)) ^ 2)) =
      spinGaussianNormalizer T *
        (quadratic T v - (spinLaw T 0).expectation
          (fun σ => (v ⬝ᵥ (T *ᵥ spinVector σ)) ^ 2)) := by
    rw [uniform_weighted_spin_identity]
    simp only [expectation_sub, expectation_const]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [quadratic_cosine_eq_average]
  rw [integral_complexAverage _ _
    (fun σ => integrable_covariance_dot_sq_fourier hT v (spinVector σ))]
  simp_rw [he]
  rw [complexAverage_ofReal, hr]

/-- The signed Gaussian second moment is an actual ratio of integrals. -/
def signedSecondMoment (T : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  (∫ x, (v ⬝ᵥ x) ^ 2 * ∏ i, Real.cos (x i) ∂covarianceGaussian T) /
    spinGaussianNormalizer T

/-- The exact covariance transfer used by A.28. -/
theorem signedSecondMoment_eq {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (v : ι → ℝ) :
    signedSecondMoment T v = quadratic T v -
      quadratic (covariance (spinLaw T 0) spinVector) (T *ᵥ v) := by
  rw [signedSecondMoment, integral_quadratic_cosine_product hT,
    mul_div_cancel_left₀ _ (ne_of_gt (spinGaussianNormalizer_pos T)),
    zero_field_quadratic_covariance]
  congr 1
  apply expectation_congr
  intro σ
  rw [symmetric_bilinear hT.isHermitian, dotProduct_comm]

end

end TheoremA2.GaussianCovariance
