import TheoremA2.GaussianEnvelopeLaw

/-!
# Identification with the actual Euclidean Gibbs measure

The Gaussian-envelope law is identified with normalized Lebesgue density
`exp (-(xᵀT⁻¹x/2 + ∑ f(xᵢ)))`. The determinant factor cancels through its
proved normalizing integral, and the coordinate-to-Euclidean map preserves
actual volume.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrable_covarianceDensity {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    Integrable (covarianceDensity T) := by
  simpa using (integrable_covarianceGaussian_iff hT (fun _ => (1 : ℝ))).mp (integrable_const 1)

theorem integral_covarianceDensity {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    (∫ x, covarianceDensity T x) = 1 := by
  have hh := integral_covarianceGaussian_eq hT (fun _ => (1 : ℝ))
  simpa using hh.symm

theorem integrable_exp_precision {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    Integrable (fun x => Real.exp (-quadratic T⁻¹ x / 2)) := by
  have hc := covarianceDensity_pos hT (0 : ι → ℝ)
  have he : (fun x => Real.exp (-quadratic T⁻¹ x / 2)) =
      (fun x => (covarianceDensity T 0)⁻¹ * covarianceDensity T x) := by
    funext x
    rw [covarianceDensity_eq_exp hT x]
    field_simp
  rw [he]
  exact (integrable_covarianceDensity hT).const_mul _

theorem integral_exp_precision {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    (∫ x, Real.exp (-quadratic T⁻¹ x / 2)) = (covarianceDensity T 0)⁻¹ := by
  have he (x : ι → ℝ) : Real.exp (-quadratic T⁻¹ x / 2) =
      (covarianceDensity T 0)⁻¹ * covarianceDensity T x := by
    rw [covarianceDensity_eq_exp hT x]
    have hc := ne_of_gt (covarianceDensity_pos hT (0 : ι → ℝ))
    field_simp
  simp_rw [he]
  rw [integral_const_mul, integral_covarianceDensity hT, mul_one]

/-- The same actual Gaussian is its normalized precision-density Gibbs measure. -/
theorem covarianceGaussian_eq_volume_tilted {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    covarianceGaussian T = volume.tilted (fun x => -quadratic T⁻¹ x / 2) := by
  rw [covarianceGaussian_eq_withDensity hT, Measure.tilted, integral_exp_precision hT]
  congr 1
  funext x
  rw [covarianceDensity_eq_exp hT x]
  congr 1
  rw [div_inv_eq_mul, mul_comm]

/-- Exact transport of a normalized exponential tilt by a measurable equivalence. -/
theorem tilted_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (f : α → ℝ) :
    (μ.tilted f).map e = (μ.map e).tilted (fun y => f (e.symm y)) := by
  have hi : (∫ y, Real.exp (f (e.symm y)) ∂μ.map e) = ∫ x, Real.exp (f x) ∂μ := by
    rw [integral_map_equiv]
    simp only [e.symm_apply_apply]
  rw [Measure.tilted, map_withDensity_equiv, Measure.tilted, hi]

/-- The potential is the literal quadratic precision plus the actual scalar envelope. -/
def fullEnvelopePotential (T : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  quadratic T⁻¹ x / 2 + envelopePotential x

theorem envelopeLaw_eq_volume_tilted {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    envelopeLaw T = volume.tilted (fun x => -fullEnvelopePotential T x) := by
  rw [envelopeLaw, covarianceGaussian_eq_volume_tilted hT,
    tilted_tilted (integrable_exp_precision hT)]
  congr 1
  funext x
  simp only [Pi.add_apply, fullEnvelopePotential]
  ring

def euclideanEnvelopePotential (T : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  fullEnvelopePotential T (WithLp.ofLp x)

def euclideanEnvelopeLaw (T : Matrix ι ι ℝ) : Measure (EuclideanSpace ℝ ι) :=
  (envelopeLaw T).map (WithLp.toLp 2)

instance euclideanEnvelopeLaw_probability (T : Matrix ι ι ℝ) :
    IsProbabilityMeasure (euclideanEnvelopeLaw T) := by
  unfold euclideanEnvelopeLaw
  infer_instance

/-- The exact Euclidean law to which whole-space Brascamp–Lieb and
Cramér–Rao apply. No equality of densities or normalizers is assumed. -/
theorem euclideanEnvelopeLaw_eq_volume_tilted {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    euclideanEnvelopeLaw T =
      volume.tilted (fun x => -euclideanEnvelopePotential T x) := by
  unfold euclideanEnvelopeLaw
  rw [envelopeLaw_eq_volume_tilted hT]
  change (volume.tilted (fun x => -fullEnvelopePotential T x)).map
    (MeasurableEquiv.toLp 2 (ι → ℝ)) = _
  rw [tilted_map_equiv]
  have hv : (volume : Measure (ι → ℝ)).map (MeasurableEquiv.toLp 2 (ι → ℝ)) = volume :=
    (PiLp.volume_preserving_toLp ι).map_eq
  rw [hv]
  rfl

theorem integral_euclideanEnvelopeLaw (T : Matrix ι ι ℝ)
    (f : EuclideanSpace ℝ ι → ℝ) :
    (∫ x, f x ∂euclideanEnvelopeLaw T) = ∫ x, f (WithLp.toLp 2 x) ∂envelopeLaw T :=
  integral_map_equiv (MeasurableEquiv.toLp 2 (ι → ℝ)) f

end

end TheoremA2.GaussianCovariance
