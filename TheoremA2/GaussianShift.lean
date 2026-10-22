import TheoremA2.Imports
import Mathlib.Analysis.Convex.Integral

/-!
# Gaussian shifts and the variational estimate for lattice decoding

The law is the actual finite product of centered one-dimensional Gaussians.
No change-of-measure or entropy inequality is assumed.
-/

namespace TheoremA2.GaussianShift

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

noncomputable section

abbrev Vector (r : ℕ) := Fin r → ℝ

def variance (beta : ℝ) : ℝ≥0 := (1 / beta).toNNReal

def gaussian (r : ℕ) (beta : ℝ) : Measure (Vector r) :=
  Measure.pi fun _ : Fin r => gaussianReal 0 (variance beta)

instance (r : ℕ) (beta : ℝ) : IsProbabilityMeasure (gaussian r beta) := by
  unfold gaussian
  infer_instance

def density {r : ℕ} (beta : ℝ) (x : Vector r) : ℝ :=
  ∏ i, gaussianPDFReal 0 (variance beta) (x i)

theorem variance_coe {beta : ℝ} (hb : 0 < beta) :
    (variance beta : ℝ) = 1 / beta := Real.coe_toNNReal _ (by positivity)

theorem variance_pos {beta : ℝ} (hb : 0 < beta) : 0 < variance beta := by
  unfold variance
  exact Real.toNNReal_pos.2 (by positivity)

theorem density_nonneg {r : ℕ} (beta : ℝ) (x : Vector r) : 0 ≤ density beta x := by
  exact Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _

theorem density_pos {r : ℕ} {beta : ℝ} (hb : 0 < beta) (x : Vector r) :
    0 < density beta x := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos _ _ _ (ne_of_gt (variance_pos hb))

theorem measurable_density {r : ℕ} (beta : ℝ) : Measurable (@density r beta) := by
  unfold density
  fun_prop

theorem integrable_density {r : ℕ} (beta : ℝ) : Integrable (@density r beta) := by
  exact Integrable.fintype_prod fun _ => integrable_gaussianPDFReal _ _

theorem integral_density_rectangle {r : ℕ} (beta : ℝ) (s : Fin r → Set ℝ) :
    (∫ x in Set.univ.pi s, density beta x) =
      ∏ i, ∫ x in s i, gaussianPDFReal 0 (variance beta) x := by
  change (∫ x, density beta x ∂(Measure.pi fun _ : Fin r => volume).restrict
    (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod _

/-- The product law has its actual product Gaussian density with respect to volume. -/
theorem gaussian_eq_withDensity {r : ℕ} {beta : ℝ} (hb : 0 < beta) :
    gaussian r beta = volume.withDensity (fun x => ENNReal.ofReal (density beta x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply' _ _]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_density beta).integrableOn
    (Filter.Eventually.of_forall fun x => density_nonneg beta x)]
  rw [integral_density_rectangle]
  simp_rw [gaussianReal_apply_eq_integral _ (ne_of_gt (variance_pos hb))]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun x =>
    gaussianPDFReal_nonneg _ _ _)

theorem integral_gaussian_eq {r : ℕ} {beta : ℝ} (hb : 0 < beta)
    (f : Vector r → ℝ) :
    (∫ x, f x ∂gaussian r beta) = ∫ x, density beta x * f x := by
  rw [gaussian_eq_withDensity hb,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_density beta).ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (density_nonneg beta _), smul_eq_mul]

theorem integrable_gaussian_iff {r : ℕ} {beta : ℝ} (hb : 0 < beta)
    (f : Vector r → ℝ) :
    Integrable f (gaussian r beta) ↔ Integrable (fun x => density beta x * f x) := by
  rw [gaussian_eq_withDensity hb,
    integrable_withDensity_iff_integrable_smul'
      ((measurable_density beta).ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (density_nonneg beta _), smul_eq_mul]

def dot {r : ℕ} (z x : Vector r) : ℝ := ∑ i, z i * x i

def normSq {r : ℕ} (z : Vector r) : ℝ := ∑ i, z i ^ 2

def shiftExponent {r : ℕ} (beta : ℝ) (z x : Vector r) : ℝ :=
  -beta * dot z x - beta / 2 * normSq z

theorem scalar_density_shift {beta : ℝ} (hb : 0 < beta) (z x : ℝ) :
    gaussianPDFReal 0 (variance beta) (z + x) =
      gaussianPDFReal 0 (variance beta) x * Real.exp (-beta * z * x - beta / 2 * z ^ 2) := by
  unfold gaussianPDFReal
  rw [variance_coe hb]
  simp only [sub_zero]
  have he : -(z + x) ^ 2 / (2 * (1 / beta)) =
      -x ^ 2 / (2 * (1 / beta)) + (-beta * z * x - beta / 2 * z ^ 2) := by
    field_simp
    ring
  rw [he, Real.exp_add]
  ring

theorem density_shift {r : ℕ} {beta : ℝ} (hb : 0 < beta) (z x : Vector r) :
    density beta (z + x) = density beta x * Real.exp (shiftExponent beta z x) := by
  unfold density
  simp only [Pi.add_apply, scalar_density_shift hb, Finset.prod_mul_distrib]
  rw [← Real.exp_sum]
  congr 2
  unfold shiftExponent dot normSq
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · rfl

/-- The exact Gaussian translation identity, with no integrability convention used for a bound. -/
theorem integral_shift {r : ℕ} {beta : ℝ} (hb : 0 < beta)
    (z : Vector r) (f : Vector r → ℝ) :
    (∫ x, f (z + x) * Real.exp (shiftExponent beta z x) ∂gaussian r beta) =
      ∫ x, f x ∂gaussian r beta := by
  rw [integral_gaussian_eq hb, integral_gaussian_eq hb]
  calc
    (∫ x, density beta x * (f (z + x) * Real.exp (shiftExponent beta z x))) =
        ∫ x, density beta (z + x) * f (z + x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [density_shift hb]
      ring
    _ = _ := integral_add_left_eq_self
      (fun x : Vector r => density beta x * f x) z

theorem integrable_shift {r : ℕ} {beta : ℝ} (hb : 0 < beta)
    (z : Vector r) {f : Vector r → ℝ} (hf : Integrable f (gaussian r beta)) :
    Integrable (fun x => f (z + x) * Real.exp (shiftExponent beta z x)) (gaussian r beta) := by
  rw [integrable_gaussian_iff hb] at hf ⊢
  convert hf.comp_add_left z using 1
  funext x
  rw [density_shift hb]
  ring

theorem integrable_coordinate {r : ℕ} (beta : ℝ) (i : Fin r) :
    Integrable (fun x : Vector r => x i) (gaussian r beta) := by
  exact integrable_comp_eval (μ := fun _ : Fin r => gaussianReal 0 (variance beta)) (i := i)
    (show Integrable (fun x : ℝ => x) (gaussianReal 0 (variance beta)) from
      memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))

theorem integral_coordinate {r : ℕ} (beta : ℝ) (i : Fin r) :
    (∫ x : Vector r, x i ∂gaussian r beta) = 0 := by
  unfold gaussian
  rw [integral_comp_eval (μ := fun _ : Fin r => gaussianReal 0 (variance beta)) (i := i)
    (show AEStronglyMeasurable (fun x : ℝ => x)
    (gaussianReal 0 (variance beta)) by fun_prop)]
  exact integral_id_gaussianReal

theorem integrable_dot {r : ℕ} (beta : ℝ) (z : Vector r) :
    Integrable (dot z) (gaussian r beta) := by
  exact integrable_finset_sum _ fun i _ => (integrable_coordinate beta i).const_mul (z i)

theorem integral_dot {r : ℕ} (beta : ℝ) (z : Vector r) :
    (∫ x, dot z x ∂gaussian r beta) = 0 := by
  unfold dot
  rw [integral_finset_sum _ (fun i _ => (integrable_coordinate beta i).const_mul (z i))]
  simp_rw [integral_const_mul, integral_coordinate, mul_zero]
  simp

theorem integrable_shiftExponent {r : ℕ} (beta : ℝ) (z : Vector r) :
    Integrable (shiftExponent beta z) (gaussian r beta) :=
  ((integrable_dot beta z).const_mul (-beta)).sub (integrable_const _)

theorem integral_shiftExponent {r : ℕ} (beta : ℝ) (z : Vector r) :
    (∫ x, shiftExponent beta z x ∂gaussian r beta) = -beta / 2 * normSq z := by
  unfold shiftExponent
  rw [integral_sub ((integrable_dot beta z).const_mul (-beta)) (integrable_const _),
    integral_const_mul, integral_dot, integral_const]
  simp
  ring

/-- Gaussian shift followed by Jensen's inequality. This proves the variational
bound for the actual probability law and the actual decoder likelihood. -/
theorem variational_bound {r : ℕ} {beta : ℝ} (hb : 0 < beta)
    (z : Vector r) {Q : Vector r → ℝ} (hQm : Measurable Q)
    (hQpos : ∀ x, 0 < Q x) (hQone : ∀ x, Q x ≤ 1)
    (hlog : Integrable (fun x => Real.log (Q (z + x))) (gaussian r beta))
    {C : ℝ} (hC : -(∫ x, Real.log (Q (z + x)) ∂gaussian r beta) ≤ C) :
    Real.exp (-beta / 2 * normSq z - C) ≤ ∫ x, Q x ∂gaussian r beta := by
  have hQi : Integrable Q (gaussian r beta) :=
    (integrable_const (1 : ℝ)).mono' hQm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (hQpos x)]
        exact hQone x)
  let X : Vector r → ℝ := fun x => Real.log (Q (z + x)) + shiftExponent beta z x
  have hXi : Integrable X (gaussian r beta) := hlog.add (integrable_shiftExponent beta z)
  have hExp (x : Vector r) : Real.exp (X x) =
      Q (z + x) * Real.exp (shiftExponent beta z x) := by
    change Real.exp (Real.log (Q (z + x)) + shiftExponent beta z x) = _
    rw [Real.exp_add, Real.exp_log (hQpos _)]
  have hExpi : Integrable (fun x => Real.exp (X x)) (gaussian r beta) := by
    simpa only [hExp] using integrable_shift hb z hQi
  have hj : Real.exp (∫ x, X x ∂gaussian r beta) ≤
      ∫ x, Real.exp (X x) ∂gaussian r beta :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
      isClosed_univ (by simp) hXi hExpi
  have hi : (∫ x, X x ∂gaussian r beta) =
      (∫ x, Real.log (Q (z + x)) ∂gaussian r beta) - beta / 2 * normSq z := by
    rw [show X = fun x => Real.log (Q (z + x)) + shiftExponent beta z x from rfl,
      integral_add hlog (integrable_shiftExponent beta z), integral_shiftExponent]
    ring
  calc
    Real.exp (-beta / 2 * normSq z - C) ≤ Real.exp (∫ x, X x ∂gaussian r beta) := by
      apply Real.exp_le_exp.2
      rw [hi]
      linarith
    _ ≤ ∫ x, Real.exp (X x) ∂gaussian r beta := hj
    _ = ∫ x, Q x ∂gaussian r beta := by
      simp_rw [hExp]
      exact integral_shift hb z Q

def projection {r : ℕ} (b : Vector r) : Vector r →L[ℝ] ℝ :=
  ∑ i, b i • ContinuousLinearMap.proj i

@[simp] theorem projection_apply {r : ℕ} (b x : Vector r) :
    projection b x = dot b x := by
  simp [projection, dot]

@[simp] theorem projection_single {r : ℕ} (b : Vector r) (i : Fin r) (x : ℝ) :
    projection b (Pi.single i x) = b i * x := by
  simp [projection, dot, Pi.single_apply]

theorem normSq_nonneg {r : ℕ} (z : Vector r) : 0 ≤ normSq z := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- An arbitrary linear projection of the actual product law has its exact
one-dimensional Gaussian distribution, including degenerate projections. -/
theorem map_dot {r : ℕ} {beta : ℝ} (hb : 0 < beta) (b : Vector r) :
    (gaussian r beta).map (dot b) =
      gaussianReal 0 ((normSq b / beta).toNNReal) := by
  rw [show dot b = ⇑(projection b) by funext x; exact (projection_apply b x).symm]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_eq_charFunDual_smul, gaussian, charFunDual_pi]
  simp_rw [charFunDual_eq_charFun_map_one, gaussianReal_map_continuousLinearMap,
    charFun_gaussianReal]
  simp only [map_zero, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero,
    one_pow, mul_one, zero_sub, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.single_apply,
    projection_single, smul_eq_mul, NNReal.coe_mul,
    Real.coe_toNNReal _ (sq_nonneg _), variance_coe hb]
  rw [← Complex.exp_sum]
  congr 1
  rw [Real.coe_toNNReal _ (div_nonneg (normSq_nonneg b) hb.le)]
  simp only [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_pow,
    Complex.ofReal_mul, normSq, Finset.sum_div]
  simp only [Complex.ofReal_one, Finset.sum_neg_distrib, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end TheoremA2.GaussianShift
