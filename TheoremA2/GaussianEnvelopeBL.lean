import TheoremA2.GaussianEnvelopeDifferential
import TheoremA2.GaussianEnvelopeBoxEuclidean
import TheoremA2.GaussianPolynomial
import TheoremA2.TiltedMGF

/-!
# Actual envelope covariance, MGF and fourth-moment estimates

All variance bounds are applications of the proved Brascamp–Lieb theorem
to the literal Gibbs potential. The box law uses concrete smooth penalties
and dominated limits. The MGF bounds integrate actual variances under every
linear tilt; the fourth moment applies Brascamp–Lieb again to the square of
the linear observable. No covariance or MGF estimate is assumed.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory Measure ProbabilityTheory GinibrePoincare
open TheoremA2.PrincipalInverse TheoremA2.CosineEnvelope TheoremA2.CramerRao
open TheoremA2.BrascampLieb
open scoped Topology RealInnerProductSpace Matrix MatrixOrder BigOperators ENNReal
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem envelope_linear_variance_le {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (h u : EuclideanSpace ℝ ι) :
    Var[fun x => ⟪u, x⟫; volume.tilted (fun x => -tiltedEnvelopePotential T h x)] ≤
      quadratic (envelopePrecision T κ)⁻¹ (WithLp.ofLp u) := by
  have hwi := integrable_tiltedEnvelope_weight hT h
  letI := isProbabilityMeasure_tilted hwi
  have hv := wholeSpace_variance_hessian_bound (tiltedEnvelopePotential T h)
    (fun x => ⟪u, x⟫) (EuclideanSpace.basisFun ι ℝ)
    (fun _ => envelopePrecision T κ) (tiltedEnvelopePotential_contDiff T h) hwi
    (fun _ => envelopePrecision_posDef hT hκ0)
    (envelope_hessian_difference_posSemidef hT hκ1 h) (innerSL ℝ u).contDiff
    (integrable_tiltedEnvelope_linear_sq hT h u)
    (by
      simp only [actualGradient_linear]
      exact hwi.const_mul _)
  simpa [actualGradient_linear, quadratic] using hv

theorem box_envelope_linear_variance_le {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {κ r : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hr : 0 < r)
    (h u : EuclideanSpace ℝ ι) :
    Var[fun x => ⟪u, x⟫;
      (volume.restrict (euclideanCoordinateBox r)).tilted
        (fun x => -tiltedEnvelopePotential T h x)] ≤
      quadratic (envelopePrecision T κ)⁻¹ (WithLp.ofLp u) := by
  have hwi := integrable_tiltedEnvelope_weight hT h
  rw [euclideanCoordinateBox_eq]
  have hs : 0 < volume (BrascampLieb.coordinateBox (EuclideanSpace.basisFun ι ℝ) r) :=
    (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ ι) hr).trans_le
      (measure_mono (ball_subset_coordinateBox (EuclideanSpace.basisFun ι ℝ)))
  letI : NeZero (volume.restrict (BrascampLieb.coordinateBox (EuclideanSpace.basisFun ι ℝ) r)) :=
    ⟨fun hz => (ne_of_gt hs) (Measure.restrict_eq_zero.mp hz)⟩
  letI : IsProbabilityMeasure
      ((volume.restrict (BrascampLieb.coordinateBox (EuclideanSpace.basisFun ι ℝ) r)).tilted
        (fun x => -tiltedEnvelopePotential T h x)) :=
    isProbabilityMeasure_tilted hwi.integrableOn
  have hv := box_variance_hessian_bound (tiltedEnvelopePotential T h)
    (fun x => ⟪u, x⟫) (EuclideanSpace.basisFun ι ℝ)
    (fun _ => envelopePrecision T κ) hr (tiltedEnvelopePotential_contDiff T h) hwi
    (fun _ => envelopePrecision_posDef hT hκ0)
    (envelope_hessian_difference_posSemidef hT hκ1 h) (innerSL ℝ u).contDiff
    (integrable_tiltedEnvelope_linear hT h u)
    (integrable_tiltedEnvelope_linear_sq hT h u)
    (by
      simp only [actualGradient_linear]
      exact hwi.const_mul _)
  simpa [actualGradient_linear, quadratic] using hv

theorem euclideanBoxEnvelopeLaw_tilted {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (r : ℝ) (h : EuclideanSpace ℝ ι) :
    (euclideanBoxEnvelopeLaw T r).tilted (fun x => ⟪h, x⟫) =
      (volume.restrict (euclideanCoordinateBox r)).tilted
        (fun x => -tiltedEnvelopePotential T h x) := by
  rw [euclideanBoxEnvelopeLaw_eq_volume_tilted hT]
  have hi : Integrable (fun x => Real.exp (-euclideanEnvelopePotential T x)) :=
    integrable_weight (euclideanEnvelopePotential_contDiff T).continuous
      (by norm_num : (0 : ℝ) < 1 / 2) (euclideanEnvelopePotential_quadratic_lower hT)
  rw [tilted_tilted hi.integrableOn]
  congr 1
  funext x
  simp only [Pi.add_apply, tiltedEnvelopePotential]
  ring

theorem euclidean_envelope_exp_integrable {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (u : EuclideanSpace ℝ ι) (t : ℝ) :
    Integrable (fun x => Real.exp (t * ⟪u, x⟫)) (euclideanEnvelopeLaw T) := by
  change Integrable _ ((envelopeLaw T).map (MeasurableEquiv.toLp 2 (ι → ℝ)))
  rw [integrable_map_equiv]
  change Integrable (fun x : ι → ℝ => Real.exp (t * ⟪u, WithLp.toLp 2 x⟫)) (envelopeLaw T)
  simp only [inner_toLp_right]
  convert integrable_envelopeLaw_exp_dot hT.posSemidef (fun i => t * u i) using 1
  funext x
  congr 1
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem euclidean_box_envelope_exp_integrable {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (r : ℝ) (u : EuclideanSpace ℝ ι) (t : ℝ) :
    Integrable (fun x => Real.exp (t * ⟪u, x⟫)) (euclideanBoxEnvelopeLaw T r) := by
  change Integrable _ ((boxEnvelopeLaw T r).map (MeasurableEquiv.toLp 2 (ι → ℝ)))
  rw [integrable_map_equiv]
  change Integrable (fun x : ι → ℝ => Real.exp (t * ⟪u, WithLp.toLp 2 x⟫)) (boxEnvelopeLaw T r)
  simp only [inner_toLp_right]
  convert integrable_boxEnvelopeLaw_exp_dot hT.posSemidef r (fun i => t * u i) using 1
  funext x
  congr 1
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem euclidean_envelope_mean_zero (T : Matrix ι ι ℝ) (u : EuclideanSpace ℝ ι) :
    (∫ x, ⟪u, x⟫ ∂euclideanEnvelopeLaw T) = 0 := by
  rw [integral_euclideanEnvelopeLaw]
  simp only [inner_toLp_right]
  exact integral_envelopeLaw_dot T (WithLp.ofLp u)

theorem euclidean_box_envelope_mean_zero (T : Matrix ι ι ℝ) (r : ℝ)
    (u : EuclideanSpace ℝ ι) :
    (∫ x, ⟪u, x⟫ ∂euclideanBoxEnvelopeLaw T r) = 0 := by
  rw [integral_euclideanBoxEnvelopeLaw]
  simp only [inner_toLp_right]
  exact integral_boxEnvelopeLaw_dot T r (WithLp.ofLp u)

theorem envelope_mgf_general {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (u : ι → ℝ) :
    (∫ x, Real.exp (u ⬝ᵥ x) ∂envelopeLaw T) ≤
      Real.exp (quadratic (envelopePrecision T κ)⁻¹ u / 2) := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 u
  have hv := TheoremA2.exp_integral_le_of_tilted_variance
    (X := fun x => ⟪v, x⟫) (μ := euclideanEnvelopeLaw T)
    (v := quadratic (envelopePrecision T κ)⁻¹ u)
    (euclidean_envelope_exp_integrable hT v) (euclidean_envelope_mean_zero T v)
    (fun t => by
      have he : (fun x : EuclideanSpace ℝ ι => t * ⟪v, x⟫) =
          (fun x => ⟪t • v, x⟫) := by funext x; simp only [real_inner_smul_left]
      rw [he, euclideanEnvelopeLaw_tilted hT]
      exact envelope_linear_variance_le hT hκ0 hκ1 (t • v) v)
  rw [integral_euclideanEnvelopeLaw] at hv
  simpa only [v, inner_toLp, WithLp.ofLp_toLp] using hv

theorem box_envelope_mgf_general {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {κ r : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hr : 0 < r) (u : ι → ℝ) :
    (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw T r) ≤
      Real.exp (quadratic (envelopePrecision T κ)⁻¹ u / 2) := by
  letI := euclideanBoxEnvelopeLaw_probability hT hr
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 u
  have hv := TheoremA2.exp_integral_le_of_tilted_variance
    (X := fun x => ⟪v, x⟫) (μ := euclideanBoxEnvelopeLaw T r)
    (v := quadratic (envelopePrecision T κ)⁻¹ u)
    (euclidean_box_envelope_exp_integrable hT r v) (euclidean_box_envelope_mean_zero T r v)
    (fun t => by
      have he : (fun x : EuclideanSpace ℝ ι => t * ⟪v, x⟫) =
          (fun x => ⟪t • v, x⟫) := by funext x; simp only [real_inner_smul_left]
      rw [he, euclideanBoxEnvelopeLaw_tilted hT]
      exact box_envelope_linear_variance_le hT hκ0 hκ1 hr (t • v) v)
  rw [integral_euclideanBoxEnvelopeLaw] at hv
  simpa only [v, inner_toLp, WithLp.ofLp_toLp] using hv

theorem envelopePrecision_zero_inv {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    (envelopePrecision T 0)⁻¹ = T := by
  simp only [envelopePrecision, Matrix.diagonal_zero, add_zero]
  exact Matrix.nonsing_inv_nonsing_inv T (T.isUnit_iff_isUnit_det.mp hT.isUnit)

/-- The whole-space envelope law has the original Gaussian covariance proxy. -/
theorem envelope_mgf_le_covariance {T : Matrix ι ι ℝ} (hT : T.PosDef) (u : ι → ℝ) :
    (∫ x, Real.exp (u ⬝ᵥ x) ∂envelopeLaw T) ≤ Real.exp (quadratic T u / 2) := by
  have h := envelope_mgf_general hT (κ := 0) (by norm_num) (by norm_num) u
  rwa [envelopePrecision_zero_inv hT] at h

/-- The stronger whole-space precision includes the genuine unit lower curvature. -/
theorem envelope_mgf {T : Matrix ι ι ℝ} (hT : T.PosDef) (u : ι → ℝ) :
    (∫ x, Real.exp (u ⬝ᵥ x) ∂envelopeLaw T) ≤
      Real.exp (quadratic (T⁻¹ + Matrix.diagonal (fun _ => (1 : ℝ)))⁻¹ u / 2) :=
  envelope_mgf_general hT (κ := 1) (by norm_num) (by norm_num) u

/-- Exact central-cell MGF proxy used in A.26. -/
theorem box_envelope_mgf {T : Matrix ι ι ℝ} (hT : T.PosDef) (u : ι → ℝ) :
    (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw T (Real.pi / 2)) ≤
      Real.exp (quadratic (T⁻¹ + Matrix.diagonal (fun _ => (3 / 4 : ℝ)))⁻¹ u / 2) :=
  box_envelope_mgf_general hT (κ := 3 / 4) (by norm_num) (by norm_num)
    (div_pos Real.pi_pos (by norm_num)) u

/-- The weaker central-box proxy required by the exact rank-one normalizer comparison. -/
theorem box_envelope_mgf_le_covariance {T : Matrix ι ι ℝ} (hT : T.PosDef) (u : ι → ℝ) :
    (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw T (Real.pi / 2)) ≤
      Real.exp (quadratic T u / 2) := by
  have h := box_envelope_mgf_general hT (κ := 0) (r := Real.pi / 2) (by norm_num) (by norm_num)
    (div_pos Real.pi_pos (by norm_num)) u
  rwa [envelopePrecision_zero_inv hT] at h

/-- Actual second moment, using the proved zero mean of the concrete law. -/
theorem envelope_second_moment_le_covariance {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (u : ι → ℝ) : (∫ x, (u ⬝ᵥ x) ^ 2 ∂envelopeLaw T) ≤ quadratic T u := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 u
  have hvar := envelope_linear_variance_le hT (κ := 0) (by norm_num) (by norm_num) 0 v
  rw [envelopePrecision_zero_inv hT] at hvar
  have hpot : (fun x => -tiltedEnvelopePotential T (0 : EuclideanSpace ℝ ι) x) =
      (fun x => -euclideanEnvelopePotential T x) := by
    funext x
    simp only [tiltedEnvelopePotential, inner_zero_left, sub_zero]
  rw [hpot, ← euclideanEnvelopeLaw_eq_volume_tilted hT] at hvar
  have hi : Integrable (fun x => ⟪v, x⟫ ^ 2) (euclideanEnvelopeLaw T) := by
    change Integrable _ ((envelopeLaw T).map (MeasurableEquiv.toLp 2 (ι → ℝ)))
    rw [integrable_map_equiv]
    simp only [Function.comp_apply, v, inner_toLp, WithLp.ofLp_toLp]
    exact integrable_envelopeLaw_dot_pow hT.posSemidef u 2
  have hLp : MemLp (fun x => ⟪v, x⟫) 2 (euclideanEnvelopeLaw T) :=
    (memLp_two_iff_integrable_sq (innerSL ℝ v).continuous.measurable.aestronglyMeasurable).mpr hi
  rw [variance_eq_sub hLp, euclidean_envelope_mean_zero T v, zero_pow (by norm_num : 2 ≠ 0),
    sub_zero, integral_euclideanEnvelopeLaw] at hvar
  simp only [Pi.pow_apply, v, WithLp.ofLp_toLp, inner_toLp] at hvar
  exact hvar


/-- Applying actual Brascamp–Lieb to the square of a linear observable gives
its fourth moment, with the exact constant used in A.27. -/
theorem envelope_fourth_moment_le {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (u : ι → ℝ) : (∫ x, (u ⬝ᵥ x) ^ 4 ∂envelopeLaw T) ≤ 5 * (quadratic T u) ^ 2 := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 u
  let W := tiltedEnvelopePotential T (0 : EuclideanSpace ℝ ι)
  let g : EuclideanSpace ℝ ι → ℝ := fun x => ⟪v, x⟫ ^ 2
  have hwi := integrable_tiltedEnvelope_weight hT (0 : EuclideanSpace ℝ ι)
  have hpot : (fun x => -W x) = (fun x => -euclideanEnvelopePotential T x) := by
    funext x
    simp only [W, tiltedEnvelopePotential, inner_zero_left, sub_zero]
  have hmu : volume.tilted (fun x => -W x) = euclideanEnvelopeLaw T := by
    rw [hpot, euclideanEnvelopeLaw_eq_volume_tilted hT]
  have hi4 : Integrable (fun x => ⟪v, x⟫ ^ 4) (euclideanEnvelopeLaw T) := by
    change Integrable _ ((envelopeLaw T).map (MeasurableEquiv.toLp 2 (ι → ℝ)))
    rw [integrable_map_equiv]
    simp only [Function.comp_apply, v, inner_toLp, WithLp.ofLp_toLp]
    exact integrable_envelopeLaw_dot_pow hT.posSemidef u 4
  have hpow (x : EuclideanSpace ℝ ι) : g x ^ 2 = ⟪v, x⟫ ^ 4 := by
    dsimp [g]
    ring
  have hg2 : Integrable (fun x => g x ^ 2 * bakryEmeryGibbsWeight W x) := by
    have hh : Integrable (fun x => ⟪v, x⟫ ^ 4) (volume.tilted (fun x => -W x)) := by
      rw [hmu]
      exact hi4
    have hh' := (integrable_tilted_iff hwi (fun x => ⟪v, x⟫ ^ 4)).mp hh
    simp only [smul_eq_mul] at hh'
    simp only [hpow, bakryEmeryGibbsWeight]
    convert hh' using 1
    funext x
    ring
  have henergy (x : EuclideanSpace ℝ ι) :
      correspondenceBrascampLiebGradient g (EuclideanSpace.basisFun ι ℝ) x ⬝ᵥ
        (envelopePrecision T 0)⁻¹ *ᵥ
          correspondenceBrascampLiebGradient g (EuclideanSpace.basisFun ι ℝ) x =
        (4 * quadratic T u) * ⟪v, x⟫ ^ 2 := by
    rw [show g = (fun y => ⟪v, y⟫ ^ 2) from rfl,
      actualGradient_linear_sq, envelopePrecision_zero_inv hT]
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      v, WithLp.ofLp_toLp, quadratic]
    ring
  have hR : Integrable (fun x =>
      (correspondenceBrascampLiebGradient g (EuclideanSpace.basisFun ι ℝ) x ⬝ᵥ
        (envelopePrecision T 0)⁻¹ *ᵥ
          correspondenceBrascampLiebGradient g (EuclideanSpace.basisFun ι ℝ) x) *
            bakryEmeryGibbsWeight W x) := by
    simp_rw [henergy]
    have hh := (integrable_tiltedEnvelope_linear_sq hT (0 : EuclideanSpace ℝ ι) v).const_mul
      (4 * quadratic T u)
    convert hh using 1
    funext x
    ring
  have hv := wholeSpace_variance_hessian_bound W g (EuclideanSpace.basisFun ι ℝ)
    (fun _ => envelopePrecision T 0) (tiltedEnvelopePotential_contDiff T 0) hwi
    (fun _ => envelopePrecision_posDef hT (by norm_num : (0 : ℝ) ≤ 0))
    (envelope_hessian_difference_posSemidef hT (by norm_num : (0 : ℝ) ≤ 1) 0)
    ((innerSL ℝ v).contDiff.pow 2) hg2 hR
  rw [hmu] at hv
  simp_rw [henergy] at hv
  rw [integral_const_mul] at hv
  have hgi : Integrable (fun x => g x ^ 2) (euclideanEnvelopeLaw T) := by
    simp only [hpow]
    exact hi4
  have hLp : MemLp g 2 (euclideanEnvelopeLaw T) :=
    (memLp_two_iff_integrable_sq
      ((innerSL ℝ v).continuous.pow 2).measurable.aestronglyMeasurable).mpr hgi
  rw [variance_eq_sub hLp] at hv
  change (∫ x, g x ^ 2 ∂euclideanEnvelopeLaw T) -
    (∫ x, g x ∂euclideanEnvelopeLaw T) ^ 2 ≤
      (4 * quadratic T u) * ∫ x, ⟪v, x⟫ ^ 2 ∂euclideanEnvelopeLaw T at hv
  simp_rw [hpow] at hv
  have hm : (∫ x, ⟪v, x⟫ ^ 2 ∂euclideanEnvelopeLaw T) ≤ quadratic T u := by
    rw [integral_euclideanEnvelopeLaw]
    simp only [v, inner_toLp, WithLp.ofLp_toLp]
    exact envelope_second_moment_le_covariance hT u
  have hm0 : 0 ≤ ∫ x, ⟪v, x⟫ ^ 2 ∂euclideanEnvelopeLaw T :=
    integral_nonneg (fun x => sq_nonneg _)
  have hs0 := quadratic_nonneg hT.posSemidef u
  have hfour : (∫ x, ⟪v, x⟫ ^ 4 ∂euclideanEnvelopeLaw T) ≤ 5 * (quadratic T u) ^ 2 := by
    change (∫ x, ⟪v, x⟫ ^ 4 ∂euclideanEnvelopeLaw T) -
      (∫ x, ⟪v, x⟫ ^ 2 ∂euclideanEnvelopeLaw T) ^ 2 ≤
        (4 * quadratic T u) * ∫ x, ⟪v, x⟫ ^ 2 ∂euclideanEnvelopeLaw T at hv
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hs0,
      sq_le_sq₀ hm0 hs0 |>.mpr hm]
  rw [integral_euclideanEnvelopeLaw] at hfour
  simpa only [v, inner_toLp, WithLp.ofLp_toLp] using hfour

end
end TheoremA2.GaussianCovariance
