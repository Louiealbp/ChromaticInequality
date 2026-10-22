import TheoremA2.CramerRaoCore
import TheoremA2.GaussianEnvelopeEuclidean

/-!
# The actual Cramér–Rao bound for the cosine-envelope Gibbs law

The potential, law, derivatives and normalizer are the concrete ones used
in the paper. The score grows at most linearly by the proved derivative
bound for the clamped-curvature envelope. Integration by parts is supplied
by `CramerRaoCore`, with its analytic hypotheses derived here.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory TheoremA2.PrincipalInverse TheoremA2.CosineEnvelope
open TheoremA2.CramerRao
open scoped Topology RealInnerProductSpace Matrix MatrixOrder BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev precisionMap (T : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) T⁻¹

theorem inner_precision_eq (T : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪x, precisionMap T x⟫ = quadratic T⁻¹ (WithLp.ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  simp only [Pi.star_apply, star_trivial, quadratic]
  exact dotProduct_comm _ _

theorem euclideanEnvelopePotential_eq (T : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    euclideanEnvelopePotential T x =
      ⟪x, precisionMap T x⟫ / 2 + ∑ i, envelope (x i) := by
  rw [inner_precision_eq]
  rfl

theorem euclideanEnvelopePotential_contDiff (T : Matrix ι ι ℝ) :
    ContDiff ℝ 2 (euclideanEnvelopePotential T) := by
  change ContDiff ℝ 2 (fun x => euclideanEnvelopePotential T x)
  simp_rw [euclideanEnvelopePotential_eq]
  apply ContDiff.add
  · exact (contDiff_id.inner ℝ (precisionMap T).contDiff).div_const 2
  · exact ContDiff.sum fun i _ => envelope_contDiff.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).contDiff

theorem fderiv_euclideanEnvelopePotential (T : Matrix ι ι ℝ)
    (x v : EuclideanSpace ℝ ι) :
    fderiv ℝ (euclideanEnvelopePotential T) x v =
      (⟪precisionMap T v, x⟫ + ⟪v, precisionMap T x⟫) / 2 +
        ∑ i, deriv envelope (x i) * v i := by
  let Q := precisionMap T
  have hq := ((hasFDerivAt_id x).inner ℝ Q.hasFDerivAt).const_mul (1 / 2 : ℝ)
  have he : HasFDerivAt (fun y : EuclideanSpace ℝ ι => ∑ i, envelope (y i))
      (∑ i, deriv envelope (x i) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact ((envelope_contDiff.differentiable (by norm_num) (x i)).hasDerivAt).comp_hasFDerivAt x
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).hasFDerivAt
  have hd := hq.add he
  change HasFDerivAt (fun y : EuclideanSpace ℝ ι => (1 / 2 : ℝ) * ⟪y, Q y⟫ +
    ∑ i, envelope (y i)) _ x at hd
  have hfun : (fun y : EuclideanSpace ℝ ι => (1 / 2 : ℝ) * ⟪y, Q y⟫ +
      ∑ i, envelope (y i)) = euclideanEnvelopePotential T := by
    funext y
    rw [euclideanEnvelopePotential_eq]
    dsimp [Q]
    ring
  rw [hfun] at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderivInnerCLM_apply, smul_eq_mul,
    ContinuousLinearMap.sum_apply, PiLp.proj_apply]
  rw [real_inner_comm x (Q v)]
  dsimp [Q]
  ring

theorem second_mixed_euclideanEnvelopePotential (T : Matrix ι ι ℝ)
    (x v w : EuclideanSpace ℝ ι) :
    fderiv ℝ (score (euclideanEnvelopePotential T) v) x w =
      (⟪precisionMap T v, w⟫ + ⟪v, precisionMap T w⟫) / 2 +
        ∑ i, deriv (deriv envelope) (x i) * v i * w i := by
  have he : score (euclideanEnvelopePotential T) v =
      fun y => (⟪precisionMap T v, y⟫ + ⟪v, precisionMap T y⟫) / 2 +
        ∑ i, deriv envelope (y i) * v i := by
    funext y
    exact fderiv_euclideanEnvelopePotential T y v
  rw [he]
  have hq := (((innerSL ℝ (precisionMap T v)).hasFDerivAt (x := x)).add
    (((innerSL ℝ v).comp (precisionMap T)).hasFDerivAt (x := x))).const_mul (1 / 2 : ℝ)
  have hf' : Differentiable ℝ (deriv envelope) :=
    envelope_contDiff.differentiable_deriv_two
  have hs := HasFDerivAt.fun_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    ((hf' (x i)).hasDerivAt.comp_hasFDerivAt x
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).hasFDerivAt).mul_const (v i)
  have hd := hq.add hs
  change HasFDerivAt (fun y : EuclideanSpace ℝ ι =>
    (1 / 2 : ℝ) * (⟪precisionMap T v, y⟫ + ⟪v, precisionMap T y⟫) +
      ∑ i, deriv envelope (y i) * v i) _ x at hd
  have hfun : (fun y : EuclideanSpace ℝ ι =>
      (1 / 2 : ℝ) * (⟪precisionMap T v, y⟫ + ⟪v, precisionMap T y⟫) +
        ∑ i, deriv envelope (y i) * v i) =
      (fun y => (⟪precisionMap T v, y⟫ + ⟪v, precisionMap T y⟫) / 2 +
        ∑ i, deriv envelope (y i) * v i) := by funext y; ring
  rw [hfun] at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, smul_eq_mul,
    PiLp.proj_apply, innerSL_apply_apply]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem second_direction_euclideanEnvelopePotential (T : Matrix ι ι ℝ)
    (x v : EuclideanSpace ℝ ι) :
    fderiv ℝ (score (euclideanEnvelopePotential T) v) x v =
      quadratic T⁻¹ (WithLp.ofLp v) + ∑ i, deriv (deriv envelope) (x i) * (v i) ^ 2 := by
  rw [second_mixed_euclideanEnvelopePotential, real_inner_comm v (precisionMap T v)]
  have heq : (⟪v, precisionMap T v⟫ + ⟪v, precisionMap T v⟫) / 2 =
      ⟪v, precisionMap T v⟫ := by ring
  rw [heq, inner_precision_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem euclideanEnvelopePotential_quadratic_lower {T : Matrix ι ι ℝ}
    (hT : T.PosDef) (x : EuclideanSpace ℝ ι) :
    (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ euclideanEnvelopePotential T x := by
  have hq := quadratic_nonneg hT.posSemidef.inv (WithLp.ofLp x)
  have hs := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    envelope_quadratic_lower (x i)
  rw [← Finset.sum_div] at hs
  rw [euclideanEnvelopePotential_eq, inner_precision_eq]
  have hn : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [hn]
  linarith

def envelopePrecisionUpper (T : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  T⁻¹ + Matrix.diagonal (fun _ => upperCurvature)

theorem envelopePrecisionUpper_posDef {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    (envelopePrecisionUpper T).PosDef := by
  exact hT.inv.add_posSemidef (Matrix.PosSemidef.diagonal (fun _ => upperCurvature_pos.le))

theorem envelopePrecisionUpper_quadratic (T : Matrix ι ι ℝ) (v : ι → ℝ) :
    quadratic (envelopePrecisionUpper T) v =
      quadratic T⁻¹ v + upperCurvature * ∑ i, (v i) ^ 2 := by
  simp only [envelopePrecisionUpper, quadratic, Matrix.add_mulVec, dotProduct_add,
    Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum, Pi.add_apply,
    mul_add, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem envelope_second_direction_bounds {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (v x : EuclideanSpace ℝ ι) :
    0 ≤ fderiv ℝ (score (euclideanEnvelopePotential T) v) x v ∧
      fderiv ℝ (score (euclideanEnvelopePotential T) v) x v ≤
        quadratic (envelopePrecisionUpper T) (WithLp.ofLp v) := by
  rw [second_direction_euclideanEnvelopePotential, envelopePrecisionUpper_quadratic]
  constructor
  · apply add_nonneg (quadratic_nonneg hT.posSemidef.inv _)
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (by linarith [envelope_curvature_lower (x i)]) (sq_nonneg _)
  · apply add_le_add le_rfl
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (envelope_curvature_upper (x i)) (sq_nonneg _)

def envelopeScoreBound (T : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  (‖precisionMap T v‖ + ‖v‖ * ‖precisionMap T‖) / 2 + upperCurvature * ∑ i, |v i|

theorem envelopeScoreBound_nonneg (T : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    0 ≤ envelopeScoreBound T v := by
  unfold envelopeScoreBound
  exact add_nonneg (div_nonneg
    (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (by norm_num))
    (mul_nonneg upperCurvature_pos.le (Finset.sum_nonneg (fun i _ => abs_nonneg (v i))))

theorem envelope_score_linear_growth (T : Matrix ι ι ℝ) (v x : EuclideanSpace ℝ ι) :
    |score (euclideanEnvelopePotential T) v x| ≤ envelopeScoreBound T v * ‖x‖ := by
  rw [score, fderiv_euclideanEnvelopePotential]
  have hq₁ := abs_real_inner_le_norm (precisionMap T v) x
  have hq₂ : |⟪v, precisionMap T x⟫| ≤ (‖v‖ * ‖precisionMap T‖) * ‖x‖ := by
    exact (abs_real_inner_le_norm v (precisionMap T x)).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        ((precisionMap T).le_opNorm x) (norm_nonneg v))
  have hs : |∑ i, deriv envelope (x i) * v i| ≤
      (upperCurvature * ∑ i, |v i|) * ‖x‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    have hx : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    have hd : |deriv envelope (x i)| ≤ upperCurvature * ‖x‖ :=
      (abs_deriv_envelope_le (x i)).trans (mul_le_mul_of_nonneg_left hx upperCurvature_pos.le)
    have h := mul_le_mul_of_nonneg_right hd (abs_nonneg (v i))
    nlinarith
  apply (abs_add_le _ _).trans
  have hq : |(⟪precisionMap T v, x⟫ + ⟪v, precisionMap T x⟫) / 2| ≤
      ((‖precisionMap T v‖ + ‖v‖ * ‖precisionMap T‖) / 2) * ‖x‖ := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := (abs_add_le _ _).trans (add_le_add hq₁ hq₂)
    nlinarith
  unfold envelopeScoreBound
  nlinarith

/-- Exact lower second-moment matrix bound for the actual normalized
Euclidean envelope law. This is the instance of A.18 used in A.28. -/
theorem envelope_cramerRao {T : Matrix ι ι ℝ} (hT : T.PosDef) (z : ι → ℝ) :
    quadratic (envelopePrecisionUpper T)⁻¹ z ≤
      ∫ x, (z ⬝ᵥ WithLp.ofLp x) ^ 2 ∂euclideanEnvelopeLaw T := by
  let K := envelopePrecisionUpper T
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 z
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (K⁻¹ *ᵥ z)
  have hK : K.PosDef := envelopePrecisionUpper_posDef hT
  have hkv : K *ᵥ (WithLp.ofLp v) = z := by
    change K *ᵥ (K⁻¹ *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv K
      (K.isUnit_iff_isUnit_det.mp hK.isUnit), Matrix.one_mulVec]
  have huv : ⟪u, v⟫ = quadratic K⁻¹ z := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [u, v, WithLp.ofLp_toLp, Pi.star_apply, star_trivial, quadratic]
    exact dotProduct_comm _ _
  have hqv : quadratic K (WithLp.ofLp v) = quadratic K⁻¹ z := by
    rw [quadratic, hkv]
    exact dotProduct_comm _ _
  have hraw := raw_secondMoment_lower (euclideanEnvelopePotential T) u v
    (a := 1 / 2) (C := envelopeScoreBound T v) (k := quadratic K (WithLp.ofLp v))
    (euclideanEnvelopePotential_contDiff T) (by norm_num : (0 : ℝ) < 1 / 2)
    (envelopeScoreBound_nonneg T v) (quadratic_nonneg hK.posSemidef _)
    (euclideanEnvelopePotential_quadratic_lower hT) (envelope_score_linear_growth T v)
    (fun x => (envelope_second_direction_bounds hT v x).1)
    (fun x => (envelope_second_direction_bounds hT v x).2)
  rw [huv, hqv] at hraw
  have hi := integrable_weight (euclideanEnvelopePotential_contDiff T).continuous
    (by norm_num : (0 : ℝ) < 1 / 2) (euclideanEnvelopePotential_quadratic_lower hT)
  have hZ : 0 < ∫ x, weight (euclideanEnvelopePotential T) x := integral_exp_pos hi
  rw [euclideanEnvelopeLaw_eq_volume_tilted hT, integral_tilted]
  have hid : (∫ x, (Real.exp (-euclideanEnvelopePotential T x) /
      (∫ y, Real.exp (-euclideanEnvelopePotential T y))) •
        (z ⬝ᵥ WithLp.ofLp x) ^ 2) =
      (∫ x, ⟪u, x⟫ ^ 2 * weight (euclideanEnvelopePotential T) x) /
        (∫ y, weight (euclideanEnvelopePotential T) y) := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [] with x
    have he : ⟪u, x⟫ = z ⬝ᵥ WithLp.ofLp x := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [u, WithLp.ofLp_toLp, Pi.star_apply, star_trivial]
      exact dotProduct_comm _ _
    rw [he]
    simp only [weight, smul_eq_mul]
    ring
  rw [hid]
  apply (le_div_iff₀ hZ).mpr
  dsimp [K] at hraw ⊢
  nlinarith

end
end TheoremA2.GaussianCovariance
