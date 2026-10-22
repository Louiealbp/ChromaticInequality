import TheoremA2.JointMarginalIntegrability
import TheoremA2.JointReferenceTilt
import BrascampLieb.CosineApproximation

/-!
# Actual moment convergence to the compactly supported joint reference law

The smooth potentials are the concrete extensions of the cosine prior.
Their unnormalized joint densities converge to a positive constant times
the literal tilted reference density. First and second moments converge by
one explicit, integrable Gaussian majorant. The endpoints are included.
-/

namespace TheoremA2.JointMarginal

open MeasureTheory ProbabilityTheory Filter Set
open TheoremA2.JointReference TheoremA2.PeriodicCells
open scoped BigOperators Topology
noncomputable section

def approximatePrior (lam : ℝ) (n : ℕ) : ℝ → ℝ :=
  BrascampLieb.cosineExtension lam (BrascampLieb.innerRadius lam n)

theorem approximatePrior_contDiff {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ContDiff ℝ 2 (approximatePrior lam n) :=
  BrascampLieb.cosineExtension_contDiff hlam
    (BrascampLieb.innerRadius_nonneg hlam n) (BrascampLieb.innerRadius_lt hlam n)

theorem approximatePrior_curvature {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (x : ℝ) :
    BrascampLieb.curvatureConstant lam ≤ deriv (deriv (approximatePrior lam n)) x :=
  BrascampLieb.cosineExtension_curvature hlam
    (BrascampLieb.innerRadius_nonneg hlam n) (BrascampLieb.innerRadius_lt hlam n) x

theorem approximatePrior_quadratic {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (x : ℝ) :
    BrascampLieb.curvatureConstant lam / 2 * x ^ 2 ≤ approximatePrior lam n x := by
  have h := BrascampLieb.cosineExtension_quadratic_lower hlam
    (BrascampLieb.innerRadius_nonneg hlam n) (BrascampLieb.innerRadius_lt hlam n) x
  simpa only [approximatePrior, div_mul_eq_mul_div] using h

theorem cosinePriorWeight_eq_density {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    BrascampLieb.cosinePriorWeight lam x =
      CosineReference.normalizer lam * CosineReference.density lam x := by
  have hZ := ne_of_gt (CosineReference.normalizer_pos hlam)
  have he : BrascampLieb.endpoint lam = CosineReference.endpoint lam := rfl
  by_cases hx : x ∈ Ioo (-CosineReference.endpoint lam) (CosineReference.endpoint lam)
  · have hx' : x ∈ Icc (-CosineReference.endpoint lam) (CosineReference.endpoint lam) :=
      ⟨hx.1.le, hx.2.le⟩
    rw [CosineReference.density, indicator_of_mem hx', BrascampLieb.cosinePriorWeight,
      he, if_pos hx]
    change CosineReference.weight lam x = _
    field_simp
  · rw [BrascampLieb.cosinePriorWeight, he, if_neg hx]
    by_cases hc : x ∈ Icc (-CosineReference.endpoint lam) (CosineReference.endpoint lam)
    · have he : x = -CosineReference.endpoint lam ∨ x = CosineReference.endpoint lam := by
        simp only [mem_Ioo, not_and_or, not_lt] at hx
        rcases hx with h | h
        · exact Or.inl (le_antisymm h hc.1)
        · exact Or.inr (le_antisymm hc.2 h)
      rw [CosineReference.density, indicator_of_mem hc]
      rcases he with rfl | rfl <;>
        simp [CosineReference.weight_neg, CosineReference.weight_endpoint hlam]
    · simp [CosineReference.density, hc]

/-- The factor omitted by the smooth, unnormalized finite/Lebesgue weights. -/
def priorScale (r s : ℕ) (lam : ℝ) : ℝ :=
  (Fintype.card (Spin r) : ℝ) * CosineReference.normalizer lam ^ s

theorem priorScale_pos (r s : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    0 < priorScale r s lam := by
  unfold priorScale
  exact mul_pos (by exact_mod_cast Fintype.card_pos) (pow_pos (CosineReference.normalizer_pos hlam) _)

theorem jointWeight_product {r s : ℕ} (U : ℝ → ℝ)
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (h : Fin r → ℝ)
    (k : Fin s → ℝ) (σ : Spin r) (t : Auxiliary s) :
    jointWeight U B lam h k σ t =
      Real.exp (spinConstant B lam h σ + spinLinear B σ t + fieldLinear k t) *
        ∏ j, Real.exp (-U (t j)) := by
  rw [jointWeight, sub_eq_add_neg, Real.exp_add, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem limitWeight_eq_tiltedRaw {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h : Fin r → ℝ) (k : Fin s → ℝ)
    (σ : Spin r) (t : Auxiliary s) :
    Real.exp (spinConstant B lam h σ + spinLinear B σ t + fieldLinear k t) *
      (∏ j, BrascampLieb.cosinePriorWeight lam (t j)) =
        priorScale r s lam * tiltedRaw B lam h k (σ, t) := by
  simp_rw [cosinePriorWeight_eq_density hlam]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcard : (Fintype.card (Spin r) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold priorScale tiltedRaw raw spinConstant spinLinear linear
  simp only [fieldLinear_apply, dotProduct, SpinCovariance.spinVector, Real.exp_add]
  field_simp

theorem tendsto_jointWeight {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h : Fin r → ℝ) (k : Fin s → ℝ)
    (σ : Spin r) (t : Auxiliary s) :
    Tendsto (fun n => jointWeight (approximatePrior lam n) B lam h k σ t) atTop
      (𝓝 (priorScale r s lam * tiltedRaw B lam h k (σ, t))) := by
  simp_rw [jointWeight_product]
  rw [← limitWeight_eq_tiltedRaw B hlam h k σ t]
  apply Tendsto.const_mul
  exact tendsto_finsetProd _ fun j _ => BrascampLieb.tendsto_innerRadius_density hlam (t j)

/-- One dominated-convergence statement handles the mass and both moments. -/
theorem tendsto_integral_jointWeight_observable {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (h : Fin r → ℝ) (k : Fin s → ℝ) (σ : Spin r)
    {g : Auxiliary s → ℝ} (hg : AEStronglyMeasurable g volume)
    {C : ℝ} (hC : 0 ≤ C) (hgC : ∀ t, |g t| ≤ C * (1 + ‖t‖ ^ 2)) :
    Tendsto (fun n => ∫ t, g t * jointWeight (approximatePrior lam n) B lam h k σ t)
      atTop (𝓝 (∫ t, g t * (priorScale r s lam * tiltedRaw B lam h k (σ, t)))) := by
  let H := BrascampLieb.curvatureConstant lam
  have hH : 0 < H := BrascampLieb.curvatureConstant_pos hlam
  apply tendsto_integral_of_dominated_convergence
    (fun t : Auxiliary s =>
      (C * Real.exp (spinConstant B lam h σ)) * (1 + ‖t‖ ^ 2) *
        Real.exp (-(H / 2) * ‖t‖ ^ 2 +
          inner ℝ (WithLp.toLp 2 (projection B σ + k)) t))
  · intro n
    exact hg.mul (continuous_jointWeight (approximatePrior_contDiff hlam n).continuous
      B lam h k σ).aestronglyMeasurable
  · convert (BrascampLieb.integrable_one_add_quadratic_gaussian_linear
      (show 0 < H / 2 by positivity) (WithLp.toLp 2 (projection B σ + k))).const_mul
        (C * Real.exp (spinConstant B lam h σ)) using 1
    ext t
    ring
  · intro n
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_pos (jointWeight_pos (approximatePrior lam n) B lam h k σ t)]
      calc
        _ ≤ (C * (1 + ‖t‖ ^ 2)) * jointWeight (approximatePrior lam n) B lam h k σ t :=
          mul_le_mul_of_nonneg_right (hgC t)
            (jointWeight_pos (approximatePrior lam n) B lam h k σ t).le
        _ ≤ (C * (1 + ‖t‖ ^ 2)) *
            (Real.exp (spinConstant B lam h σ) * Real.exp (-(H / 2) * ‖t‖ ^ 2 +
              inner ℝ (WithLp.toLp 2 (projection B σ + k)) t)) :=
          mul_le_mul_of_nonneg_left
            (jointWeight_gaussian_bound (approximatePrior_quadratic hlam n) B lam h k σ t)
            (by positivity)
        _ = _ := by ring
  · exact Eventually.of_forall fun t => (tendsto_jointWeight B hlam h k σ t).const_mul (g t)

/-- A literal unnormalized moment of the smooth finite/Lebesgue mixture. -/
def approximateMoment {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ)
    (h : Fin r → ℝ) (k : Fin s → ℝ) (f : Outcome r s → ℝ) (n : ℕ) : ℝ :=
  ∑ σ : Spin r, ∫ t : Auxiliary s,
    f (σ, t) * jointWeight (approximatePrior lam n) B lam h k σ t

theorem tendsto_approximateMoment {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h : Fin r → ℝ) (k : Fin s → ℝ)
    (f : Outcome r s → ℝ) (hf : Measurable f)
    (hfi : Integrable (fun ω => tiltedRaw B lam h k ω * f ω) (base r s))
    {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ σ t, |f (σ, t)| ≤ C * (1 + ‖t‖ ^ 2)) :
    Tendsto (approximateMoment B lam h k f) atTop
      (𝓝 (priorScale r s lam * ∫ ω, tiltedRaw B lam h k ω * f ω ∂base r s)) := by
  have he : priorScale r s lam * (∫ ω, tiltedRaw B lam h k ω * f ω ∂base r s) =
      ∑ σ : Spin r, ∫ t : Auxiliary s,
        f (σ, t) * (priorScale r s lam * tiltedRaw B lam h k (σ, t)) := by
    rw [base, integral_prod _ hfi, integral_count, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by ring
  rw [he]
  exact tendsto_finsetSum _ fun σ _ =>
    tendsto_integral_jointWeight_observable B hlam h k σ
      (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable hC (hfC σ)

theorem approximateMoment_one {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h : Fin r → ℝ) (k : Fin s → ℝ) (n : ℕ) :
    approximateMoment B lam h k (fun _ => 1) n =
      ∫ t, Real.exp (-potential (approximatePrior lam n) B lam h k t) := by
  unfold approximateMoment
  simp only [one_mul]
  rw [← integral_finsetSum _ (fun σ _ => integrable_jointWeight
    (approximatePrior_contDiff hlam n).continuous (BrascampLieb.curvatureConstant_pos hlam)
    (approximatePrior_quadratic hlam n) B lam h k σ)]
  simp only [sum_jointWeight]

theorem tendsto_approximate_mass {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h : Fin r → ℝ) (k : Fin s → ℝ) :
    Tendsto (approximateMoment B lam h k (fun _ => 1)) atTop
      (𝓝 (priorScale r s lam * tiltedRawMass B lam h k)) := by
  have hi : Integrable (fun ω => tiltedRaw B lam h k ω * (1 : ℝ)) (base r s) := by
    simpa only [mul_one] using integrable_tiltedRaw B hlam h k
  simpa only [mul_one, tiltedRawMass] using
    tendsto_approximateMoment B hlam h k (fun _ => 1) measurable_const hi
      (C := 1) (by norm_num) (fun σ t => by
        simpa only [abs_one, one_mul] using le_add_of_nonneg_right (sq_nonneg ‖t‖))

theorem tendsto_approximate_linear {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h u : Fin r → ℝ) (k v : Fin s → ℝ) :
    Tendsto (approximateMoment B lam h k (linear u v)) atTop
      (𝓝 (priorScale r s lam *
        ∫ ω, tiltedRaw B lam h k ω * linear u v ω ∂base r s)) :=
  tendsto_approximateMoment B hlam h k (linear u v) (measurable_linear u v)
    (integrable_tiltedRaw_moment B hlam h u k v).1 (momentBound_pos u v).le
    (fun σ t => (linear_first_second_bounds u v σ t).1)

theorem tendsto_approximate_linear_square {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h u : Fin r → ℝ) (k v : Fin s → ℝ) :
    Tendsto (approximateMoment B lam h k (fun ω => linear u v ω ^ 2)) atTop
      (𝓝 (priorScale r s lam *
        ∫ ω, tiltedRaw B lam h k ω * linear u v ω ^ 2 ∂base r s)) := by
  apply tendsto_approximateMoment B hlam h k (fun ω => linear u v ω ^ 2)
    ((measurable_linear u v).pow_const 2) (integrable_tiltedRaw_moment B hlam h u k v).2
    (momentBound_pos u v).le
  intro σ t
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (linear_first_second_bounds u v σ t).2

end
end TheoremA2.JointMarginal
