import TheoremA2.PeriodicCells
import TheoremA2.JointPrecisionAlgebra
import TheoremA2.FiniteExponential
import TheoremA2.TiltedMGF

/-!
# The actual joint positive-reference law

The base measure is counting measure on all spins times ordinary Euclidean
volume. The density contains the literal scalar prior from A.32, the uniform
spin factor, and the displayed quadratic/bilinear Gibbs weight.
-/

namespace TheoremA2.JointReference

open MeasureTheory ProbabilityTheory Set TheoremA2.PeriodicCells
open scoped BigOperators ENNReal NNReal Matrix
noncomputable section

abbrev Auxiliary (s : ℕ) := EuclideanSpace ℝ (Fin s)
abbrev Outcome (r s : ℕ) := Spin r × Auxiliary s
abbrev JointSpace (r s : ℕ) := EuclideanSpace ℝ (Fin r ⊕ Fin s)

def base (r s : ℕ) : Measure (Outcome r s) := Measure.count.prod volume

def vector {r s : ℕ} (ω : Outcome r s) : JointSpace r s :=
  WithLp.toLp 2 (Sum.elim (fun i => sign (ω.1 i)) (fun j => ω.2 j))

def raw {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (ω : Outcome r s) : ℝ :=
  (Fintype.card (Spin r) : ℝ)⁻¹ *
    Real.exp (-lam * projectedEnergy B ω.1 + ∑ j, projection B ω.1 j * ω.2 j) *
      ∏ j, CosineReference.density lam (ω.2 j)

def normalizer {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) : ℝ :=
  referenceNormalizer B (CosineReference.reference lam)

def law {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) : Measure (Outcome r s) :=
  (base r s).withDensity (fun ω => ENNReal.ofReal (raw B lam ω / normalizer B lam))

theorem normalizer_pos {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ}
    (hlam : 0 < lam) : 0 < normalizer B lam :=
  lt_of_lt_of_le (Real.exp_pos _)
    (CosineReference.referenceNormalizer_lower_bound_explicit B hlam)

theorem raw_nonneg {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ}
    (hlam : 0 < lam) (ω : Outcome r s) : 0 ≤ raw B lam ω := by
  unfold raw
  apply mul_nonneg (by positivity)
  exact Finset.prod_nonneg fun j _ => CosineReference.density_nonneg hlam _

theorem measurable_scalar_density (lam : ℝ) : Measurable (CosineReference.density lam) := by
  unfold CosineReference.density
  apply Measurable.indicator _ measurableSet_Icc
  exact ((CosineReference.continuous_weight lam).div_const _).measurable

theorem measurable_raw {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) :
    Measurable (raw B lam) := by
  apply measurable_from_prod_countable_right
  intro σ
  unfold raw
  apply Measurable.mul (by fun_prop)
  apply Finset.measurable_prod
  intro j _
  exact (measurable_scalar_density lam).comp (by fun_prop)

theorem measurable_vector (r s : ℕ) : Measurable (@vector r s) := by
  apply measurable_from_prod_countable_right
  intro σ
  change Measurable (fun t : Auxiliary s =>
    (MeasurableEquiv.toLp 2 ((Fin r ⊕ Fin s) → ℝ))
      (Sum.elim (fun i => sign (σ i)) (fun j => t j)))
  apply (MeasurableEquiv.toLp 2 ((Fin r ⊕ Fin s) → ℝ)).measurable.comp
  apply measurable_pi_lambda
  intro i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem euclidean_product_integral {s : ℕ} (f : Fin s → ℝ → ℝ) :
    (∫ t : Auxiliary s, ∏ j, f j (t j)) = ∏ j, ∫ x, f j x := by
  calc
    (∫ t : Auxiliary s, ∏ j, f j (t j)) = ∫ t : Fin s → ℝ, ∏ j, f j (t j) :=
      (PiLp.volume_preserving_ofLp (Fin s)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin s → ℝ)).symm.measurableEmbedding
        (fun t : Fin s → ℝ => ∏ j, f j (t j))
    _ = _ := integral_fintype_prod_eq_prod _

theorem integrable_euclidean_product {s : ℕ} {f : Fin s → ℝ → ℝ}
    (hf : ∀ j, Integrable (f j)) :
    Integrable (fun t : Auxiliary s => ∏ j, f j (t j)) := by
  exact (PiLp.volume_preserving_ofLp (Fin s)).integrable_comp_of_integrable
    (Integrable.fintype_prod hf)

theorem raw_factorization {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ)
    (σ : Spin r) (t : Auxiliary s) :
    raw B lam (σ, t) =
      (Fintype.card (Spin r) : ℝ)⁻¹ * Real.exp (-lam * projectedEnergy B σ) *
        ∏ j, CosineReference.density lam (t j) * Real.exp (projection B σ j * t j) := by
  rw [raw, Real.exp_add, Real.exp_sum, Finset.prod_mul_distrib]
  ring

theorem integrable_raw_section {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (σ : Spin r) : Integrable (fun t => raw B lam (σ, t)) := by
  simp_rw [raw_factorization]
  exact (integrable_euclidean_product fun j =>
    CosineReference.integrable_density_exponential_moment lam (projection B σ j)).const_mul _

theorem integrable_raw {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) :
    Integrable (raw B lam) (base r s) := by
  apply (integrable_prod_iff (measurable_raw B lam).aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall (integrable_raw_section B lam), Integrable.of_finite⟩

theorem raw_section_integral {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ}
    (hlam : 0 < lam) (σ : Spin r) :
    (∫ t, raw B lam (σ, t)) = (Fintype.card (Spin r) : ℝ)⁻¹ *
      referenceProduct lam (projection B σ) := by
  simp_rw [raw_factorization]
  rw [integral_const_mul, euclidean_product_integral (fun j x =>
    CosineReference.density lam x * Real.exp (projection B σ j * x))]
  unfold referenceProduct
  simp_rw [CosineReference.reference_eq_gaussian_times_mgf hlam]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  have he : (∑ j : Fin s, -lam * (projection B σ j) ^ 2) =
      -lam * projectedEnergy B σ := by
    rw [← Finset.mul_sum]
    rfl
  rw [he]
  ring

/-- The joint normalizing constant is exactly the finite reference normalizer. -/
theorem integral_raw {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ}
    (hlam : 0 < lam) : (∫ ω, raw B lam ω ∂base r s) = normalizer B lam := by
  rw [base, integral_prod _ (integrable_raw B lam), integral_count]
  simp_rw [raw_section_integral B hlam]
  rw [← Finset.mul_sum]
  rfl

theorem isProbabilityMeasure_law {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ}
    (hlam : 0 < lam) : IsProbabilityMeasure (law B lam) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_raw B lam).div_const _)
    (Filter.Eventually.of_forall fun ω =>
      div_nonneg (raw_nonneg B hlam ω) (normalizer_pos B hlam).le)]
  rw [integral_div, integral_raw B hlam, div_self (ne_of_gt (normalizer_pos B hlam))]
  simp

theorem integral_law {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ}
    (hlam : 0 < lam) (f : Outcome r s → ℝ) :
    (∫ ω, f ω ∂law B lam) =
      (normalizer B lam)⁻¹ * ∫ ω, raw B lam ω * f ω ∂base r s := by
  rw [law, integral_withDensity_eq_integral_toReal_smul
    (((measurable_raw B lam).div_const _).ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (div_nonneg (raw_nonneg B hlam _)
    (normalizer_pos B hlam).le), smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ω
  ring

theorem integrable_law_iff {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ}
    (hlam : 0 < lam) (f : Outcome r s → ℝ) :
    Integrable f (law B lam) ↔
      Integrable (fun ω => raw B lam ω * f ω) (base r s) := by
  rw [law, integrable_withDensity_iff_integrable_smul'
    (((measurable_raw B lam).div_const _).ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (div_nonneg (raw_nonneg B hlam _)
    (normalizer_pos B hlam).le), smul_eq_mul]
  have he : (fun ω => raw B lam ω / normalizer B lam * f ω) =
      fun ω => (normalizer B lam)⁻¹ * (raw B lam ω * f ω) := by
    funext ω
    ring
  rw [he]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (inv_ne_zero (ne_of_gt (normalizer_pos B hlam)))) _

def linear {r s : ℕ} (u : Fin r → ℝ) (v : Fin s → ℝ) (ω : Outcome r s) : ℝ :=
  (∑ i, u i * sign (ω.1 i)) + ∑ j, v j * ω.2 j

theorem inner_vector {r s : ℕ} (u : Fin r → ℝ) (v : Fin s → ℝ) (ω : Outcome r s) :
    inner ℝ (WithLp.toLp 2 (Sum.elim u v)) (vector ω) = linear u v ω := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, vector, linear,
    WithLp.ofLp_toLp, dotProduct, Pi.star_apply, star_trivial, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, mul_comm]

theorem measurable_linear {r s : ℕ} (u : Fin r → ℝ) (v : Fin s → ℝ) :
    Measurable (linear u v) := by
  apply measurable_from_prod_countable_right
  intro σ
  unfold linear
  fun_prop

theorem raw_exponential_factorization {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (u : Fin r → ℝ) (v : Fin s → ℝ) (σ : Spin r) (t : Auxiliary s) :
    raw B lam (σ, t) * Real.exp (linear u v (σ, t)) =
      (Fintype.card (Spin r) : ℝ)⁻¹ *
        Real.exp (-lam * projectedEnergy B σ + ∑ i, u i * sign (σ i)) *
          ∏ j, CosineReference.density lam (t j) *
            Real.exp ((projection B σ j + v j) * t j) := by
  unfold raw linear
  simp only [add_mul, Real.exp_add, Real.exp_sum,
    Finset.prod_mul_distrib]
  ring

theorem integrable_raw_exponential_section {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (u : Fin r → ℝ) (v : Fin s → ℝ) (σ : Spin r) :
    Integrable (fun t => raw B lam (σ, t) * Real.exp (linear u v (σ, t))) := by
  simp_rw [raw_exponential_factorization]
  exact (integrable_euclidean_product fun j =>
    CosineReference.integrable_density_exponential_moment lam (projection B σ j + v j)).const_mul _

theorem integral_raw_exponential_section {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (u : Fin r → ℝ) (v : Fin s → ℝ) (σ : Spin r) :
    (∫ t : Auxiliary s, raw B lam (σ, t) * Real.exp (linear u v (σ, t))) =
      (Fintype.card (Spin r) : ℝ)⁻¹ *
        Real.exp (-lam * projectedEnergy B σ + ∑ i, u i * sign (σ i)) *
          ∏ j, ∫ x, CosineReference.density lam x *
            Real.exp ((projection B σ j + v j) * x) := by
  simp_rw [raw_exponential_factorization]
  rw [integral_const_mul, euclidean_product_integral (fun j x =>
    CosineReference.density lam x * Real.exp ((projection B σ j + v j) * x))]

theorem integrable_raw_exponential {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (u : Fin r → ℝ) (v : Fin s → ℝ) :
    Integrable (fun ω => raw B lam ω * Real.exp (linear u v ω)) (base r s) := by
  apply (integrable_prod_iff ((measurable_raw B lam).mul
    (measurable_linear u v).exp).aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall (integrable_raw_exponential_section B lam u v),
    Integrable.of_finite⟩

theorem integrable_exponential_linear {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (u : Fin r → ℝ) (v : Fin s → ℝ) :
    Integrable (fun ω => Real.exp (linear u v ω)) (law B lam) :=
  (integrable_law_iff B hlam _).2 (integrable_raw_exponential B lam u v)

theorem integrable_exponential_inner {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h : JointSpace r s) :
    Integrable (fun ω => Real.exp (inner ℝ h (vector ω))) (law B lam) := by
  have he : h = WithLp.toLp 2 (Sum.elim (fun i => h (Sum.inl i))
      (fun j => h (Sum.inr j))) := by
    ext i
    cases i <;> rfl
  rw [he]
  simp_rw [inner_vector]
  exact integrable_exponential_linear B hlam _ _

def negateSpin {r : ℕ} (σ : Spin r) : Spin r := fun i => !σ i

def negateSpinEquiv (r : ℕ) : Spin r ≃ Spin r where
  toFun := negateSpin
  invFun := negateSpin
  left_inv σ := by ext i; simp [negateSpin]
  right_inv σ := by ext i; simp [negateSpin]

theorem projection_negateSpin {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (σ : Spin r) :
    projection B (negateSpin σ) = -projection B σ := by
  funext j
  simp [projection, negateSpin, Finset.sum_neg_distrib]

theorem projectedEnergy_negateSpin {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (σ : Spin r) :
    projectedEnergy B (negateSpin σ) = projectedEnergy B σ := by
  change (∑ j, (projection B (negateSpin σ) j) ^ 2) = ∑ j, (projection B σ j) ^ 2
  rw [projection_negateSpin]
  simp

theorem scalar_density_neg (lam t : ℝ) : CosineReference.density lam (-t) =
    CosineReference.density lam t := by
  have hm : -t ∈ Icc (-CosineReference.endpoint lam) (CosineReference.endpoint lam) ↔
      t ∈ Icc (-CosineReference.endpoint lam) (CosineReference.endpoint lam) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  unfold CosineReference.density
  by_cases ht : t ∈ Icc (-CosineReference.endpoint lam) (CosineReference.endpoint lam)
  · rw [indicator_of_mem ht, indicator_of_mem (hm.2 ht)]
    simp [CosineReference.weight, neg_div]
  · rw [indicator_of_notMem ht, indicator_of_notMem (mt hm.1 ht)]

theorem raw_negation {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ)
    (σ : Spin r) (t : Auxiliary s) :
    raw B lam (negateSpin σ, -t) = raw B lam (σ, t) := by
  simp [raw, projectedEnergy_negateSpin, projection_negateSpin, scalar_density_neg]

theorem linear_negation {r s : ℕ} (u : Fin r → ℝ) (v : Fin s → ℝ)
    (σ : Spin r) (t : Auxiliary s) :
    linear u v (negateSpin σ, -t) = -linear u v (σ, t) := by
  simp only [linear, negateSpin, sign_not, PiLp.neg_apply, mul_neg,
    Finset.sum_neg_distrib]
  ring

theorem linear_smul {r s : ℕ} (a : ℝ) (u : Fin r → ℝ) (v : Fin s → ℝ)
    (ω : Outcome r s) : linear (a • u) (a • v) ω = a * linear u v ω := by
  simp only [linear, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem integrable_exp_mul_linear {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (u : Fin r → ℝ) (v : Fin s → ℝ) (a : ℝ) :
    Integrable (fun ω => Real.exp (a * linear u v ω)) (law B lam) := by
  simpa only [linear_smul] using integrable_exponential_linear B hlam (a • u) (a • v)

theorem integrable_linear {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (u : Fin r → ℝ) (v : Fin s → ℝ) :
    Integrable (linear u v) (law B lam) := by
  have hi : (0 : ℝ) ∈ interior (integrableExpSet (linear u v) (law B lam)) := by
    simp [integrableExpSet, integrable_exp_mul_linear B hlam u v]
  exact memLp_one_iff_integrable.1 (memLp_of_mem_interior_integrableExpSet hi 1)

/-- The actual joint law is centered, by its simultaneous spin/auxiliary symmetry. -/
theorem integral_linear_zero {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (u : Fin r → ℝ) (v : Fin s → ℝ) :
    (∫ ω, linear u v ω ∂law B lam) = 0 := by
  have hi := (integrable_law_iff B hlam (linear u v)).1 (integrable_linear B hlam u v)
  rw [integral_law B hlam, base, integral_prod _ hi, integral_count]
  have hz : (∑ σ : Spin r, ∫ t : Auxiliary s, raw B lam (σ, t) * linear u v (σ, t)) = 0 := by
    let F : Spin r → ℝ := fun σ => ∫ t : Auxiliary s, raw B lam (σ, t) * linear u v (σ, t)
    have hsym : (∑ σ, F σ) = -(∑ σ, F σ) := by
      calc
        (∑ σ, F σ) = ∑ σ, F (negateSpin σ) := (Equiv.sum_comp (negateSpinEquiv r) F).symm
        _ = ∑ σ : Spin r, ∫ t : Auxiliary s,
            raw B lam (negateSpin σ, -t) * linear u v (negateSpin σ, -t) := by
          apply Finset.sum_congr rfl
          intro σ _
          exact (integral_neg_eq_self _ volume).symm
        _ = -(∑ σ, F σ) := by
          simp_rw [raw_negation, linear_negation, mul_neg, integral_neg]
          rw [Finset.sum_neg_distrib]
    dsimp only [F] at hsym
    linarith
  rw [hz, mul_zero]

theorem integrable_raw_spin_function {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (f : Spin r → ℝ) :
    Integrable (fun ω : Outcome r s => raw B lam ω * f ω.1) (base r s) := by
  apply (integrable_prod_iff ((measurable_raw B lam).mul
    ((measurable_of_countable f).comp measurable_fst)).aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall (fun σ => (integrable_raw_section B lam σ).mul_const (f σ)),
    Integrable.of_finite⟩

/-- Forgetting the auxiliary variables gives precisely the displayed finite
reference-weighted spin law, including its uniform-spin normalizing factor. -/
theorem spin_marginal_integral {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (f : Spin r → ℝ) :
    (∫ ω : Outcome r s, f ω.1 ∂law B lam) =
      (normalizer B lam)⁻¹ * average (fun σ =>
        referenceProduct lam (projection B σ) * f σ) := by
  rw [integral_law B hlam, base,
    integral_prod _ (integrable_raw_spin_function B lam f), integral_count]
  simp_rw [integral_mul_const, raw_section_integral B hlam, mul_assoc]
  rw [← Finset.mul_sum]
  rfl

theorem weighted_spin_exponential_identity {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ} (hlam : 0 < lam) (u : Fin r → ℝ) :
    average (fun σ => referenceProduct lam (projection B σ) *
      Real.exp (∑ i, u i * sign (σ i))) =
      normalizer B lam * ∫ ω, Real.exp (linear u 0 ω) ∂law B lam := by
  simp only [linear, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [spin_marginal_integral B hlam (fun σ => Real.exp (∑ i, u i * sign (σ i))), ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt (normalizer_pos B hlam)), one_mul]

end
end TheoremA2.JointReference
