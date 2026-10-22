import TheoremA2.JointReference

/-!
# Arbitrary external fields for the actual reference law

Tilts are mathlib's normalized exponential tilts of the explicitly constructed
joint probability measure. Their moments are written as ratios of the literal
unnormalized density integrals, with positivity and integrability proved.
-/

namespace TheoremA2.JointReference

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
noncomputable section

theorem linear_add {r s : ℕ} (h u : Fin r → ℝ) (k v : Fin s → ℝ)
    (ω : Outcome r s) : linear (h + u) (k + v) ω = linear h k ω + linear u v ω := by
  simp only [linear, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem integrable_exponential_tilted {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h u : Fin r → ℝ) (k v : Fin s → ℝ) (a : ℝ) :
    Integrable (fun ω => Real.exp (a * linear u v ω))
      ((law B lam).tilted (linear h k)) := by
  rw [integrable_tilted_iff (integrable_exponential_linear B hlam h k)]
  simpa only [smul_eq_mul, ← Real.exp_add, linear_add, linear_smul] using
    integrable_exponential_linear B hlam (h + a • u) (k + a • v)

theorem tilted_probability {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h : Fin r → ℝ) (k : Fin s → ℝ) :
    IsProbabilityMeasure ((law B lam).tilted (linear h k)) := by
  letI := isProbabilityMeasure_law B hlam
  exact isProbabilityMeasure_tilted (integrable_exponential_linear B hlam h k)

theorem memLp_linear_tilted {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h u : Fin r → ℝ) (k v : Fin s → ℝ) (p : ℝ≥0) :
    MemLp (linear u v) p ((law B lam).tilted (linear h k)) := by
  have hi : (0 : ℝ) ∈ interior
      (integrableExpSet (linear u v) ((law B lam).tilted (linear h k))) := by
    simp [integrableExpSet, integrable_exponential_tilted B hlam h u k v]
  exact memLp_of_mem_interior_integrableExpSet hi p

def tiltedRaw {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ)
    (h : Fin r → ℝ) (k : Fin s → ℝ) (ω : Outcome r s) : ℝ :=
  raw B lam ω * Real.exp (linear h k ω)

def tiltedRawMass {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ)
    (h : Fin r → ℝ) (k : Fin s → ℝ) : ℝ :=
  ∫ ω, tiltedRaw B lam h k ω ∂base r s

theorem integrable_tiltedRaw {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h : Fin r → ℝ) (k : Fin s → ℝ) :
    Integrable (tiltedRaw B lam h k) (base r s) :=
  (integrable_law_iff B hlam _).1 (integrable_exponential_linear B hlam h k)

theorem tiltedRawMass_pos {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h : Fin r → ℝ) (k : Fin s → ℝ) :
    0 < tiltedRawMass B lam h k := by
  letI := isProbabilityMeasure_law B hlam
  have hp := integral_exp_pos (integrable_exponential_linear B hlam h k)
  rw [integral_law B hlam] at hp
  change 0 < (normalizer B lam)⁻¹ * tiltedRawMass B lam h k at hp
  exact (mul_pos_iff_of_pos_left (inv_pos.2 (normalizer_pos B hlam))).1 hp

/-- A normalized exponential tilt, expressed entirely in the actual base
counting/Lebesgue density. Common normalizing factors cancel explicitly. -/
theorem integral_tilted_raw {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h : Fin r → ℝ) (k : Fin s → ℝ)
    (f : Outcome r s → ℝ) :
    (∫ ω, f ω ∂(law B lam).tilted (linear h k)) =
      (∫ ω, tiltedRaw B lam h k ω * f ω ∂base r s) / tiltedRawMass B lam h k := by
  rw [integral_tilted]
  simp only [smul_eq_mul]
  have he : (fun ω : Outcome r s =>
      (Real.exp (linear h k ω) / ∫ ω, Real.exp (linear h k ω) ∂law B lam) * f ω) =
      (fun ω => (Real.exp (linear h k ω) * f ω) /
        (∫ ω, Real.exp (linear h k ω) ∂law B lam)) := by
    funext ω
    ring
  rw [he, integral_div, integral_law B hlam, integral_law B hlam]
  rw [mul_div_mul_left _ _ (inv_ne_zero (ne_of_gt (normalizer_pos B hlam)))]
  simp only [tiltedRawMass, tiltedRaw, mul_assoc]

theorem tilted_variance_eq_raw {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h u : Fin r → ℝ) (k v : Fin s → ℝ) :
    Var[linear u v; (law B lam).tilted (linear h k)] =
      (∫ ω, tiltedRaw B lam h k ω * linear u v ω ^ 2 ∂base r s) / tiltedRawMass B lam h k -
        ((∫ ω, tiltedRaw B lam h k ω * linear u v ω ∂base r s) /
          tiltedRawMass B lam h k) ^ 2 := by
  letI := tilted_probability B hlam h k
  rw [variance_eq_sub (memLp_linear_tilted B hlam h u k v 2)]
  rw [integral_tilted_raw B hlam h k, integral_tilted_raw B hlam h k]
  rfl

theorem integrable_tiltedRaw_moment {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (h u : Fin r → ℝ) (k v : Fin s → ℝ) :
    Integrable (fun ω => tiltedRaw B lam h k ω * linear u v ω) (base r s) ∧
      Integrable (fun ω => tiltedRaw B lam h k ω * linear u v ω ^ 2) (base r s) := by
  letI := tilted_probability B hlam h k
  have hp := memLp_linear_tilted B hlam h u k v 2
  have hi := memLp_one_iff_integrable.1 (memLp_linear_tilted B hlam h u k v 1)
  have hi2 := (memLp_two_iff_integrable_sq hp.aestronglyMeasurable).1 hp
  have he := integrable_exponential_linear B hlam h k
  rw [integrable_tilted_iff he] at hi hi2
  simp only [smul_eq_mul] at hi hi2
  have h1 := (integrable_law_iff B hlam _).1 hi
  have h2 := (integrable_law_iff B hlam _).1 hi2
  simpa only [tiltedRaw, mul_assoc] using And.intro h1 h2

end
end TheoremA2.JointReference
