import TheoremA2.GaussianEnvelopeBox

/-! Polynomial moments for the actual Gaussian and bounded envelope tilts. -/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrable_dot_pow {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (b : ι → ℝ) (n : ℕ) :
    Integrable (fun x => (b ⬝ᵥ x) ^ n) (covarianceGaussian T) := by
  have hi : Integrable (fun x : ℝ => x ^ n)
      (gaussianReal 0 ((quadratic T b).toNNReal)) := by
    apply integrable_pow_of_mem_interior_integrableExpSet
    simp [integrableExpSet_id_gaussianReal]
  rw [← covarianceGaussian_map_dot hT b] at hi
  exact hi.comp_measurable (measurable_dot b)

theorem integrable_envelopeLaw_dot_pow {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (b : ι → ℝ) (n : ℕ) :
    Integrable (fun x => (b ⬝ᵥ x) ^ n) (envelopeLaw T) :=
  integrable_envelopeLaw T (integrable_dot_pow hT b n)

theorem integrable_boxEnvelopeLaw_dot_pow {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (radius : ℝ) (b : ι → ℝ) (n : ℕ) :
    Integrable (fun x => (b ⬝ᵥ x) ^ n) (boxEnvelopeLaw T radius) :=
  integrable_boxEnvelopeLaw T radius (integrable_dot_pow hT b n)

end

end TheoremA2.GaussianCovariance
