import TheoremA2.Target
import TheoremA2.ScaledMatrix
import TheoremA2.CosineReference

/-!
# A conditional reduction using the actual reference normalizer

The definitions in this module use the explicit Lebesgue-integral reference
function from `CosineReference.lean` and the actual scaled sign matrix. The
normalizer lower bound (77) is proved, not postulated.

The relative comparison (76) is an explicit premise of the reusable numerical
reduction in this module. Its unconditional proof is `concreteRelativeComparison`
in `UniformPositivity.lean`, using the actual joint-law and spin-covariance
theorems.
-/

namespace TheoremA2

noncomputable section

/-- The paper's actual positive-reference normalizer at the A.2 parameters. -/
def actualReferenceNormalizer {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  referenceNormalizer (scaledMatrix S) (CosineReference.reference (referenceLambda k))

/-- Equation (77), with the concrete reference and exact scaled sign matrix. -/
theorem actualReferenceNormalizer_lower_bound {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) :
    Real.exp (-(referenceLambda k * ((k : ℝ) * rowVariance k))) ≤
      actualReferenceNormalizer S := by
  have hlam : 0 < referenceLambda k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    (referenceLambda_ge_two hk)
  have h := CosineReference.referenceNormalizer_lower_bound_explicit (scaledMatrix S) hlam
  rw [frobeniusSq_scaledMatrix hk S hS] at h
  simpa only [actualReferenceNormalizer, neg_mul] using h

theorem actualReferenceNormalizer_pos {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) :
    0 < actualReferenceNormalizer S :=
  lt_of_lt_of_le (Real.exp_pos _) (actualReferenceNormalizer_lower_bound hk S hS)

/-- The relative comparison specialized to the exact A.2 parameters.
It is proved by `concreteRelativeComparison` in the final assembly. -/
def ConcreteRelativeComparisonStatement : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ S : Matrix (Fin k) (Fin k) ℝ, IsSignMatrix S →
    actualReferenceNormalizer S * comparisonBracket k ≤ realCharacteristic S (theta k)

/-- The numerical deduction from the concrete relative comparison (76). -/
theorem conclusion_of_concrete_relative_comparison {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S)
    (hcomparison : actualReferenceNormalizer S * comparisonBracket k ≤
      realCharacteristic S (theta k)) : A2Conclusion S :=
  conclusion_of_relative_comparison hk S (actualReferenceNormalizer S)
    (actualReferenceNormalizer_lower_bound hk S hS) hcomparison

/-- A reusable implication from the concrete relative comparison to A.2. -/
theorem uniformPositivity_of_concrete_relative_comparison
    (hcomparison : ConcreteRelativeComparisonStatement) : UniformPositivityStatement := by
  intro k hk S hS
  exact conclusion_of_concrete_relative_comparison hk S hS (hcomparison k hk S hS)

end

end TheoremA2
