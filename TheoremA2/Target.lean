import TheoremA2.Characteristic
import TheoremA2.Parameters

/-!
# The exact statement and its numerical final reduction

`UniformPositivityStatement` below is the full statement of Theorem A.2.
Its unconditional proof is `uniformPositivity` in `UniformPositivity.lean`.

This module isolates the numerical deduction from the actual relative
comparison (76) and normalizer lower bound (77). The final assembly supplies
both estimates from their proved analytic constructions.
-/

namespace TheoremA2

/-- The three assertions made by A.2, for one dimension and one matrix. -/
def A2Conclusion {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (characteristic S (theta k)).im = 0 ∧
    lowerBound k ≤ (characteristic S (theta k)).re ∧ 0 < lowerBound k

/--
The exact unrestricted statement in the paper, proved by `uniformPositivity`.
-/
def UniformPositivityStatement : Prop :=
  ∀ (k : ℕ), 0 < k →
    ∀ S : Matrix (Fin k) (Fin k) ℝ, IsSignMatrix S → A2Conclusion S

/-- The target really is equivalent to the corresponding real expectation bound. -/
theorem uniformPositivityStatement_iff :
    UniformPositivityStatement ↔
      ∀ (k : ℕ), 0 < k → ∀ S : Matrix (Fin k) (Fin k) ℝ,
        IsSignMatrix S → lowerBound k ≤ realCharacteristic S (theta k) := by
  constructor
  · intro h k hk S hS
    simpa only [characteristic_re] using (h k hk S hS).2.1
  · intro h k hk S hS
    exact ⟨characteristic_im S _, by simpa only [characteristic_re] using h k hk S hS,
      lowerBound_pos k⟩

/--
The final numerical deduction from (76) and (77). The concrete analytic proofs
of both premises are supplied by the final unrestricted assembly.
-/
theorem conclusion_of_relative_comparison {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (ZF : ℝ)
    (hnormalizer : Real.exp (-(referenceLambda k * ((k : ℝ) * rowVariance k))) ≤ ZF)
    (hcomparison : ZF * comparisonBracket k ≤ realCharacteristic S (theta k)) :
    A2Conclusion S := by
  have hZpos : 0 < ZF := lt_of_lt_of_le (Real.exp_pos _) hnormalizer
  have hquarter : ZF * (1 / 4) ≤ ZF * comparisonBracket k :=
    mul_le_mul_of_nonneg_left (comparisonBracket_ge_quarter hk) hZpos.le
  have hbound : lowerBound k ≤ ZF * (1 / 4) := by
    unfold lowerBound
    rw [← normalizer_exponent_eq hk]
    nlinarith
  exact ⟨characteristic_im S _, by
    rw [characteristic_re]
    exact le_trans hbound (le_trans hquarter hcomparison), lowerBound_pos k⟩

end TheoremA2
