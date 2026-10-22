import TheoremA2.JointReference
import TheoremA2.CellEnergyComparison

/-!
# The exact translated-cell identity for the actual joint reference law

The auxiliary variable and its prior are unchanged. Only the source in the
exponential moment changes. Every integral below is that of the explicitly
normalized joint law, and every spin in the original finite space is retained.
-/

namespace TheoremA2.JointReference

open MeasureTheory Set
open TheoremA2.PeriodicCells TheoremA2.PrincipalInverse
open scoped BigOperators Matrix
noncomputable section
open Classical

theorem projection_eq_mulVec {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (σ : Spin r) : projection B σ = B.transpose *ᵥ (fun i => sign (σ i)) := rfl

theorem spinPart_vector {r s : ℕ} (ω : Outcome r s) :
    CellEnergyComparison.spinPart (vector ω) = fun i => sign (ω.1 i) := rfl

theorem vector_mem_cell_iff {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (l : Fin s → ℤ) (ω : Outcome r s) :
    vector ω ∈ CellEnergyComparison.cellSet B l ↔ InCell l (projection B ω.1) := Iff.rfl

theorem shifted_source_spin {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (v : Fin s → ℝ) (σ : Spin r) :
    (∑ i, ((2 * lam) • (B *ᵥ v)) i * sign (σ i)) =
      2 * lam * (projection B σ ⬝ᵥ v) := by
  change ((2 * lam) • (B *ᵥ v)) ⬝ᵥ (fun i => sign (σ i)) = _
  rw [smul_dotProduct, smul_eq_mul, dotProduct_comm (B *ᵥ v),
    JointPrecision.dot_transpose, ← projection_eq_mulVec]

/-- Complete the square without shifting the auxiliary integration variable. -/
theorem shifted_raw_integral {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (v : Fin s → ℝ) (σ : Spin r) :
    Real.exp (-lam * normSq v) *
      (∫ t : Auxiliary s, raw B lam (σ, t) *
        Real.exp (linear ((2 * lam) • (B *ᵥ v)) (-v) (σ, t))) =
      (Fintype.card (Spin r) : ℝ)⁻¹ *
        ∏ j, CosineReference.reference lam (projection B σ j - v j) := by
  rw [integral_raw_exponential_section, shifted_source_spin]
  simp only [Pi.neg_apply, ← sub_eq_add_neg]
  have henergy : -lam * normSq v +
      (-lam * projectedEnergy B σ + 2 * lam * (projection B σ ⬝ᵥ v)) =
        -lam * normSq (projection B σ - v) := by
    have hn := JointPrecision.normSq_sub_smul (projection B σ) v 1
    simp only [one_smul, mul_one, one_pow, one_mul] at hn
    change -lam * normSq v +
      (-lam * normSq (projection B σ) + 2 * lam * (projection B σ ⬝ᵥ v)) = _
    rw [hn]
    ring
  calc
    _ = (Fintype.card (Spin r) : ℝ)⁻¹ *
        Real.exp (-lam * normSq (projection B σ - v)) *
          ∏ j, ∫ x, CosineReference.density lam x *
            Real.exp ((projection B σ j - v j) * x) := by
      rw [← henergy]
      simp only [Real.exp_add]
      ring
    _ = _ := by
      simp_rw [CosineReference.reference_eq_gaussian_times_mgf hlam]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      have he : (∑ j, -lam * (projection B σ j - v j) ^ 2) =
          -lam * normSq (projection B σ - v) := by
        simp only [normSq, Pi.sub_apply, Finset.mul_sum]
      rw [he]
      ring

/-- Equation (73), proved for the literal reference normalizer and literal law. -/
theorem translated_cell_identity {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (l : Fin s → ℤ) :
    cellMass B lam l =
      referenceNormalizer B (CosineReference.reference lam) *
        CellEnergyComparison.translatedCellIntegral (law B lam) vector B lam l := by
  let K := CellEnergyComparison.cellSet B l
  let h := CellEnergyComparison.source B lam l
  let f : Outcome r s → ℝ := fun ω => K.indicator (fun x => Real.exp (inner ℝ h x)) (vector ω)
  have hf : Integrable f (law B lam) := by
    exact (integrable_exponential_inner B hlam h).indicator
      ((CellEnergyComparison.cellSet_isClosed B l).measurableSet.preimage (measurable_vector r s))
  have hiraw := (integrable_law_iff B hlam f).1 hf
  have hZ : normalizer B lam ≠ 0 := ne_of_gt (normalizer_pos B hlam)
  symm
  calc
    _ = Real.exp (-lam * normSq (CellEnergyComparison.period l)) *
        ∫ ω, raw B lam ω * f ω ∂base r s := by
      change normalizer B lam *
        (Real.exp (-lam * normSq (CellEnergyComparison.period l)) *
          ∫ ω, f ω ∂law B lam) = _
      rw [integral_law B hlam]
      field_simp
    _ = ∑ σ : Spin r, Real.exp (-lam * normSq (CellEnergyComparison.period l)) *
        ∫ t : Auxiliary s, raw B lam (σ, t) * f (σ, t) := by
      rw [base, integral_prod _ hiraw, integral_count, Finset.mul_sum]
    _ = ∑ σ : Spin r, (Fintype.card (Spin r) : ℝ)⁻¹ *
        cellWeight lam l (projection B σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hc : InCell l (projection B σ)
      · have hi (t : Auxiliary s) : f (σ, t) = Real.exp
            (linear ((2 * lam) • (B *ᵥ CellEnergyComparison.period l))
              (-CellEnergyComparison.period l) (σ, t)) := by
          rw [show f (σ, t) = K.indicator (fun x => Real.exp (inner ℝ h x)) (vector (σ, t)) from rfl,
            Set.indicator_of_mem ((vector_mem_cell_iff B l (σ, t)).2 hc)]
          rw [show h = WithLp.toLp 2 (Sum.elim
            ((2 * lam) • (B *ᵥ CellEnergyComparison.period l))
            (-CellEnergyComparison.period l)) from rfl, inner_vector]
        simp_rw [hi]
        rw [shifted_raw_integral B hlam]
        simp only [cellWeight, hc, ite_true, shiftedProduct, CellEnergyComparison.period]
      · have hi (t : Auxiliary s) : f (σ, t) = 0 := by
          exact Set.indicator_of_notMem (mt (vector_mem_cell_iff B l (σ, t)).1 hc) _
        simp only [hi, mul_zero, integral_zero, cellWeight, hc, ite_false]
    _ = cellMass B lam l := by
      rw [← Finset.mul_sum]
      rfl

end
end TheoremA2.JointReference
