import TheoremA2.GaussianEnvelopeRelative
import TheoremA2.GaussianEnvelopeBL
import TheoremA2.EnvelopeCramerRao
import TheoremA2.GaussianResolvent

/-!
# Lemmas A.27 and A.28 for the actual Gaussian and spin laws

The analytic inputs used by the relative comparison are discharged by the
actual Brascamp–Lieb applications. The covariance transfer then uses genuine
whole-space integration by parts, the exact Gaussian Fourier moments, and the
ordinary matrix inverse identity. The final statements have no analytic
certificate or unproved covariance premise.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal signed second-moment comparison of Claim A.27. -/
theorem signed_second_moment_comparison {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {q : ℝ} (hq : 0 < q) (hdiag : ∀ i, T i i ≤ q)
    (hcut : 2 * q / decoderBeta ≤ 1 / 1000000)
    (halpha : SpinCovariance.zeroFieldAlpha (Fintype.card ι) q < 1)
    (v : ι → ℝ) :
    |signedSecondMoment T v - (∫ x, (v ⬝ᵥ x) ^ 2 ∂envelopeLaw T)| ≤
      SpinCovariance.zeroFieldZeta (Fintype.card ι) q * quadratic T v := by
  apply signed_second_moment_comparison_of_bounds hT hq hdiag hcut halpha
  · exact envelope_mgf_le_covariance hT
  · intro U hU u
    simpa only [cellPrecision] using box_envelope_mgf hU u
  · exact box_envelope_mgf_le_covariance hT
  · exact envelope_second_moment_le_covariance hT
  · exact envelope_fourth_moment_le hT

/-- Lemma A.28 with the exact real covariance of the actual zero-field Gibbs
law, the literal inverse shifts, and the full dimension-dependent error. -/
theorem zero_field_covariance_bound {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {q : ℝ} (hq : 0 < q) (hdiag : ∀ i, T i i ≤ q)
    (hcut : 2 * q / decoderBeta ≤ 1 / 1000000)
    (halpha : SpinCovariance.zeroFieldAlpha (Fintype.card ι) q < 1)
    (z : ι → ℝ) :
    quadratic (SpinCovariance.covariance (SpinCovariance.spinLaw T 0)
      SpinCovariance.spinVector) z ≤
      quadratic (T + Matrix.diagonal (fun _ => 1 / CosineEnvelope.upperCurvature))⁻¹ z +
        SpinCovariance.zeroFieldZeta (Fintype.card ι) q * quadratic T⁻¹ z := by
  have hrelative := signed_second_moment_comparison hT hq hdiag hcut halpha (T⁻¹ *ᵥ z)
  have hlower := (abs_le.mp hrelative).1
  have hcr := envelope_cramerRao hT (T⁻¹ *ᵥ z)
  rw [integral_euclideanEnvelopeLaw] at hcr
  simp only [WithLp.ofLp_toLp] at hcr
  rw [signedSecondMoment_eq hT.posSemidef, matrix_mul_inverse_vector hT] at hlower
  change quadratic (T⁻¹ + Matrix.diagonal (fun _ => CosineEnvelope.upperCurvature))⁻¹
    (T⁻¹ *ᵥ z) ≤ _ at hcr
  have hbound : quadratic (SpinCovariance.covariance (SpinCovariance.spinLaw T 0)
      SpinCovariance.spinVector) z ≤
      quadratic T (T⁻¹ *ᵥ z) -
        quadratic (T⁻¹ + Matrix.diagonal (fun _ => CosineEnvelope.upperCurvature))⁻¹
          (T⁻¹ *ᵥ z) +
        SpinCovariance.zeroFieldZeta (Fintype.card ι) q * quadratic T (T⁻¹ *ᵥ z) := by
    linarith
  rw [quadratic_inverse_complement hT CosineEnvelope.upperCurvature_pos,
    quadratic_inverse_vector hT] at hbound
  exact hbound

end

end TheoremA2.GaussianCovariance
