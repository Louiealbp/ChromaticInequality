import TheoremA2.SpinCovarianceConditional
import TheoremA2.SpinCovarianceMoments

/-!
# The exact two-copy reduction from zero field to arbitrary fields

This module proves the finite algebraic step in Proposition A.31. Its zero-field
input is explicitly a local hypothesis about the actual Gibbs law on each
principal coordinate set. `SpinCovarianceTheorems.lean` supplies the proved
zero-field analytic estimate and exports the unconditional all-field theorem.
-/

namespace TheoremA2.SpinCovariance

open TheoremA2.ConvexSupport TheoremA2.PrincipalInverse
open scoped BigOperators Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact zero-field second-moment inequality needed from Proposition A.29. -/
def ZeroFieldSecondMomentBound (N : Matrix ι ι ℝ) (c : ℝ) : Prop :=
  ∀ z : ι → ℝ,
    (spinLaw N 0).expectation (fun σ => (z ⬝ᵥ spinVector σ) ^ 2) ≤
      quadratic (N + Matrix.diagonal (fun _ => c))⁻¹ z

/-- The zero-dimensional case is a literal equality of empty quadratic forms. -/
theorem zeroFieldSecondMomentBound_empty [IsEmpty ι]
    (N : Matrix ι ι ℝ) (c : ℝ) : ZeroFieldSecondMomentBound N c := by
  intro z
  exact (empty_zero_field_second_moment N _ z).le

/-- The factor two in the conditional Gibbs energy is exactly canceled by
the half-difference covariance and the half diagonal shift. -/
theorem doubled_inverse_quadratic {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    {c : ℝ} (hc : 0 < c) (mask : ι → Bool) (z : Coordinates mask → ℝ) :
    2 * quadratic
      (doubledPrincipal N mask + Matrix.diagonal (fun _ => c))⁻¹ z =
        quadratic (principalShift N (c / 2) mask)⁻¹ z := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hp : (principalShift N (c / 2) mask).PosDef :=
    principalShift_posDef hN (by positivity) mask
  have hid : doubledPrincipal N mask + Matrix.diagonal (fun _ => c) =
      (2 : ℝ) • principalShift N (c / 2) mask := by
    ext i j
    by_cases hij : i = j
    · simp [doubledPrincipal, principalShift, hij]
      ring
    · simp [doubledPrincipal, principalShift, hij]
  rw [hid, Matrix.inv_smul (principalShift N (c / 2) mask) (2 : ℝ)
    (isUnit_iff_ne_zero.mpr (ne_of_gt hp.det_pos)), quadratic_smul]
  simp only [invOf_eq_inv]
  ring

/-- Scalar-form A.31 reduction. The hypothesis concerns actual zero-field
principal Gibbs laws and is the only analytic input. -/
theorem all_field_quadratic_of_principal_zero_field
    {N : Matrix ι ι ℝ} (hN : N.PosSemidef) {c : ℝ} (hc : 0 < c)
    (hzero : ∀ mask : ι → Bool,
      ZeroFieldSecondMomentBound (doubledPrincipal N mask) c)
    (h z : ι → ℝ) :
    quadratic (covariance (spinLaw N h) spinVector) z ≤
      quadratic (N + Matrix.diagonal (fun _ => c))⁻¹ z := by
  have hpoint (mask : ι → Bool) :
      2 * (spinLaw (doubledPrincipal N mask) 0).expectation
        (fun w => ((fun i : Coordinates mask => z i.val) ⬝ᵥ spinVector w) ^ 2) ≤
        quadratic (principalShift N (c / 2) mask)⁻¹
          (fun i : Coordinates mask => z i.val) := by
    have hh := mul_le_mul_of_nonneg_left
      (hzero mask (fun i : Coordinates mask => z i.val)) (by norm_num : (0 : ℝ) ≤ 2)
    rwa [doubled_inverse_quadratic hN hc] at hh
  have hprincipal := principal_inverse_average (maskLaw N h) hN (fun mask => mask)
    (by positivity : 0 < c / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (maskLaw_inclusion_le_half N h) z
  have hdiag : (c / 2) / (1 / 2) = c := by ring
  rw [hdiag] at hprincipal
  calc
    quadratic (covariance (spinLaw N h) spinVector) z =
        2 * (independent (spinLaw N h) (spinLaw N h)).expectation
          (fun x => (z ⬝ᵥ pairDifference x) ^ 2) :=
      quadratic_covariance_two_difference (spinLaw N h) z
    _ = 2 * (maskLaw N h).expectation (fun mask =>
        (spinLaw (doubledPrincipal N mask) 0).expectation
          (fun w => ((fun i : Coordinates mask => z i.val) ⬝ᵥ spinVector w) ^ 2)) := by
      rw [pair_expectation_disintegrate N h (fun _ v => (z ⬝ᵥ v) ^ 2)]
      simp_rw [dot_extend]
    _ = (maskLaw N h).expectation (fun mask =>
        2 * (spinLaw (doubledPrincipal N mask) 0).expectation
          (fun w => ((fun i : Coordinates mask => z i.val) ⬝ᵥ spinVector w) ^ 2)) :=
      (expectation_const_mul _ _ _).symm
    _ ≤ (maskLaw N h).expectation (fun mask =>
        quadratic (principalShift N (c / 2) mask)⁻¹
          (fun i : Coordinates mask => z i.val)) := expectation_mono _ hpoint
    _ ≤ quadratic (N + Matrix.diagonal (fun _ => c))⁻¹ z := hprincipal

/-- The literal matrix covariance inequality. It remains explicitly conditional
on the zero-field input until that input is proved from the small-diagonal bound. -/
theorem all_field_covariance_of_principal_zero_field
    {N : Matrix ι ι ℝ} (hN : N.PosSemidef) {c : ℝ} (hc : 0 < c)
    (hzero : ∀ mask : ι → Bool,
      ZeroFieldSecondMomentBound (doubledPrincipal N mask) c)
    (h : ι → ℝ) :
    ((N + Matrix.diagonal (fun _ => c))⁻¹ -
      covariance (spinLaw N h) spinVector).PosSemidef := by
  have hp : (N + Matrix.diagonal (fun _ => c)).PosDef :=
    Matrix.PosDef.posSemidef_add hN (Matrix.PosDef.diagonal (fun _ => hc))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hp.inv.isHermitian.sub (covariance_isHermitian _ _))
  intro z
  change 0 ≤ quadratic
    ((N + Matrix.diagonal (fun _ => c))⁻¹ - covariance (spinLaw N h) spinVector) z
  rw [quadratic_sub]
  exact sub_nonneg.mpr (all_field_quadratic_of_principal_zero_field hN hc hzero h z)

/-- It is enough to provide the analytic input on nonempty masks. The empty
mask is handled by its actual empty sum, not a dimension-one convention. -/
theorem all_field_covariance_of_nonempty_principal_zero_field
    {N : Matrix ι ι ℝ} (hN : N.PosSemidef) {c : ℝ} (hc : 0 < c)
    (hzero : ∀ mask : ι → Bool, Nonempty (Coordinates mask) →
      ZeroFieldSecondMomentBound (doubledPrincipal N mask) c)
    (h : ι → ℝ) :
    ((N + Matrix.diagonal (fun _ => c))⁻¹ -
      covariance (spinLaw N h) spinVector).PosSemidef := by
  apply all_field_covariance_of_principal_zero_field hN hc
  intro mask
  cases isEmpty_or_nonempty (Coordinates mask) with
  | inl he =>
      letI := he
      exact zeroFieldSecondMomentBound_empty _ _
  | inr hn => exact hzero mask hn

end

end TheoremA2.SpinCovariance
