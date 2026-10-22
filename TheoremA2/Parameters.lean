import TheoremA2.Imports
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exact constants in Theorem A.2

The angle is `a / (sqrt k * log (4*k))`.  In particular the logarithm is
outside the square root.  All decimals below are exact rational numbers.
This file proves the scalar facts used in the final unrestricted analytic
comparison and its exact lower bound.
-/

namespace TheoremA2

noncomputable section

def amplitude : ℝ := 1 / 10000000

def dimensionLog (k : ℕ) : ℝ := Real.log (4 * (k : ℝ))

def theta (k : ℕ) : ℝ := amplitude / (Real.sqrt (k : ℝ) * dimensionLog k)

def referenceLambda (k : ℕ) : ℝ := 64 * dimensionLog k

def rowVariance (k : ℕ) : ℝ := amplitude ^ 2 / dimensionLog k ^ 2

def precisionConstant : ℝ := 93 / 100

def decoderBeta : ℝ := 9 / 10

def diagonalCutoff : ℝ := 1 / 10000000000

def referenceError (k : ℕ) : ℝ :=
  4 * Real.sqrt (referenceLambda k) * Real.exp (-(referenceLambda k) / 4)

def latticeError (d : ℕ) (q : ℝ) : ℝ :=
  Real.exp (-(Real.pi ^ 2) / (80 * q) +
    16 * (d : ℝ) * Real.exp (-((1 / 100000 : ℝ) * decoderBeta) / q))

def lowerBound (k : ℕ) : ℝ :=
  (1 / 4) * Real.exp (-(64 * amplitude ^ 2 * (k : ℝ)) / dimensionLog k)

theorem amplitude_pos : 0 < amplitude := by norm_num [amplitude]

theorem dimensionLog_gt_one {k : ℕ} (hk : 0 < k) : 1 < dimensionLog k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  apply (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < 4 * k)).2
  have h := Real.exp_one_lt_d9
  linarith

theorem dimensionLog_pos {k : ℕ} (hk : 0 < k) : 0 < dimensionLog k :=
  lt_trans zero_lt_one (dimensionLog_gt_one hk)

theorem dimensionLog_ne_zero {k : ℕ} (hk : 0 < k) : dimensionLog k ≠ 0 :=
  ne_of_gt (dimensionLog_pos hk)

theorem exp_dimensionLog {k : ℕ} (hk : 0 < k) :
    Real.exp (dimensionLog k) = 4 * (k : ℝ) := by
  exact Real.exp_log (by positivity)

theorem theta_pos {k : ℕ} (hk : 0 < k) : 0 < theta k := by
  unfold theta
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  exact div_pos amplitude_pos (mul_pos (Real.sqrt_pos.2 hkR) (dimensionLog_pos hk))

theorem rowVariance_pos {k : ℕ} (hk : 0 < k) : 0 < rowVariance k := by
  unfold rowVariance
  exact div_pos (sq_pos_of_pos amplitude_pos) (sq_pos_of_pos (dimensionLog_pos hk))

theorem k_mul_theta_sq {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * theta k ^ 2 = rowVariance k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hkR)
  have hL := dimensionLog_ne_zero hk
  unfold theta rowVariance
  rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hkR)]
  field_simp

theorem referenceLambda_ge_two {k : ℕ} (hk : 0 < k) :
    2 ≤ referenceLambda k := by
  have h := dimensionLog_gt_one hk
  unfold referenceLambda
  linarith

theorem spin_diagonal_cutoff {k : ℕ} (hk : 0 < k) :
    4 * referenceLambda k * rowVariance k ≤ diagonalCutoff / dimensionLog k := by
  have hL := dimensionLog_pos hk
  have hL0 := ne_of_gt hL
  unfold referenceLambda rowVariance diagonalCutoff amplitude
  field_simp
  nlinarith

theorem lowerBound_pos (k : ℕ) : 0 < lowerBound k := by
  unfold lowerBound
  positivity

theorem lowerBound_le_quarter {k : ℕ} (hk : 0 < k) : lowerBound k ≤ 1 / 4 := by
  have hL := dimensionLog_pos hk
  have hex : Real.exp (-(64 * amplitude ^ 2 * (k : ℝ)) / dimensionLog k) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · have : 0 ≤ 64 * amplitude ^ 2 * (k : ℝ) := by positivity
      linarith
    · exact hL.le
  unfold lowerBound
  nlinarith

theorem rowVariance_le_amplitude_sq {k : ℕ} (hk : 0 < k) :
    rowVariance k ≤ amplitude ^ 2 := by
  have hL := dimensionLog_gt_one hk
  unfold rowVariance
  apply (div_le_iff₀ (sq_pos_of_pos (dimensionLog_pos hk))).2
  have hsq : 1 ≤ dimensionLog k ^ 2 := by nlinarith
  nlinarith [sq_nonneg amplitude]

theorem decoder_variance_cutoff {k : ℕ} (hk : 0 < k) :
    rowVariance k / (decoderBeta * precisionConstant) ≤ (1 / 1000000 : ℝ) := by
  have hr := rowVariance_le_amplitude_sq hk
  norm_num [decoderBeta, precisionConstant, amplitude] at hr ⊢
  linarith

theorem exp_neg_two_dimensionLog {k : ℕ} (hk : 0 < k) :
    Real.exp (-(2 * dimensionLog k)) = 1 / (16 * (k : ℝ) ^ 2) := by
  rw [Real.exp_neg, show (2 : ℝ) = (2 : ℕ) from rfl,
    Real.exp_nat_mul, exp_dimensionLog hk]
  ring

theorem exponent_ge_two_log {k : ℕ} (hk : 0 < k) {d : ℝ}
    (hd : 2 * amplitude ^ 2 ≤ d) :
    2 * dimensionLog k ≤ d / rowVariance k := by
  have hL := dimensionLog_gt_one hk
  have hLp := dimensionLog_pos hk
  have ha := sq_pos_of_pos amplitude_pos
  have hsq : dimensionLog k ≤ dimensionLog k ^ 2 := by nlinarith
  have hd0 : 0 ≤ d := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hd0
  have hmul' := mul_le_mul_of_nonneg_right hd hLp.le
  have hratio : d / rowVariance k = d * dimensionLog k ^ 2 / amplitude ^ 2 := by
    unfold rowVariance
    field_simp
  rw [hratio]
  apply (le_div_iff₀ ha).2
  nlinarith

/-- The first error term in equation (76) is at most one quarter. -/
theorem central_tail_error_le_quarter {k : ℕ} (hk : 0 < k) :
    2 * (k : ℝ) * Real.exp (-precisionConstant / (2 * rowVariance k)) ≤ 1 / 4 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hexp := exponent_ge_two_log hk
    (d := precisionConstant / 2) (by norm_num [precisionConstant, amplitude])
  have he : Real.exp (-precisionConstant / (2 * rowVariance k)) ≤
      Real.exp (-(2 * dimensionLog k)) := by
    apply Real.exp_le_exp.mpr
    have hid : -precisionConstant / (2 * rowVariance k) =
        -(precisionConstant / 2 / rowVariance k) := by ring
    rw [hid]
    linarith
  calc
    2 * (k : ℝ) * Real.exp (-precisionConstant / (2 * rowVariance k)) ≤
        2 * k * (1 / (16 * (k : ℝ) ^ 2)) := by
      rw [← exp_neg_two_dimensionLog hk]
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = 1 / (8 * (k : ℝ)) := by field_simp; ring
    _ ≤ 1 / 4 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * k)).2
      linarith

/-- The lattice error appearing in equation (76) is at most one quarter. -/
theorem lattice_error_le_quarter {k : ℕ} (hk : 0 < k) :
    latticeError k (rowVariance k / precisionConstant) ≤ 1 / 4 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have houter := exponent_ge_two_log hk
    (d := precisionConstant * Real.pi ^ 2 / 80) (by
      norm_num [precisionConstant, amplitude]
      nlinarith)
  have hinner := exponent_ge_two_log hk
    (d := (1 / 100000 : ℝ) * decoderBeta * precisionConstant)
    (by norm_num [precisionConstant, decoderBeta, amplitude])
  have hr0 := ne_of_gt (rowVariance_pos hk)
  have hc0 : precisionConstant ≠ 0 := by norm_num [precisionConstant]
  have hid1 : -(Real.pi ^ 2) / (80 * (rowVariance k / precisionConstant)) =
      -(precisionConstant * Real.pi ^ 2 / 80 / rowVariance k) := by field_simp
  have hid2 : -((1 / 100000 : ℝ) * decoderBeta) /
      (rowVariance k / precisionConstant) =
      -((1 / 100000 : ℝ) * decoderBeta * precisionConstant / rowVariance k) := by
    field_simp
  have hi : Real.exp (-((1 / 100000 : ℝ) * decoderBeta) /
      (rowVariance k / precisionConstant)) ≤ 1 / (16 * (k : ℝ) ^ 2) := by
    rw [← exp_neg_two_dimensionLog hk, hid2]
    exact Real.exp_le_exp.mpr (by linarith)
  have hit : 16 * (k : ℝ) * Real.exp (-((1 / 100000 : ℝ) * decoderBeta) /
      (rowVariance k / precisionConstant)) ≤ 1 := by
    calc
      _ ≤ 16 * k * (1 / (16 * (k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = 1 / (k : ℝ) := by field_simp
      _ ≤ 1 := (div_le_one hkR).2 hk1
  unfold latticeError
  calc
    _ ≤ Real.exp (1 - 2 * dimensionLog k) := by
      apply Real.exp_le_exp.mpr
      rw [hid1]
      linarith
    _ = Real.exp 1 / (16 * (k : ℝ) ^ 2) := by
      rw [sub_eq_add_neg, Real.exp_add, exp_neg_two_dimensionLog hk]
      ring
    _ ≤ 1 / 4 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (k : ℝ) ^ 2)).2
      have h := Real.exp_one_lt_d9
      nlinarith

/-- A coarse exact bound suffices for the reference approximation error. -/
theorem reference_error_cost_le_eighth {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * referenceError k ≤ 1 / 8 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hL := dimensionLog_gt_one hk
  have hLp := dimensionLog_pos hk
  have hs : Real.sqrt (referenceLambda k) ≤ 8 * dimensionLog k := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · unfold referenceLambda
      nlinarith
  have hLe : dimensionLog k ≤ Real.exp (dimensionLog k) := by
    have h := Real.add_one_le_exp (dimensionLog k)
    linarith
  have hse : Real.sqrt (referenceLambda k) ≤ 8 * Real.exp (dimensionLog k) := by
    linarith
  have he : referenceError k ≤ 32 * Real.exp (-(4 * dimensionLog k)) := by
    calc
      referenceError k ≤
          32 * Real.exp (dimensionLog k) * Real.exp (-(referenceLambda k) / 4) := by
        unfold referenceError
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 32 * Real.exp (-(15 * dimensionLog k)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        unfold referenceLambda
        congr 1
        ring
      _ ≤ 32 * Real.exp (-(4 * dimensionLog k)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.exp_le_exp.mpr (by linarith)
  have hex : Real.exp (-(4 * dimensionLog k)) = 1 / (256 * (k : ℝ) ^ 4) := by
    rw [Real.exp_neg, show (4 : ℝ) = (4 : ℕ) from rfl,
      Real.exp_nat_mul, exp_dimensionLog hk]
    ring
  calc
    (k : ℝ) * referenceError k ≤
        k * (32 * (1 / (256 * (k : ℝ) ^ 4))) := by
      rw [← hex]
      exact mul_le_mul_of_nonneg_left he hkR.le
    _ = 1 / (8 * (k : ℝ) ^ 3) := by field_simp; ring
    _ ≤ 1 / 8 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (k : ℝ) ^ 3)).2
      have hpow : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hk1
      linarith

theorem reference_error_factor_ge_two_thirds {k : ℕ} (hk : 0 < k) :
    (2 / 3 : ℝ) ≤ Real.exp (-((k : ℝ) * referenceError k)) := by
  have hcost := reference_error_cost_le_eighth hk
  have hex := Real.one_sub_le_exp_neg ((k : ℝ) * referenceError k)
  linarith

def comparisonBracket (k : ℕ) : ℝ :=
  (1 - 2 * (k : ℝ) * Real.exp (-precisionConstant / (2 * rowVariance k))) *
      Real.exp (-((k : ℝ) * referenceError k)) -
    latticeError k (rowVariance k / precisionConstant)

/-- This is the numerical bracket in equation (76), with all errors substituted. -/
theorem comparisonBracket_ge_quarter {k : ℕ} (hk : 0 < k) :
    (1 / 4 : ℝ) ≤ comparisonBracket k := by
  have ht := central_tail_error_le_quarter hk
  have hf := reference_error_factor_ge_two_thirds hk
  have hl := lattice_error_le_quarter hk
  have hp : (3 / 4 : ℝ) * (2 / 3 : ℝ) ≤
      (1 - 2 * (k : ℝ) * Real.exp (-precisionConstant / (2 * rowVariance k))) *
      Real.exp (-((k : ℝ) * referenceError k)) := by
    apply mul_le_mul
    · linarith
    · exact hf
    · norm_num
    · linarith
  unfold comparisonBracket
  linarith

theorem normalizer_exponent_eq {k : ℕ} (hk : 0 < k) :
    -(referenceLambda k * ((k : ℝ) * rowVariance k)) =
      -(64 * amplitude ^ 2 * (k : ℝ)) / dimensionLog k := by
  have hL := dimensionLog_ne_zero hk
  unfold referenceLambda rowVariance
  field_simp

end

end TheoremA2
