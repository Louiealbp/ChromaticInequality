import TheoremA2.SpinCovarianceParameters

set_option maxHeartbeats 800000

/-!
# Uniform scalar estimates for Proposition A.29

Dimension may be arbitrarily large. The small diagonal parameter controls
`log (4*d)`, and the Gaussian errors retain the resulting dimension factors
throughout the estimates.
-/

namespace TheoremA2.SpinCovariance

open scoped BigOperators
noncomputable section

/-- Any admissible positive diagonal upper bound is smaller than the fixed cutoff. -/
theorem rho_lt_cutoff {d : ℕ} (hd : 0 < d) {rho : ℝ} (hrho : 0 < rho)
    (hsmall : rho ≤ diagonalCutoff / dimensionLog d) : rho < diagonalCutoff := by
  have hmul := (le_div_iff₀ (dimensionLog_pos hd)).1 hsmall
  have hstrict := mul_lt_mul_of_pos_left (dimensionLog_gt_one hd) hrho
  linarith

theorem dimension_bound {d : ℕ} (hd : 0 < d) {rho : ℝ} (hrho : 0 < rho)
    (hsmall : rho ≤ diagonalCutoff / dimensionLog d) :
    (d : ℝ) ≤ (1 / 4) * Real.exp (diagonalCutoff / rho) := by
  have hmul := (le_div_iff₀ (dimensionLog_pos hd)).1 hsmall
  have hlog : dimensionLog d ≤ diagonalCutoff / rho := (le_div_iff₀ hrho).2 (by nlinarith)
  have he := Real.exp_le_exp.2 hlog
  rw [exp_dimensionLog hd] at he
  linarith

/-- Both A.27–28 decoder calls, at `q=2rho` and at `2q=4rho`, meet the cutoff. -/
theorem all_decoder_cutoffs {d : ℕ} (hd : 0 < d) {rho : ℝ} (hrho : 0 < rho)
    (hsmall : rho ≤ diagonalCutoff / dimensionLog d) :
    4 * rho / decoderBeta ≤ 1 / 1000000 := by
  have hr := rho_lt_cutoff hd hrho hsmall
  norm_num [decoderBeta, diagonalCutoff] at hr ⊢
  linarith

theorem exp_neg_two_le_quarter : Real.exp (-(2 : ℝ)) ≤ 1 / 4 := by
  have hq := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by norm_num at hq; linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) h4

/-- The lattice entropy exponent is at most one uniformly for every `u≤4rho`. -/
theorem entropy_exponent_le_one {d : ℕ} (hd : 0 < d) {rho u : ℝ}
    (hrho : 0 < rho) (hsmall : rho ≤ diagonalCutoff / dimensionLog d)
    (hu : 0 < u) (hu4 : u ≤ 4 * rho) :
    16 * (d : ℝ) * Real.exp (-((1 / 100000 : ℝ) * decoderBeta) / u) ≤ 1 := by
  have hdim := dimension_bound hd hrho hsmall
  have hr := rho_lt_cutoff hd hrho hsmall
  have hquot : ((1 / 100000 : ℝ) * decoderBeta) / (4 * rho) ≤
      ((1 / 100000 : ℝ) * decoderBeta) / u := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * rho) hu).2
    norm_num [decoderBeta]
    nlinarith
  have hexponent : diagonalCutoff / rho - ((1 / 100000 : ℝ) * decoderBeta) / u ≤ -2 := by
    have hbase : diagonalCutoff / rho - ((1 / 100000 : ℝ) * decoderBeta) / (4 * rho) ≤ -2 := by
      rw [show diagonalCutoff / rho - ((1 / 100000 : ℝ) * decoderBeta) / (4 * rho) =
        (diagonalCutoff - ((1 / 100000 : ℝ) * decoderBeta) / 4) / rho by ring]
      apply (div_le_iff₀ hrho).2
      norm_num [diagonalCutoff, decoderBeta] at hr ⊢
      linarith
    linarith
  calc
    _ ≤ 16 * ((1 / 4) * Real.exp (diagonalCutoff / rho)) *
        Real.exp (-((1 / 100000 : ℝ) * decoderBeta) / u) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdim (by norm_num))
        (Real.exp_pos _).le
    _ = 4 * Real.exp (diagonalCutoff / rho - ((1 / 100000 : ℝ) * decoderBeta) / u) := by
      calc
        _ = 4 * (Real.exp (diagonalCutoff / rho) *
            Real.exp (-((1 / 100000 : ℝ) * decoderBeta) / u)) := by ring
        _ = 4 * Real.exp (diagonalCutoff / rho +
            -((1 / 100000 : ℝ) * decoderBeta) / u) := by rw [Real.exp_add]
        _ = _ := by congr 1; congr 1; ring
    _ ≤ 4 * Real.exp (-2) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexponent) (by norm_num)
    _ ≤ 1 := by linarith [exp_neg_two_le_quarter]

/-- Equation (58), retaining the complete dimension-dependent entropy term. -/
theorem latticeError_le_fast_exponential {d : ℕ} (hd : 0 < d) {rho u : ℝ}
    (hrho : 0 < rho) (hsmall : rho ≤ diagonalCutoff / dimensionLog d)
    (hu : 0 < u) (hu4 : u ≤ 4 * rho) :
    latticeError d u ≤ Real.exp (-(1 : ℝ) / (64 * rho)) := by
  have hi := entropy_exponent_le_one hd hrho hsmall hu hu4
  have hr := rho_lt_cutoff hd hrho hsmall
  have hp2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have houter : (9 : ℝ) / (320 * rho) ≤ Real.pi ^ 2 / (80 * u) := by
    calc
      (9 : ℝ) / (320 * rho) ≤ 9 / (80 * u) := by
        apply (div_le_div_iff₀ (by positivity : 0 < 320 * rho) (by positivity : 0 < 80 * u)).2
        nlinarith
      _ ≤ _ := div_le_div_of_nonneg_right hp2 (by positivity)
  have hsmallrho : 80 * rho ≤ 1 := by norm_num [diagonalCutoff] at hr; linarith
  have hrecip : 1 ≤ 1 / (80 * rho) := (one_le_div (by positivity)).2 hsmallrho
  have hcompare : -(9 : ℝ) / (320 * rho) + 1 ≤ -(1 : ℝ) / (64 * rho) := by
    have he : -(9 : ℝ) / (320 * rho) + 1 - (-(1 : ℝ) / (64 * rho)) =
        1 - 1 / (80 * rho) := by ring
    linarith
  unfold latticeError
  apply Real.exp_le_exp.2
  have hnegative : -(Real.pi ^ 2) / (80 * u) ≤ -(9 : ℝ) / (320 * rho) := by
    convert neg_le_neg houter using 1 <;> ring
  linarith

/-- The Gaussian coordinate union error, with its full dimension factor. -/
theorem zeroFieldDelta_le {d : ℕ} (hd : 0 < d) {rho : ℝ}
    (hrho : 0 < rho) (hsmall : rho ≤ diagonalCutoff / dimensionLog d) :
    zeroFieldDelta d (2 * rho) ≤ (1 / 2) * Real.exp (-(1 : ℝ) / (128 * rho)) := by
  have hdim := dimension_bound hd hrho hsmall
  have he : diagonalCutoff / rho + -(1 : ℝ) / (32 * (2 * rho)) ≤
      -(1 : ℝ) / (128 * rho) := by
    rw [show diagonalCutoff / rho + -(1 : ℝ) / (32 * (2 * rho)) =
      (diagonalCutoff - 1 / 64) / rho by ring]
    rw [show -(1 : ℝ) / (128 * rho) = (-1 / 128) / rho by ring]
    exact div_le_div_of_nonneg_right (by norm_num [diagonalCutoff]) hrho.le
  unfold zeroFieldDelta
  calc
    _ ≤ 2 * ((1 / 4) * Real.exp (diagonalCutoff / rho)) *
        Real.exp (-(1 : ℝ) / (32 * (2 * rho))) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdim (by norm_num))
        (Real.exp_pos _).le
    _ = (1 / 2) * Real.exp (diagonalCutoff / rho + -(1 : ℝ) / (32 * (2 * rho))) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 he) (by norm_num)

theorem zeroFieldAlpha_le {d : ℕ} (hd : 0 < d) {rho : ℝ}
    (hrho : 0 < rho) (hsmall : rho ≤ diagonalCutoff / dimensionLog d) :
    zeroFieldAlpha d (2 * rho) ≤ (3 / 2) * Real.exp (-(1 : ℝ) / (128 * rho)) := by
  have hdelta := zeroFieldDelta_le hd hrho hsmall
  have hlattice := latticeError_le_fast_exponential hd hrho hsmall
    (by positivity : 0 < 2 * rho) (by linarith : 2 * rho ≤ 4 * rho)
  have he : Real.exp (-(1 : ℝ) / (64 * rho)) ≤
      Real.exp (-(1 : ℝ) / (128 * rho)) := by
    apply Real.exp_le_exp.2
    apply (div_le_div_iff₀ (by positivity : 0 < 64 * rho)
      (by positivity : 0 < 128 * rho)).2
    nlinarith
  unfold zeroFieldAlpha
  linarith

theorem zeroFieldAlpha_le_three_eighths {d : ℕ} (hd : 0 < d) {rho : ℝ}
    (hrho : 0 < rho) (hsmall : rho ≤ diagonalCutoff / dimensionLog d) :
    zeroFieldAlpha d (2 * rho) ≤ 3 / 8 := by
  have ha := zeroFieldAlpha_le hd hrho hsmall
  have hr := rho_lt_cutoff hd hrho hsmall
  have harg : -(1 : ℝ) / (128 * rho) ≤ -2 := by
    apply (div_le_iff₀ (by positivity : 0 < 128 * rho)).2
    norm_num [diagonalCutoff] at hr
    linarith
  have he := (Real.exp_le_exp.2 harg).trans exp_neg_two_le_quarter
  linarith

theorem zeroFieldAlpha_lt_one {d : ℕ} (hd : 0 < d) {rho : ℝ}
    (hrho : 0 < rho) (hsmall : rho ≤ diagonalCutoff / dimensionLog d) :
    zeroFieldAlpha d (2 * rho) < 1 := by
  linarith [zeroFieldAlpha_le_three_eighths hd hrho hsmall]

theorem zeroFieldZeta_nonneg {d : ℕ} (hd : 0 < d) {rho : ℝ}
    (hrho : 0 < rho) (hsmall : rho ≤ diagonalCutoff / dimensionLog d) :
    0 ≤ zeroFieldZeta d (2 * rho) := by
  have ha := zeroFieldAlpha_lt_one hd hrho hsmall
  unfold zeroFieldZeta
  apply div_nonneg _ (by linarith)
  unfold zeroFieldAlpha zeroFieldDelta latticeError
  positivity

/-- The complete error in the second-moment estimate has the claimed uniform decay. -/
theorem zeroFieldZeta_le {d : ℕ} (hd : 0 < d) {rho : ℝ}
    (hrho : 0 < rho) (hsmall : rho ≤ diagonalCutoff / dimensionLog d) :
    zeroFieldZeta d (2 * rho) ≤ 20 * Real.exp (-(1 : ℝ) / (256 * rho)) := by
  let e := Real.exp (-(1 : ℝ) / (256 * rho))
  have hepos : 0 < e := Real.exp_pos _
  have hele : e ≤ 1 := by
    apply Real.exp_le_one_iff.2
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have heq : Real.exp (-(1 : ℝ) / (128 * rho)) = e ^ 2 := by
    dsimp [e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hdelta := zeroFieldDelta_le hd hrho hsmall
  rw [heq] at hdelta
  have hsqrt : Real.sqrt (5 * zeroFieldDelta d (2 * rho)) ≤ (8 / 5) * e := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ (8 / 5 : ℝ) * e)).2
    nlinarith [sq_nonneg e]
  have ha := zeroFieldAlpha_le hd hrho hsmall
  rw [heq] at ha
  have halinear : zeroFieldAlpha d (2 * rho) ≤ (3 / 2) * e := by
    nlinarith
  have hlattice := latticeError_le_fast_exponential hd hrho hsmall
    (by positivity : 0 < 2 * (2 * rho)) (by ring_nf; rfl : 2 * (2 * rho) ≤ 4 * rho)
  have hefast : Real.exp (-(1 : ℝ) / (64 * rho)) ≤ e := by
    apply Real.exp_le_exp.2
    apply (div_le_div_iff₀ (by positivity : 0 < 64 * rho)
      (by positivity : 0 < 256 * rho)).2
    nlinarith
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
    apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3 / 2)).2
    norm_num
  have hlatticenonneg : 0 ≤ latticeError d (2 * (2 * rho)) := by
    unfold latticeError
    positivity
  have htail : 4 * Real.sqrt 2 * latticeError d (2 * (2 * rho)) ≤ 6 * e := by
    have hfirst := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt2 (by norm_num : (0 : ℝ) ≤ 4)) hlatticenonneg
    nlinarith [hlattice.trans hefast]
  have hnum : zeroFieldAlpha d (2 * rho) + Real.sqrt (5 * zeroFieldDelta d (2 * rho)) +
      4 * Real.sqrt 2 * latticeError d (2 * (2 * rho)) ≤ 10 * e := by
    linarith
  have ha8 := zeroFieldAlpha_le_three_eighths hd hrho hsmall
  have hden : 0 < 1 - zeroFieldAlpha d (2 * rho) := by linarith
  unfold zeroFieldZeta
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The dimension and the inverse smallest eigenvalue are absorbed together.
This is equation (59), proved from a cubic lower bound on the exponential. -/
theorem zeroFieldZeta_absorption {d : ℕ} (hd : 0 < d) {rho : ℝ}
    (hrho : 0 < rho) (hsmall : rho ≤ diagonalCutoff / dimensionLog d) :
    zeroFieldZeta d (2 * rho) * ((d : ℝ) * rho + 3 + 2 / rho) < 1 / 1000 := by
  have hr := rho_lt_cutoff hd hrho hsmall
  have hr1 : rho < 1 := by norm_num [diagonalCutoff] at hr; linarith
  have hdim := dimension_bound hd hrho hsmall
  have hzet := zeroFieldZeta_le hd hrho hsmall
  have heone : 1 ≤ Real.exp (diagonalCutoff / rho) :=
    Real.one_le_exp (by unfold diagonalCutoff; positivity)
  have hdim' := mul_le_mul_of_nonneg_right hdim hrho.le
  have hconst : 3 + 2 / rho ≤ (3 + 2 / rho) * Real.exp (diagonalCutoff / rho) := by
    nlinarith only [heone, show 0 ≤ 3 + 2 / rho by positivity]
  have hfactor : (d : ℝ) * rho + 3 + 2 / rho ≤
      (rho / 4 + 3 + 2 / rho) * Real.exp (diagonalCutoff / rho) := by
    nlinarith only [hdim', hconst]
  have hfactor6 : rho / 4 + 3 + 2 / rho ≤ 6 / rho := by
    apply (le_div_iff₀ hrho).2
    have hident : (rho / 4 + 3 + 2 / rho) * rho = rho ^ 2 / 4 + 3 * rho + 2 := by
      field_simp
    rw [hident]
    have hr2 : rho ^ 2 ≤ 1 := by nlinarith only [hrho, hr1]
    nlinarith only [hr1, hr2]
  have harg : -(1 : ℝ) / (256 * rho) + diagonalCutoff / rho ≤
      -(1 : ℝ) / (512 * rho) := by
    rw [show -(1 : ℝ) / (256 * rho) + diagonalCutoff / rho =
      (diagonalCutoff - 1 / 256) / rho by ring]
    rw [show -(1 : ℝ) / (512 * rho) = (-1 / 512) / rho by ring]
    exact div_le_div_of_nonneg_right (by norm_num [diagonalCutoff]) hrho.le
  have hcubic : Real.exp (-(1 : ℝ) / (512 * rho)) ≤ 6 * 512 ^ 3 * rho ^ 3 := by
    have hp := Real.pow_div_factorial_le_exp (1 / (512 * rho))
      (by positivity : (0 : ℝ) ≤ 1 / (512 * rho)) 3
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat] at hp
    calc
      _ = 1 / Real.exp (1 / (512 * rho)) := by
        rw [show -(1 : ℝ) / (512 * rho) = -(1 / (512 * rho)) by ring]
        simp only [Real.exp_neg, one_div]
      _ ≤ 1 / ((1 / (512 * rho)) ^ 3 / 6) :=
        one_div_le_one_div_of_le (by positivity) hp
      _ = _ := by field_simp
  have hpoly : zeroFieldZeta d (2 * rho) * ((d : ℝ) * rho + 3 + 2 / rho) ≤
      720 * 512 ^ 3 * rho ^ 2 := by
    calc
      _ ≤ (20 * Real.exp (-(1 : ℝ) / (256 * rho))) *
          ((d : ℝ) * rho + 3 + 2 / rho) :=
        mul_le_mul_of_nonneg_right hzet (by positivity)
      _ ≤ (20 * Real.exp (-(1 : ℝ) / (256 * rho))) *
          ((rho / 4 + 3 + 2 / rho) * Real.exp (diagonalCutoff / rho)) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = 20 * (rho / 4 + 3 + 2 / rho) *
          Real.exp (-(1 : ℝ) / (256 * rho) + diagonalCutoff / rho) := by
        rw [Real.exp_add]
        ring
      _ ≤ 20 * (6 / rho) * Real.exp (-(1 : ℝ) / (512 * rho)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hfactor6 (by norm_num)
        · exact Real.exp_le_exp.2 harg
        · positivity
        · positivity
      _ ≤ 20 * (6 / rho) * (6 * 512 ^ 3 * rho ^ 3) :=
        mul_le_mul_of_nonneg_left hcubic (by positivity)
      _ = _ := by field_simp; ring
  have hr2 : rho ^ 2 < diagonalCutoff ^ 2 :=
    (sq_lt_sq₀ hrho.le (by norm_num [diagonalCutoff])).2 hr
  norm_num [diagonalCutoff] at hr2
  nlinarith only [hpoly, hr2]

/-- The inverse envelope curvature lies inside the exact interval needed by A.29. -/
theorem inverse_upperCurvature_bounds :
    (15 / 16 : ℝ) < 1 / CosineEnvelope.upperCurvature ∧
      1 / CosineEnvelope.upperCurvature ≤ 1 := by
  have hp := CosineEnvelope.upperCurvature_pos
  have hu := CosineEnvelope.upperCurvature_lt
  have hl : 1 ≤ CosineEnvelope.upperCurvature := by
    apply CosineEnvelope.curvature_ge_one
    norm_num
    linarith [Real.pi_gt_three]
  constructor
  · apply (lt_div_iff₀ hp).2
    nlinarith
  · exact (div_le_one hp).2 hl

/-- The scalar resolvent comparison, simultaneously uniform in all eigenvalues. -/
theorem scalar_inverse_absorption {d : ℕ} (hd : 0 < d) {rho ell : ℝ}
    (hrho : 0 < rho) (hsmall : rho ≤ diagonalCutoff / dimensionLog d)
    (hell : 0 ≤ ell) (hellupper : ell ≤ (d : ℝ) * rho) :
    1 / (ell + rho + 1 / CosineEnvelope.upperCurvature) +
        zeroFieldZeta d (2 * rho) / (ell + rho) ≤
      1 / (ell + precisionConstant) := by
  obtain ⟨hLlow, hLhigh⟩ := inverse_upperCurvature_bounds
  have hLpos : 0 < 1 / CosineEnvelope.upperCurvature := by linarith
  have hcpos : 0 < precisionConstant := by norm_num [precisionConstant]
  have hclt : precisionConstant < 1 := by norm_num [precisionConstant]
  have hzpos := zeroFieldZeta_nonneg hd hrho hsmall
  have hz := zeroFieldZeta_absorption hd hrho hsmall
  let L := 1 / CosineEnvelope.upperCurvature
  have hden : 0 < ell + rho := by positivity
  have hdenC : 0 < ell + precisionConstant := by positivity
  have hdenL : 0 < ell + rho + L := by dsimp [L]; positivity
  have hproduct : (ell + precisionConstant) * (ell + rho + L) / (ell + rho) ≤
      ell + 3 + 2 / rho := by
    have hratio : (ell + precisionConstant) / (ell + rho) ≤ 1 + precisionConstant / rho := by
      apply (div_le_iff₀ hden).2
      have hid : (1 + precisionConstant / rho) * (ell + rho) =
          ell + rho + precisionConstant + precisionConstant * ell / rho := by
        field_simp
        ring
      rw [hid]
      have hnn : 0 ≤ precisionConstant * ell / rho := by positivity
      linarith
    have hratnonneg : 0 ≤ (ell + precisionConstant) / (ell + rho) := by positivity
    have hLrat := mul_le_mul_of_nonneg_right hLhigh hratnonneg
    have hcquot : precisionConstant / rho ≤ 2 / rho :=
      div_le_div_of_nonneg_right (by norm_num [precisionConstant]) hrho.le
    have hid : (ell + precisionConstant) * (ell + rho + L) / (ell + rho) =
        ell + precisionConstant + L * ((ell + precisionConstant) / (ell + rho)) := by
      field_simp
    rw [hid]
    dsimp [L] at *
    nlinarith only [hratio, hLrat, hcquot, hclt]
  have hzproduct : zeroFieldZeta d (2 * rho) *
      ((ell + precisionConstant) * (ell + rho + L) / (ell + rho)) < 1 / 1000 := by
    have hh := mul_le_mul_of_nonneg_left hproduct hzpos
    have hm := mul_le_mul_of_nonneg_left hellupper hzpos
    nlinarith only [hh, hm, hz]
  have hmargin : (1 / 1000 : ℝ) ≤ rho + L - precisionConstant := by
    dsimp [L]
    norm_num only [precisionConstant]
    linarith only [hLlow, hrho]
  have hbound : zeroFieldZeta d (2 * rho) *
      ((ell + precisionConstant) * (ell + rho + L) / (ell + rho)) ≤
      rho + L - precisionConstant := hzproduct.le.trans hmargin
  change 1 / (ell + rho + L) + zeroFieldZeta d (2 * rho) / (ell + rho) ≤ _
  apply (le_div_iff₀ hdenC).2
  apply (mul_le_mul_iff_left₀ hdenL).mp
  have hid : ((1 / (ell + rho + L) + zeroFieldZeta d (2 * rho) / (ell + rho)) *
      (ell + precisionConstant)) * (ell + rho + L) =
      ell + precisionConstant + zeroFieldZeta d (2 * rho) *
        ((ell + precisionConstant) * (ell + rho + L) / (ell + rho)) := by
    field_simp
  rw [hid]
  linarith only [hbound]

end
end TheoremA2.SpinCovariance
