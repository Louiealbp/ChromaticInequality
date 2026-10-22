import TheoremA2.SpinCovarianceParameters

/-! Exact normalization algebra for the signed moment comparison in A.27. -/

namespace TheoremA2.GaussianCovariance

noncomputable section

theorem relative_second_moment_algebra {A Z I m w alpha error : ℝ}
    (hZ : 0 < Z) (hI : 0 < I) (hw : 0 ≤ w)
    (hm0 : 0 ≤ m) (hmw : m ≤ w)
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (he0 : 0 ≤ error)
    (hnormalizer : |Z - I| ≤ alpha * I)
    (hmoment : |A - I * m| ≤ error * I * w) :
    |A / Z - m| ≤ ((alpha + error) / (1 - alpha)) * w := by
  have hden : 0 < 1 - alpha := by linarith
  have hZlower : (1 - alpha) * I ≤ Z := by
    have hl := (abs_le.mp hnormalizer).1
    nlinarith
  have hcoef : 0 ≤ (alpha + error) / (1 - alpha) :=
    div_nonneg (add_nonneg ha0 he0) hden.le
  have hnum : |A - Z * m| ≤ (alpha + error) * I * w := by
    have heq : A - Z * m = (A - I * m) + (I - Z) * m := by ring
    rw [heq]
    calc
      _ ≤ |A - I * m| + |(I - Z) * m| := abs_add_le _ _
      _ = |A - I * m| + |Z - I| * m := by
        rw [abs_mul, abs_sub_comm I Z, abs_of_nonneg hm0]
      _ ≤ error * I * w + (alpha * I) * w := by
        apply add_le_add hmoment
        exact (mul_le_mul_of_nonneg_right hnormalizer hm0).trans
          (mul_le_mul_of_nonneg_left hmw (mul_nonneg ha0 hI.le))
      _ = _ := by ring
  have heq : A / Z - m = (A - Z * m) / Z := by
    field_simp
  rw [heq, abs_div, abs_of_pos hZ]
  apply (div_le_iff₀ hZ).mpr
  calc
    _ ≤ (alpha + error) * I * w := hnum
    _ = ((alpha + error) / (1 - alpha)) * w * ((1 - alpha) * I) := by
      field_simp [ne_of_gt hden]
    _ ≤ ((alpha + error) / (1 - alpha)) * w * Z :=
      mul_le_mul_of_nonneg_left hZlower (mul_nonneg hcoef hw)

end

end TheoremA2.GaussianCovariance
