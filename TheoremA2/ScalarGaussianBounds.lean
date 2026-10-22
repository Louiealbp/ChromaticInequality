import TheoremA2.Imports

set_option maxHeartbeats 800000

/-!
# Explicit scalar Gaussian estimates for the cosine reference

The tail estimate is proved by integrating the derivative of the Gaussian,
and the normalizer estimate by integrating a positive lower bound on a
concrete central interval. All integrals are Lebesgue integrals on `ℝ`.
-/

namespace TheoremA2.ScalarGaussianBounds

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- The Gaussian first moment on a half-line, obtained from its actual primitive. -/
theorem integral_mul_gaussian_Ioi {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    (∫ x in Ioi a, x * Real.exp (-lam * x ^ 2)) =
      Real.exp (-lam * a ^ 2) / (2 * lam) := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun x : ℝ => -(2 * lam)⁻¹ * Real.exp (-lam * x ^ 2))
        (x * Real.exp (-lam * x ^ 2)) x := by
    convert (((hasDerivAt_pow 2 x).const_mul (-lam)).exp.const_mul (-(2 * lam)⁻¹)) using 1
    field_simp
    ring
  have ht : Tendsto (fun x : ℝ => -(2 * lam)⁻¹ * Real.exp (-lam * x ^ 2))
      atTop (𝓝 (-(2 * lam)⁻¹ * 0)) := by
    apply Tendsto.const_mul
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hlam))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := a) (fun x _ => hderiv x)
    (integrable_mul_exp_neg_mul_sq hlam).integrableOn ht
  simpa [div_eq_mul_inv, mul_comm] using h

/-- The one-sided tail at `1/2`, with the sharper factor `1/lam`. -/
theorem gaussian_tail_half_one_sided {lam : ℝ} (hlam : 0 < lam) :
    (∫ x in Ioi (1 / 2 : ℝ), Real.exp (-lam * x ^ 2)) ≤
      Real.exp (-lam / 4) / lam := by
  have h := setIntegral_mono_on
    (integrable_exp_neg_mul_sq hlam).integrableOn
    ((integrable_mul_exp_neg_mul_sq hlam).const_mul 2).integrableOn
    measurableSet_Ioi (fun x hx => show Real.exp (-lam * x ^ 2) ≤
      2 * (x * Real.exp (-lam * x ^ 2)) from by
      have hpos := Real.exp_pos (-lam * x ^ 2)
      have hx' : (1 / 2 : ℝ) < x := hx
      nlinarith)
  rw [integral_const_mul, integral_mul_gaussian_Ioi hlam] at h
  rw [show -lam * (1 / 2 : ℝ) ^ 2 = -lam / 4 by ring] at h
  convert h using 1
  ring

/-- The two-sided Gaussian tail estimate used for the scalar cosine reference. -/
theorem gaussian_tail_half {lam : ℝ} (hlam : 2 ≤ lam) :
    (∫ x in {x : ℝ | (1 / 2 : ℝ) ≤ |x|}, Real.exp (-lam * x ^ 2)) ≤
      Real.exp (-lam / 4) := by
  have hlampos : 0 < lam := by linarith
  have hset : {x : ℝ | (1 / 2 : ℝ) ≤ |x|} =
      Iic (-(1 / 2 : ℝ)) ∪ Ici (1 / 2 : ℝ) := by
    ext x
    constructor
    · intro hx
      change (1 / 2 : ℝ) ≤ |x| at hx
      rcases le_total x 0 with hx0 | hx0
      · left
        change x ≤ -(1 / 2 : ℝ)
        rw [abs_of_nonpos hx0] at hx
        linarith
      · right
        simpa [abs_of_nonneg hx0] using hx
    · rintro (hx | hx)
      · change x ≤ -(1 / 2 : ℝ) at hx
        change (1 / 2 : ℝ) ≤ |x|
        linarith [neg_le_abs x]
      · exact le_trans hx (le_abs_self x)
  have hdisj : Disjoint (Iic (-(1 / 2 : ℝ))) (Ici (1 / 2 : ℝ)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : x ≤ -(1 / 2 : ℝ) := hx
    have hy' : (1 / 2 : ℝ) ≤ x := hy
    linarith only [hx', hy']
  have hsymm : (∫ x in Iic (-(1 / 2 : ℝ)), Real.exp (-lam * x ^ 2)) =
      ∫ x in Ioi (1 / 2 : ℝ), Real.exp (-lam * x ^ 2) := by
    have h := integral_comp_neg_Iic (E := ℝ) (-(1 / 2 : ℝ))
      (fun x : ℝ => Real.exp (-lam * x ^ 2))
    simp only [neg_sq, neg_neg] at h
    exact h
  rw [hset, setIntegral_union hdisj measurableSet_Ici
    (integrable_exp_neg_mul_sq hlampos).integrableOn
    (integrable_exp_neg_mul_sq hlampos).integrableOn,
    hsymm, integral_Ici_eq_integral_Ioi]
  have h := gaussian_tail_half_one_sided hlampos
  have hfac : 2 / lam ≤ (1 : ℝ) := (div_le_one hlampos).mpr hlam
  have he := Real.exp_pos (-lam / 4)
  have hmul := mul_le_mul_of_nonneg_right hfac he.le
  calc
    _ ≤ Real.exp (-lam / 4) / lam + Real.exp (-lam / 4) / lam := add_le_add h h
    _ = (2 / lam) * Real.exp (-lam / 4) := by ring
    _ ≤ Real.exp (-lam / 4) := by simpa only [one_mul] using hmul

/-- A pointwise lower bound on the central interval of radius `1/(2 sqrt lam)`. -/
theorem gaussian_cosine_central_lower {lam x : ℝ} (hlam : 2 ≤ lam)
    (hx : |x| ≤ 1 / (2 * Real.sqrt lam)) :
    (1 / 2 : ℝ) ≤ Real.exp (-lam * x ^ 2) * Real.cos x := by
  have hlampos : 0 < lam := by linarith
  have hspos := Real.sqrt_pos.mpr hlampos
  have hsone : 1 ≤ Real.sqrt lam := by
    have hs := Real.sq_sqrt hlampos.le
    nlinarith [Real.sqrt_nonneg lam]
  have hrle : 1 / (2 * Real.sqrt lam) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt lam)).mpr
    nlinarith
  have hxsq : x ^ 2 ≤ (1 / (2 * Real.sqrt lam)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hrid : lam * (1 / (2 * Real.sqrt lam)) ^ 2 = (1 / 4 : ℝ) := by
    calc
      _ = (Real.sqrt lam) ^ 2 * (1 / (2 * Real.sqrt lam)) ^ 2 := by
        rw [Real.sq_sqrt hlampos.le]
      _ = _ := by field_simp [ne_of_gt hspos]; ring
  have hlxsq : lam * x ^ 2 ≤ (1 / 4 : ℝ) := by
    calc
      _ ≤ lam * (1 / (2 * Real.sqrt lam)) ^ 2 :=
        mul_le_mul_of_nonneg_left hxsq hlampos.le
      _ = _ := hrid
  have hsmall : x ^ 2 ≤ (1 / 4 : ℝ) := by
    have hh := pow_le_pow_left₀ (abs_nonneg x) (hx.trans hrle) 2
    norm_num only [sq_abs] at hh
    nlinarith
  have hexp : (3 / 4 : ℝ) ≤ Real.exp (-lam * x ^ 2) := by
    nlinarith [Real.add_one_le_exp (-lam * x ^ 2)]
  have hcos : (7 / 8 : ℝ) ≤ Real.cos x := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  calc
    (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) * (7 / 8 : ℝ) := by norm_num
    _ ≤ Real.exp (-lam * x ^ 2) * Real.cos x :=
      mul_le_mul hexp hcos (by norm_num) (Real.exp_pos _).le

/-- A quantitative lower bound for the actual truncated Gaussian-cosine normalizer. -/
theorem gaussian_cosine_normalizer_lower {lam : ℝ} (hlam : 2 ≤ lam) :
    1 / (2 * Real.sqrt lam) ≤
      ∫ x in Icc (-(Real.pi / 2)) (Real.pi / 2),
        Real.exp (-lam * x ^ 2) * Real.cos x := by
  let r : ℝ := 1 / (2 * Real.sqrt lam)
  have hlampos : 0 < lam := by linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hsone : 1 ≤ Real.sqrt lam := by
    have hs := Real.sq_sqrt hlampos.le
    nlinarith [Real.sqrt_nonneg lam]
  have hrle : r ≤ Real.pi / 2 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt lam)).mpr
    have hpi := Real.pi_gt_three
    nlinarith
  have hc : Continuous (fun x : ℝ => Real.exp (-lam * x ^ 2) * Real.cos x) := by
    fun_prop
  have hsmall := setIntegral_ge_of_const_le
    (s := Icc (-r) r) (μ := volume) (c := (1 / 2 : ℝ)) measurableSet_Icc
    (by simp : volume (Icc (-r) r) ≠ ⊤)
    (fun x hx => gaussian_cosine_central_lower hlam (abs_le.mpr ⟨hx.1, hx.2⟩))
    hc.integrableOn_Icc
  rw [Real.volume_real_Icc_of_le (by linarith : -r ≤ r)] at hsmall
  have hsubset : Icc (-r) r ⊆ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (-(Real.pi / 2)) (Real.pi / 2))]
      (fun x : ℝ => Real.exp (-lam * x ^ 2) * Real.cos x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc hx)
  have hlarge : (∫ x in Icc (-r) r, Real.exp (-lam * x ^ 2) * Real.cos x) ≤
      ∫ x in Icc (-(Real.pi / 2)) (Real.pi / 2),
        Real.exp (-lam * x ^ 2) * Real.cos x :=
    setIntegral_mono_set hc.integrableOn_Icc hnonneg
      (Filter.Eventually.of_forall hsubset)
  change r ≤ _
  simp only [smul_eq_mul] at hsmall
  linarith only [hsmall, hlarge]

end

end TheoremA2.ScalarGaussianBounds
