import TheoremA2.Imports

set_option maxHeartbeats 800000

/-!
# The actual padded Gaussian decoder of Lemma A.24

Every probability is constructed from its explicit, summable integer-indexed
weight. No decoder inequality or normalization is assumed.
-/

namespace TheoremA2.PaddedDecoder

open MeasureTheory ProbabilityTheory Set
open scoped Topology
noncomputable section

/-- Distance to the padded interval `[-1.6,1.6]`. -/
def paddingDistance (t : ℝ) : ℝ := max (|t| - 8 / 5) 0

/-- The unnormalized probability assigned to integer period `j`. -/
def weight (v w : ℝ) (j : ℤ) : ℝ :=
  Real.exp (-(paddingDistance (w - Real.pi * j) ^ 2) / v)

/-- The actual sum of all padded Gaussian weights. -/
def denominator (v w : ℝ) : ℝ := ∑' j : ℤ, weight v w j

/-- The decoder probability `q_v(j | w)`. -/
def probability (v : ℝ) (j : ℤ) (w : ℝ) : ℝ := weight v w j / denominator v w

/-- The actual negative log probability. -/
def loss (v : ℝ) (j : ℤ) (w : ℝ) : ℝ := -Real.log (probability v j w)

@[simp] theorem paddingDistance_neg (t : ℝ) : paddingDistance (-t) = paddingDistance t := by
  simp [paddingDistance]

theorem paddingDistance_nonneg (t : ℝ) : 0 ≤ paddingDistance t := le_max_right _ _

theorem paddingDistance_ge (t : ℝ) : |t| - 8 / 5 ≤ paddingDistance t := le_max_left _ _

theorem paddingDistance_eq_zero {t : ℝ} (ht : |t| ≤ 8 / 5) : paddingDistance t = 0 := by
  exact max_eq_right (by linarith)

theorem paddingDistance_add_le {x : ℝ} (hx : |x| ≤ 8 / 5) (n : ℝ) :
    paddingDistance (x + n) ≤ |n| := by
  apply max_le
  · linarith [abs_add_le x n]
  · exact abs_nonneg n

theorem weight_pos (v w : ℝ) (j : ℤ) : 0 < weight v w j := Real.exp_pos _

theorem weight_le_one {v : ℝ} (hv : 0 < v) (w : ℝ) (j : ℤ) : weight v w j ≤ 1 := by
  apply Real.exp_le_one_iff.2
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hv.le

@[simp] theorem weight_neg (v w : ℝ) (j : ℤ) : weight v (-w) j = weight v w (-j) := by
  unfold weight
  rw [Int.cast_neg, show -w - Real.pi * (j : ℝ) = -(w - Real.pi * (-(j : ℝ))) by ring,
    paddingDistance_neg]

theorem weight_add_period (v w : ℝ) (k j : ℤ) :
    weight v (w + Real.pi * k) (j + k) = weight v w j := by
  unfold weight
  rw [Int.cast_add]
  rw [show w + Real.pi * (k : ℝ) - Real.pi * ((j : ℝ) + (k : ℝ)) =
    w - Real.pi * (j : ℝ) by ring]

@[simp] theorem denominator_neg (v w : ℝ) : denominator v (-w) = denominator v w := by
  unfold denominator
  simp only [weight_neg]
  exact (Equiv.neg ℤ).tsum_eq _

theorem denominator_add_period (v w : ℝ) (k : ℤ) :
    denominator v (w + Real.pi * k) = denominator v w := by
  unfold denominator
  have h := (Equiv.addRight k).tsum_eq (weight v (w + Real.pi * k))
  simpa only [Equiv.coe_addRight, weight_add_period] using h.symm

/-- The geometric ratio is uniformly at most one half in the decoder range. -/
theorem ratio_le_half {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    Real.exp (-1 / v) ≤ (1 / 2 : ℝ) := by
  have hinv : 1 ≤ 1 / v := (le_div_iff₀ hv).2 (by simpa using hv1)
  have hexp : 2 ≤ Real.exp (1 / v) := by linarith [Real.add_one_le_exp (1 / v)]
  rw [show -1 / v = -(1 / v) by ring, Real.exp_neg]
  rw [inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).2 (by linarith)

/-- Sum the elementary geometric envelope. -/
theorem geometric_sum_le_two {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    Summable (fun n : ℕ => Real.exp (-1 / v) ^ n) ∧
      (∑' n : ℕ, Real.exp (-1 / v) ^ n) ≤ 2 := by
  have hr0 : 0 ≤ Real.exp (-1 / v) := (Real.exp_pos _).le
  have hr : Real.exp (-1 / v) < 1 := lt_of_le_of_lt (ratio_le_half hv hv1) (by norm_num)
  have hs := hasSum_geometric_of_norm_lt_one (show ‖Real.exp (-1 / v)‖ < 1 by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr)
  refine ⟨hs.summable, ?_⟩
  rw [hs.tsum_eq]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-1 / v))).2
  linarith [ratio_le_half hv hv1]

/-- Each successive squared Gaussian distance dominates an additional geometric step. -/
theorem weight_geometric_bound {v a : ℝ} (hv : 0 < v) (ha : 0 ≤ a) (n : ℕ) :
    Real.exp (-((a + (n : ℝ) * Real.pi) ^ 2) / v) ≤
      Real.exp (-(a ^ 2) / v) * Real.exp (-1 / v) ^ n := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    by_cases h : n = 0
    · simp [h]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      nlinarith
  have hp : (n : ℝ) ≤ (n : ℝ) * Real.pi := by nlinarith [Real.pi_gt_three]
  have hsq : a ^ 2 + (n : ℝ) ≤ (a + (n : ℝ) * Real.pi) ^ 2 := by
    have ha' : a + (n : ℝ) ≤ a + (n : ℝ) * Real.pi := by linarith
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a + (n : ℝ)) ha' 2
    nlinarith [mul_nonneg ha hn]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  calc
    -((a + (n : ℝ) * Real.pi) ^ 2) / v ≤ -(a ^ 2 + (n : ℝ)) / v :=
      div_le_div_of_nonneg_right (neg_le_neg hsq) hv.le
    _ = -(a ^ 2) / v + (n : ℝ) * (-1 / v) := by ring

/-- A nonnegative Gaussian tail family is genuinely summable, with its geometric bound. -/
theorem summable_tail_bound {v a : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (ha : 0 ≤ a)
    {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∀ n, f n ≤ Real.exp (-((a + (n : ℝ) * Real.pi) ^ 2) / v)) :
    Summable f ∧ (∑' n, f n) ≤ 2 * Real.exp (-(a ^ 2) / v) := by
  have hg := geometric_sum_le_two hv hv1
  have hb (n : ℕ) : f n ≤ Real.exp (-(a ^ 2) / v) * Real.exp (-1 / v) ^ n :=
    (hf n).trans (weight_geometric_bound hv ha n)
  have hgs := hg.1.mul_left (Real.exp (-(a ^ 2) / v))
  have hs := Summable.of_nonneg_of_le hf0 hb hgs
  refine ⟨hs, ?_⟩
  calc
    (∑' n, f n) ≤ ∑' n, Real.exp (-(a ^ 2) / v) * Real.exp (-1 / v) ^ n :=
      hs.tsum_le_tsum hb hgs
    _ = Real.exp (-(a ^ 2) / v) * (∑' n, Real.exp (-1 / v) ^ n) := tsum_mul_left
    _ ≤ 2 * Real.exp (-(a ^ 2) / v) := by
      nlinarith [mul_le_mul_of_nonneg_left hg.2 (Real.exp_pos (-(a ^ 2) / v)).le]

/-- A lower distance bound yields an upper weight bound. -/
theorem weight_le_of_distance {v w a : ℝ} (hv : 0 < v) (ha : 0 ≤ a) (j : ℤ)
    (hd : a ≤ paddingDistance (w - Real.pi * j)) :
    weight v w j ≤ Real.exp (-(a ^ 2) / v) := by
  apply Real.exp_le_exp.2
  exact div_le_div_of_nonneg_right (neg_le_neg (pow_le_pow_left₀ ha hd 2)) hv.le

/-- The two far tails are separated from every observation in `[0,π/2]`. -/
theorem central_tail_distances {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ Real.pi / 2) (n : ℕ) :
    (3 / 2 : ℝ) + n * Real.pi ≤ paddingDistance (w - Real.pi * (-(n + 1 : ℤ))) ∧
      (3 / 2 : ℝ) + n * Real.pi ≤ paddingDistance (w - Real.pi * ((n : ℤ) + 2)) := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hleft := paddingDistance_ge (w - Real.pi * (-(n + 1 : ℤ)))
  have hright := paddingDistance_ge (w - Real.pi * ((n : ℤ) + 2))
  push_cast at hleft hright ⊢
  constructor
  · have ha := le_abs_self (w - Real.pi * (-((n : ℝ) + 1)))
    nlinarith [Real.pi_gt_d2]
  · have ha := neg_le_abs (w - Real.pi * ((n : ℝ) + 2))
    nlinarith [Real.pi_gt_d2]

/-- Summability and the global denominator upper bound on the half central period. -/
theorem denominator_central_bound {v w : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ Real.pi / 2) :
    Summable (weight v w) ∧ denominator v w ≤ 2 + 4 * Real.exp (-(9 / 4 : ℝ) / v) := by
  have hneg := summable_tail_bound hv hv1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    (fun n => (weight_pos v w (-(n + 1))).le)
    (fun n => weight_le_of_distance hv (by positivity) (-(n + 1))
      (by simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one] using
        (central_tail_distances hw0 hw n).1))
  have hpos := summable_tail_bound hv hv1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    (fun n => (weight_pos v w ((n : ℤ) + 2)).le)
    (fun n => weight_le_of_distance hv (by positivity) ((n : ℤ) + 2)
      (by simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using
        (central_tail_distances hw0 hw n).2))
  have hnat : Summable (fun n : ℕ => weight v w (n : ℤ)) := by
    apply (summable_nat_add_iff 2).mp
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hpos.1
  have hs : Summable (weight v w) := Summable.of_nat_of_neg_add_one hnat hneg.1
  refine ⟨hs, ?_⟩
  unfold denominator
  rw [tsum_of_nat_of_neg_add_one hnat hneg.1, hnat.tsum_eq_zero_add]
  have hnat1 : Summable (fun n : ℕ => weight v w ((n : ℤ) + 1)) := by
    have hh := (summable_nat_add_iff 1).mpr hnat
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one]
  rw [hnat1.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one]
  have htail : (fun n : ℕ => weight v w ((n : ℤ) + 1 + 1)) =
      (fun n : ℕ => weight v w ((n : ℤ) + 2)) := by
    funext n
    congr 1
  rw [htail]
  have hpow : (3 / 2 : ℝ) ^ 2 = 9 / 4 := by norm_num
  rw [hpow] at hneg hpos
  linarith [weight_le_one hv w 0, weight_le_one hv w 1]

/-- Reflection extends the denominator estimate to the full central period. -/
theorem denominator_abs_central_bound {v w : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (hw : |w| ≤ Real.pi / 2) :
    Summable (weight v w) ∧ denominator v w ≤ 2 + 4 * Real.exp (-(9 / 4 : ℝ) / v) := by
  rcases le_total 0 w with hw0 | hw0
  · exact denominator_central_bound hv hv1 hw0 (le_trans (le_abs_self w) hw)
  · have h := denominator_central_bound hv hv1 (neg_nonneg.2 hw0)
      (le_trans (neg_le_abs w) hw)
    constructor
    · apply (Equiv.neg ℤ).summable_iff.mp
      simpa only [Function.comp_def, Equiv.neg_apply, ← weight_neg] using h.1
    · simpa only [denominator_neg] using h.2

/-- Every real observation has an integer translate in the closed central period. -/
theorem exists_central_translate (w : ℝ) :
    ∃ k : ℤ, |w - Real.pi * k| ≤ Real.pi / 2 := by
  refine ⟨round (w / Real.pi), ?_⟩
  have hp := Real.pi_pos
  have hid : w - Real.pi * (round (w / Real.pi) : ℝ) =
      Real.pi * (w / Real.pi - (round (w / Real.pi) : ℝ)) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hp]
  have hh := mul_le_mul_of_nonneg_left (abs_sub_round (w / Real.pi)) hp.le
  nlinarith

/-- Convergence and the explicit global denominator bound for every observation. -/
theorem denominator_global_bound {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (w : ℝ) :
    Summable (weight v w) ∧ denominator v w ≤ 2 + 4 * Real.exp (-(9 / 4 : ℝ) / v) := by
  obtain ⟨k, hk⟩ := exists_central_translate w
  let u := w - Real.pi * (k : ℝ)
  have hu : |u| ≤ Real.pi / 2 := hk
  have hw : w = u + Real.pi * (k : ℝ) := by dsimp [u]; ring
  have h := denominator_abs_central_bound hv hv1 hu
  rw [hw]
  constructor
  · apply (Equiv.addRight k).summable_iff.mp
    simpa only [Function.comp_def, Equiv.coe_addRight, weight_add_period] using h.1
  · simpa only [denominator_add_period] using h.2

/-- The padded central term guarantees mass at least one before normalization. -/
theorem one_le_denominator {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (w : ℝ) :
    1 ≤ denominator v w := by
  obtain ⟨k, hk⟩ := exists_central_translate w
  have hpad : paddingDistance (w - Real.pi * k) = 0 :=
    paddingDistance_eq_zero (hk.trans (by linarith [Real.pi_lt_d2]))
  have hweight : weight v w k = 1 := by simp [weight, hpad]
  rw [← hweight]
  exact (denominator_global_bound hv hv1 w).1.le_tsum k (fun j _ => (weight_pos v w j).le)

theorem denominator_pos {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (w : ℝ) :
    0 < denominator v w := lt_of_lt_of_le zero_lt_one (one_le_denominator hv hv1 w)

/-- The actual integer probabilities are strictly positive. -/
theorem probability_pos {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (j : ℤ) (w : ℝ) :
    0 < probability v j w := div_pos (weight_pos v w j) (denominator_pos hv hv1 w)

/-- Each probability is at most one, with no omitted integer tails. -/
theorem probability_le_one {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (j : ℤ) (w : ℝ) :
    probability v j w ≤ 1 := by
  apply (div_le_one (denominator_pos hv hv1 w)).2
  exact (denominator_global_bound hv hv1 w).1.le_tsum j (fun l _ => (weight_pos v w l).le)

/-- Literal normalization over every integer label. -/
theorem tsum_probability {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (w : ℝ) :
    (∑' j : ℤ, probability v j w) = 1 := by
  unfold probability
  rw [tsum_div_const]
  exact div_self (ne_of_gt (denominator_pos hv hv1 w))

theorem probability_add_period (v w : ℝ) (k j : ℤ) :
    probability v (j + k) (w + Real.pi * k) = probability v j w := by
  simp only [probability, weight_add_period, denominator_add_period]

theorem loss_add_period (v w : ℝ) (k j : ℤ) :
    loss v (j + k) (w + Real.pi * k) = loss v j w := by
  simp only [loss, probability_add_period]

/-- The loss is the exact squared-distance penalty plus the log normalizer. -/
theorem loss_eq {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (j : ℤ) (w : ℝ) :
    loss v j w = paddingDistance (w - Real.pi * j) ^ 2 / v + Real.log (denominator v w) := by
  unfold loss probability
  rw [Real.log_div (ne_of_gt (weight_pos v w j)) (ne_of_gt (denominator_pos hv hv1 w))]
  simp only [weight, Real.log_exp]
  ring

theorem loss_nonneg {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (j : ℤ) (w : ℝ) :
    0 ≤ loss v j w := by
  exact neg_nonneg.2 (Real.log_nonpos (probability_pos hv hv1 j w).le
    (probability_le_one hv hv1 j w))

/-- The denominator is a measurable limit of genuine finite weight sums. -/
theorem measurable_denominator {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    Measurable (denominator v) := by
  apply measurable_of_tendsto_metrizable' Filter.atTop
    (f := fun J : Finset ℤ => fun w : ℝ => ∑ j ∈ J, weight v w j)
  · intro J
    apply Finset.measurable_sum
    intro j _
    unfold weight paddingDistance
    fun_prop
  · apply tendsto_pi_nhds.2
    intro w
    exact (denominator_global_bound hv hv1 w).1.hasSum

theorem measurable_probability {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (j : ℤ) :
    Measurable (probability v j) := by
  apply Measurable.div _ (measurable_denominator hv hv1)
  unfold weight
  unfold paddingDistance
  fun_prop

theorem measurable_loss {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (j : ℤ) :
    Measurable (loss v j) := (measurable_probability hv hv1 j).log.neg

/-- Distance to every wrong padded interval for observations near the origin. -/
theorem small_tail_distances {w : ℝ} (hw : |w| ≤ 151 / 100) (n : ℕ) :
    (3 / 100 : ℝ) + n * Real.pi ≤ paddingDistance (w - Real.pi * ((n : ℤ) + 1)) ∧
      (3 / 100 : ℝ) + n * Real.pi ≤ paddingDistance (w - Real.pi * (-((n : ℤ) + 1))) := by
  have hleft := paddingDistance_ge (w - Real.pi * ((n : ℤ) + 1))
  have hright := paddingDistance_ge (w - Real.pi * (-((n : ℤ) + 1)))
  have hw' := abs_le.mp hw
  push_cast at hleft hright ⊢
  constructor
  · have ha := neg_le_abs (w - Real.pi * ((n : ℝ) + 1))
    linarith [Real.pi_gt_d2]
  · have ha := le_abs_self (w - Real.pi * (-((n : ℝ) + 1)))
    linarith [Real.pi_gt_d2]

/-- Near the origin, the true weight is one and all wrong weights are exponentially small. -/
theorem denominator_small_bound {v w : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (hw : |w| ≤ 151 / 100) :
    denominator v w ≤ 1 + 4 * Real.exp (-(9 / 10000 : ℝ) / v) := by
  have hpos := summable_tail_bound hv hv1 (by norm_num : (0 : ℝ) ≤ 3 / 100)
    (fun n => (weight_pos v w ((n : ℤ) + 1)).le)
    (fun n => weight_le_of_distance hv (by positivity) ((n : ℤ) + 1)
      (by simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
        (small_tail_distances hw n).1))
  have hneg := summable_tail_bound hv hv1 (by norm_num : (0 : ℝ) ≤ 3 / 100)
    (fun n => (weight_pos v w (-((n : ℤ) + 1))).le)
    (fun n => weight_le_of_distance hv (by positivity) (-((n : ℤ) + 1))
      (by simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one] using
        (small_tail_distances hw n).2))
  have hzero : weight v w 0 = 1 := by
    have hpad := paddingDistance_eq_zero (show |w| ≤ 8 / 5 by linarith)
    simp [weight, hpad]
  unfold denominator
  rw [tsum_of_add_one_of_neg_add_one hpos.1 hneg.1, hzero]
  norm_num only [show (3 / 100 : ℝ) ^ 2 = 9 / 10000 by norm_num] at hpos hneg
  linarith

/-- The deterministic small-observation loss bound used on the high-probability event. -/
theorem loss_small_observation {v w : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (hw : |w| ≤ 151 / 100) :
    loss v 0 w ≤ 4 * Real.exp (-(9 / 10000 : ℝ) / v) := by
  rw [loss_eq hv hv1]
  simp only [Int.cast_zero, mul_zero, sub_zero]
  rw [paddingDistance_eq_zero (show |w| ≤ 8 / 5 by linarith)]
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, zero_add]
  linarith [Real.log_le_sub_one_of_pos (denominator_pos hv hv1 w),
    denominator_small_bound hv hv1 hw]

/-- A sharp enough global logarithmic normalizer bound, including the boundary ambiguity. -/
theorem log_denominator_le {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (w : ℝ) :
    Real.log (denominator v w) ≤ Real.log 2 + 2 * Real.exp (-(9 / 4 : ℝ) / v) := by
  have h := Real.log_le_sub_one_of_pos
    (div_pos (denominator_pos hv hv1 w) (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div (ne_of_gt (denominator_pos hv hv1 w)) (by norm_num)] at h
  linarith [(denominator_global_bound hv hv1 w).2]

/-- The global denominator is at most three throughout the actual decoder range. -/
theorem denominator_le_three {v : ℝ} (hv : 0 < v) (hvsmall : v ≤ 1 / 1000000) (w : ℝ) :
    denominator v w ≤ 3 := by
  have hv1 : v ≤ 1 := by linarith
  have hx : (7 : ℝ) ≤ (9 / 4 : ℝ) / v := (le_div_iff₀ hv).2 (by linarith)
  have he : 8 ≤ Real.exp ((9 / 4 : ℝ) / v) := by
    linarith [Real.add_one_le_exp ((9 / 4 : ℝ) / v)]
  have hinv : Real.exp (-(9 / 4 : ℝ) / v) ≤ 1 / 8 := by
    rw [show -(9 / 4 : ℝ) / v = -((9 / 4 : ℝ) / v) by ring, Real.exp_neg,
      inv_eq_one_div]
    exact (div_le_iff₀ (Real.exp_pos _)).2 (by linarith)
  linarith [(denominator_global_bound hv hv1 w).2]

/-- A global quadratic domination of the actual loss, valid also for zero noise variance. -/
theorem loss_scaled_noise_le_cost {v x s : ℝ} (hv : 0 < v)
    (hvsmall : v ≤ 1 / 1000000) (hx : |x| ≤ Real.pi / 2)
    (hsq : s ^ 2 ≤ v) (z : ℝ) :
    loss v 0 (x + s * z) ≤ z ^ 2 + Real.log 3 := by
  have hv1 : v ≤ 1 := by linarith
  have hxpad : |x| ≤ 8 / 5 := hx.trans (by linarith [Real.pi_lt_d2])
  have hd := paddingDistance_add_le hxpad (s * z)
  have hdsq := pow_le_pow_left₀ (paddingDistance_nonneg (x + s * z)) hd 2
  rw [sq_abs, mul_pow] at hdsq
  have hssq := mul_le_mul_of_nonneg_right hsq (sq_nonneg z)
  have hpenalty : paddingDistance (x + s * z) ^ 2 / v ≤ z ^ 2 := by
    apply (div_le_iff₀ hv).2
    nlinarith
  have hlog : Real.log (denominator v (x + s * z)) ≤ Real.log 3 :=
    Real.log_le_log (denominator_pos hv hv1 _) (denominator_le_three hv hvsmall _)
  rw [loss_eq hv hv1]
  simp only [Int.cast_zero, mul_zero, sub_zero]
  linarith

end
end TheoremA2.PaddedDecoder
