import TheoremA2.CosineReferenceBounds
import TheoremA2.Parameters

/-!
# Exact periodic-cell decomposition of the finite cosine average

Cells are chosen by the nearest integer period. Their full finite image under
the spin projection is retained; the lattice estimate will bound this image
by the complete integer lattice. No dimension or matrix restriction enters
the decomposition.
-/

namespace TheoremA2.PeriodicCells

open scoped BigOperators
noncomputable section
open Classical

def scalarError (lam : ℝ) : ℝ := 4 * Real.sqrt lam * Real.exp (-lam / 4)

def period (x : ℝ) : ℤ := ⌊x / Real.pi + 1 / 2⌋

def remainder (x : ℝ) : ℝ := x - Real.pi * period x

theorem remainder_bounds (x : ℝ) :
    -Real.pi / 2 ≤ remainder x ∧ remainder x < Real.pi / 2 := by
  have hlo := Int.floor_le (x / Real.pi + 1 / 2)
  have hhi := Int.lt_floor_add_one (x / Real.pi + 1 / 2)
  have hp := Real.pi_pos
  have hx : x / Real.pi * Real.pi = x := div_mul_cancel₀ _ (ne_of_gt hp)
  have h1 := mul_le_mul_of_nonneg_right hlo hp.le
  have h2 := mul_lt_mul_of_pos_right hhi hp
  change -Real.pi / 2 ≤ x - Real.pi * (⌊x / Real.pi + 1 / 2⌋ : ℝ) ∧
    x - Real.pi * (⌊x / Real.pi + 1 / 2⌋ : ℝ) < Real.pi / 2
  constructor <;> nlinarith

theorem abs_remainder_le (x : ℝ) : |remainder x| ≤ Real.pi / 2 :=
  abs_le.2 ⟨by linarith [(remainder_bounds x).1], (remainder_bounds x).2.le⟩

theorem period_eq_zero_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) : period x = 0 := by
  apply Int.floor_eq_zero_iff.2
  have hxp := (abs_le.1 hx).2
  have hxm := (abs_le.1 hx).1
  have hlo : -(1 / 2 : ℝ) < x / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_three]
  have hhi : x / Real.pi < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_three]
  constructor <;> linarith

theorem abs_cos_eq_remainder (x : ℝ) : |Real.cos x| = Real.cos (remainder x) := by
  have hc : 0 ≤ Real.cos (remainder x) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [(remainder_bounds x).1], (remainder_bounds x).2.le⟩
  have hcos := Real.cos_sub_int_mul_pi x (period x)
  rw [← abs_of_nonneg hc]
  change |Real.cos x| = |Real.cos (x - Real.pi * (period x : ℝ))|
  rw [mul_comm Real.pi (period x : ℝ)]
  rw [hcos, abs_mul]
  have hsign : |(-1 : ℝ) ^ period x| = 1 := by
    simpa only [Real.norm_eq_abs, norm_neg, norm_one, one_zpow] using
      (norm_zpow (-1 : ℝ) (period x))
  rw [hsign, one_mul]

def periodVector {s : ℕ} (y : Fin s → ℝ) : Fin s → ℤ := fun j => period (y j)

def Small {s : ℕ} (y : Fin s → ℝ) : Prop := ∀ j, |y j| ≤ 1

def InCell {s : ℕ} (l : Fin s → ℤ) (y : Fin s → ℝ) : Prop :=
  ∀ j, |y j - Real.pi * l j| ≤ Real.pi / 2

theorem in_selected_cell {s : ℕ} (y : Fin s → ℝ) : InCell (periodVector y) y :=
  fun j => abs_remainder_le (y j)

theorem periodVector_eq_zero_of_small {s : ℕ} {y : Fin s → ℝ} (hy : Small y) :
    periodVector y = 0 := by
  funext j
  exact period_eq_zero_of_abs_le_one (hy j)

def referenceProduct {s : ℕ} (lam : ℝ) (y : Fin s → ℝ) : ℝ :=
  ∏ j, CosineReference.reference lam (y j)

def shiftedProduct {s : ℕ} (lam : ℝ) (l : Fin s → ℤ) (y : Fin s → ℝ) : ℝ :=
  ∏ j, CosineReference.reference lam (y j - Real.pi * l j)

theorem referenceProduct_pos {s : ℕ} {lam : ℝ} (hlam : 0 < lam) (y : Fin s → ℝ) :
    0 < referenceProduct lam y := by
  exact Finset.prod_pos fun j _ => CosineReference.reference_pos hlam _

theorem shiftedProduct_pos {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (l : Fin s → ℤ) (y : Fin s → ℝ) : 0 < shiftedProduct lam l y := by
  exact Finset.prod_pos fun j _ => CosineReference.reference_pos hlam _

theorem cosineProduct_abs_le {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (y : Fin s → ℝ) :
    |∏ j, Real.cos (y j)| ≤ shiftedProduct lam (periodVector y) y := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod₀
  · intro j _
    exact abs_nonneg _
  · intro j _
    rw [abs_cos_eq_remainder]
    exact CosineReference.reference_ge_cos hlam (abs_remainder_le (y j))

theorem cosineProduct_nonneg_central {s : ℕ} {y : Fin s → ℝ}
    (hy : periodVector y = 0) : 0 ≤ ∏ j, Real.cos (y j) := by
  apply Finset.prod_nonneg
  intro j _
  have hp : period (y j) = 0 := congrFun hy j
  have hb := remainder_bounds (y j)
  simp only [remainder, hp, Int.cast_zero, mul_zero, sub_zero] at hb
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hb.1], hb.2.le⟩

theorem scalar_reference_lower {lam x : ℝ} (hlam : 2 ≤ lam) (hx : |x| ≤ 1) :
    Real.exp (-scalarError lam) * CosineReference.reference lam x ≤ Real.cos x := by
  have hf := CosineReference.reference_pos (by linarith : 0 < lam) x
  have hc : 0 < Real.cos x := lt_of_lt_of_le (by norm_num)
    (CosineReference.half_le_cos_of_abs_le_one hx)
  have he := (CosineReference.reference_log_gap hlam hx).2
  have hlog : -scalarError lam + Real.log (CosineReference.reference lam x) ≤
      Real.log (Real.cos x) := by
    dsimp [scalarError]
    linarith
  have h := Real.exp_le_exp.2 hlog
  simpa [Real.exp_add, Real.exp_log hf, Real.exp_log hc] using h

theorem cosineProduct_lower_small {s : ℕ} {lam : ℝ} (hlam : 2 ≤ lam)
    {y : Fin s → ℝ} (hy : Small y) :
    Real.exp (-(s : ℝ) * scalarError lam) * referenceProduct lam y ≤
      ∏ j, Real.cos (y j) := by
  calc
    Real.exp (-(s : ℝ) * scalarError lam) * referenceProduct lam y =
        ∏ j : Fin s, Real.exp (-scalarError lam) * CosineReference.reference lam (y j) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ _ := Finset.prod_le_prod₀
      (fun j _ => mul_nonneg (Real.exp_pos _).le
        (CosineReference.reference_pos (by linarith : 0 < lam) _).le)
      (fun j _ => scalar_reference_lower hlam (hy j))

/-- Exact pointwise separation of the small central region and every noncentral cell. -/
theorem pointwise_separation {s : ℕ} {lam : ℝ} (hlam : 2 ≤ lam)
    (y : Fin s → ℝ) :
    (if Small y then Real.exp (-(s : ℝ) * scalarError lam) * referenceProduct lam y else 0) -
      (if periodVector y ≠ 0 then shiftedProduct lam (periodVector y) y else 0) ≤
        ∏ j, Real.cos (y j) := by
  classical
  by_cases hs : Small y
  · simp only [hs, periodVector_eq_zero_of_small hs, ne_eq, not_true_eq_false,
      ite_true, ite_false, sub_zero]
    exact cosineProduct_lower_small hlam hs
  · simp only [hs, ite_false, zero_sub]
    by_cases hc : periodVector y = 0
    · simp only [hc, ne_eq, not_true_eq_false, ite_false, neg_zero]
      exact cosineProduct_nonneg_central hc
    · simp only [hc, ne_eq, not_false_eq_true, ite_true]
      have h := cosineProduct_abs_le (by linarith : 0 < lam) y
      exact (neg_le_neg h).trans (neg_abs_le _)

def projection {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (σ : Spin r) : Fin s → ℝ :=
  fun j => ∑ i, B i j * sign (σ i)

/-- Every period vector occurring in the entire finite spin space. -/
def occurringPeriods {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) : Finset (Fin s → ℤ) :=
  Finset.univ.image (fun σ : Spin r => periodVector (projection B σ))

theorem selected_period_mem {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (σ : Spin r) :
    periodVector (projection B σ) ∈ occurringPeriods B := by
  exact Finset.mem_image.2 ⟨σ, Finset.mem_univ _, rfl⟩

def cellWeight {s : ℕ} (lam : ℝ) (l : Fin s → ℤ) (y : Fin s → ℝ) : ℝ :=
  if InCell l y then shiftedProduct lam l y else 0

theorem cellWeight_nonneg {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (l : Fin s → ℤ) (y : Fin s → ℝ) : 0 ≤ cellWeight lam l y := by
  unfold cellWeight
  split_ifs
  · exact (shiftedProduct_pos hlam l y).le
  · rfl

def cellMass {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (l : Fin s → ℤ) : ℝ :=
  average (fun σ : Spin r => cellWeight lam l (projection B σ))

def goodMass {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) : ℝ :=
  average (fun σ : Spin r =>
    if Small (projection B σ) then referenceProduct lam (projection B σ) else 0)

def badMass {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) : ℝ :=
  average (fun σ : Spin r =>
    if Small (projection B σ) then 0 else referenceProduct lam (projection B σ))

def totalNoncentralMass {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) : ℝ :=
  ∑ l ∈ (occurringPeriods B).erase 0, cellMass B lam l

theorem average_finset_sum {α ι : Type*} [Fintype α] (I : Finset ι) (f : α → ι → ℝ) :
    average (fun a => ∑ i ∈ I, f a i) = ∑ i ∈ I, average (fun a => f a i) := by
  simp only [average, Finset.mul_sum]
  exact Finset.sum_comm

theorem selected_penalty_le_noncentral_sum {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) {lam : ℝ} (hlam : 0 < lam) (σ : Spin r) :
    (if periodVector (projection B σ) ≠ 0
      then shiftedProduct lam (periodVector (projection B σ)) (projection B σ) else 0) ≤
      ∑ l ∈ (occurringPeriods B).erase 0, cellWeight lam l (projection B σ) := by
  by_cases hc : periodVector (projection B σ) = 0
  · simp only [hc, ne_eq, not_true_eq_false, ite_false]
    exact Finset.sum_nonneg fun l _ => cellWeight_nonneg hlam l _
  · simp only [hc, ne_eq, not_false_eq_true, ite_true]
    have hm : periodVector (projection B σ) ∈ (occurringPeriods B).erase 0 :=
      Finset.mem_erase.2 ⟨hc, selected_period_mem B σ⟩
    have h := Finset.single_le_sum
      (fun l (_ : l ∈ (occurringPeriods B).erase 0) => cellWeight_nonneg hlam l (projection B σ)) hm
    simpa only [cellWeight, in_selected_cell, ite_true] using h

theorem goodMass_add_badMass {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) :
    goodMass B lam + badMass B lam = referenceNormalizer B (CosineReference.reference lam) := by
  rw [goodMass, badMass, ← average_add]
  apply average_congr
  intro σ
  by_cases h : Small (projection B σ) <;>
    simp [h, referenceProduct, projection]

/-- Exact finite-cell reduction. Every cell selected by a spin configuration is
present in the sum, including boundary cases of the half-open partition. -/
theorem cosine_average_lower {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 2 ≤ lam) :
    Real.exp (-(s : ℝ) * scalarError lam) * goodMass B lam - totalNoncentralMass B lam ≤
      average (fun σ : Spin r => ∏ j, Real.cos (projection B σ j)) := by
  have hpoint (σ : Spin r) :
      (if Small (projection B σ) then Real.exp (-(s : ℝ) * scalarError lam) *
        referenceProduct lam (projection B σ) else 0) -
        (∑ l ∈ (occurringPeriods B).erase 0, cellWeight lam l (projection B σ)) ≤
          ∏ j, Real.cos (projection B σ j) :=
    (sub_le_sub_left (selected_penalty_le_noncentral_sum B
      (by linarith : 0 < lam) σ) _).trans (pointwise_separation hlam (projection B σ))
  have h := average_mono hpoint
  rw [average_sub, average_finset_sum] at h
  have hgood : average (fun σ : Spin r =>
      if Small (projection B σ) then Real.exp (-(s : ℝ) * scalarError lam) *
        referenceProduct lam (projection B σ) else 0) =
      Real.exp (-(s : ℝ) * scalarError lam) * goodMass B lam := by
    rw [goodMass, ← average_const_mul]
    apply average_congr
    intro σ
    split_ifs <;> simp
  rw [hgood] at h
  exact h

/-- The algebraic final comparison, retaining its two separate analytic inputs.
They are the actual reference-weighted tail and actual translated-cell sum. -/
theorem relative_comparison_of_bounds {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {lam : ℝ} (hlam : 2 ≤ lam) {tail error : ℝ}
    (htail : badMass B lam ≤ referenceNormalizer B (CosineReference.reference lam) * tail)
    (hcells : totalNoncentralMass B lam ≤
      referenceNormalizer B (CosineReference.reference lam) * error) :
    referenceNormalizer B (CosineReference.reference lam) *
      ((1 - tail) * Real.exp (-(s : ℝ) * scalarError lam) - error) ≤
        average (fun σ : Spin r => ∏ j, Real.cos (projection B σ j)) := by
  have hg : referenceNormalizer B (CosineReference.reference lam) * (1 - tail) ≤
      goodMass B lam := by
    have hid := goodMass_add_badMass B lam
    nlinarith
  have he := mul_le_mul_of_nonneg_left hg
    (Real.exp_pos (-(s : ℝ) * scalarError lam)).le
  have hmain := cosine_average_lower B hlam
  nlinarith

end
end TheoremA2.PeriodicCells
