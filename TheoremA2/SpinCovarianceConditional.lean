import TheoremA2.SpinCovarianceBasic

/-!
# Exact disagreement-conditioned zero-field law

The two independent Gibbs samples are reindexed by their disagreement mask
and their first spin. Splitting that first spin into the mask and its complement
factors the actual exponential weights. No conditional distribution is assumed.
-/

namespace TheoremA2.SpinCovariance

open TheoremA2.ConvexSupport TheoremA2.PrincipalInverse
open scoped BigOperators Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complementMask (mask : ι → Bool) : ι → Bool := fun i => !(mask i)

def restrictSpin (mask : ι → Bool) (σ : SpinConfig ι) : SpinConfig (Coordinates mask) :=
  fun i => σ i.val

def flipOn (mask : ι → Bool) (σ : SpinConfig ι) : SpinConfig ι :=
  fun i => if mask i then !(σ i) else σ i

def pairOfMask (mask : ι → Bool) (σ : SpinConfig ι) :
    SpinConfig ι × SpinConfig ι := (σ, flipOn mask σ)

omit [Fintype ι] [DecidableEq ι] in
theorem disagreement_pairOfMask (mask : ι → Bool) (σ : SpinConfig ι) :
    disagreement (pairOfMask mask σ) = mask := by
  funext i
  cases hm : mask i <;> cases hs : σ i <;>
    simp [disagreement, pairOfMask, flipOn, hm, hs]

def pairMaskEquiv : (SpinConfig ι × SpinConfig ι) ≃ (SpinConfig ι × SpinConfig ι) where
  toFun x := (disagreement x, x.1)
  invFun x := pairOfMask x.1 x.2
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      cases hσ : x.1 i <;> cases hτ : x.2 i <;>
        simp [pairOfMask, flipOn, disagreement, hσ, hτ]
  right_inv x := by
    apply Prod.ext
    · exact disagreement_pairOfMask x.1 x.2
    · rfl

theorem sum_pairs_by_mask (f : SpinConfig ι × SpinConfig ι → ℝ) :
    (∑ x, f x) = ∑ mask : SpinConfig ι, ∑ σ : SpinConfig ι, f (pairOfMask mask σ) := by
  have hh := pairMaskEquiv.symm.sum_comp f
  rw [Fintype.sum_prod_type] at hh
  exact hh.symm

def mergeSpin (mask : ι → Bool)
    (w : SpinConfig (Coordinates mask) × SpinConfig (Coordinates (complementMask mask))) :
    SpinConfig ι :=
  fun i => if hi : mask i = true then w.1 ⟨i, hi⟩
    else w.2 ⟨i, by cases h : mask i <;> simp_all [complementMask]⟩

def splitSpinEquiv (mask : ι → Bool) : SpinConfig ι ≃
    (SpinConfig (Coordinates mask) × SpinConfig (Coordinates (complementMask mask))) where
  toFun σ := (restrictSpin mask σ, restrictSpin (complementMask mask) σ)
  invFun := mergeSpin mask
  left_inv σ := by
    funext i
    by_cases hi : mask i = true <;> simp [mergeSpin, restrictSpin, hi]
  right_inv w := by
    apply Prod.ext
    · funext i
      simp [restrictSpin, mergeSpin, i.property]
    · funext i
      have hi : mask i.val = false := by
        have hh := i.property
        cases hm : mask i.val <;> simp_all [complementMask]
      simp [restrictSpin, mergeSpin, hi]

theorem sum_split_spin (mask : ι → Bool)
    (f : SpinConfig (Coordinates mask) → ℝ)
    (g : SpinConfig (Coordinates (complementMask mask)) → ℝ) :
    (∑ σ : SpinConfig ι, f (restrictSpin mask σ) * g (restrictSpin (complementMask mask) σ)) =
      (∑ w, f w) * ∑ u, g u := by
  have hh := (splitSpinEquiv mask).sum_comp (fun x => f x.1 * g x.2)
  change (∑ σ, f (restrictSpin mask σ) * g (restrictSpin (complementMask mask) σ)) = _ at hh
  rw [hh, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem difference_pairOfMask (mask : ι → Bool) (σ : SpinConfig ι) :
    pairDifference (pairOfMask mask σ) = extend mask (spinVector (restrictSpin mask σ)) := by
  funext i
  cases hm : mask i <;> cases hs : σ i <;>
    norm_num [pairDifference, pairOfMask, flipOn, extend, spinVector, restrictSpin, hm, hs]

omit [Fintype ι] [DecidableEq ι] in
theorem midpoint_pairOfMask (mask : ι → Bool) (σ : SpinConfig ι) :
    pairMidpoint (pairOfMask mask σ) =
      extend (complementMask mask) (spinVector (restrictSpin (complementMask mask) σ)) := by
  funext i
  cases hm : mask i <;> cases hs : σ i <;>
    norm_num [pairMidpoint, pairOfMask, flipOn, extend, spinVector, restrictSpin,
      complementMask, hm, hs]

omit [Fintype ι] [DecidableEq ι] in
theorem pair_first_eq_sum (x : SpinConfig ι × SpinConfig ι) :
    spinVector x.1 = pairMidpoint x + pairDifference x := by
  funext i
  simp only [Pi.add_apply, pairMidpoint, pairDifference]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem pair_second_eq_sub (x : SpinConfig ι × SpinConfig ι) :
    spinVector x.2 = pairMidpoint x - pairDifference x := by
  funext i
  simp only [Pi.sub_apply, pairMidpoint, pairDifference]
  ring

omit [DecidableEq ι] in
theorem quadratic_parallelogram (N : Matrix ι ι ℝ) (u v : ι → ℝ) :
    quadratic N (u + v) + quadratic N (u - v) =
      2 * quadratic N u + 2 * quadratic N v := by
  simp only [quadratic, Matrix.mulVec_add, Matrix.mulVec_sub,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  ring

omit [DecidableEq ι] in
theorem quadratic_smul (a : ℝ) (N : Matrix ι ι ℝ) (v : ι → ℝ) :
    quadratic (a • N) v = a * quadratic N v := by
  simp only [quadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

def doubledPrincipal (N : Matrix ι ι ℝ) (mask : ι → Bool) :
    Matrix (Coordinates mask) (Coordinates mask) ℝ :=
  (2 : ℝ) • N.submatrix Subtype.val Subtype.val

def doubledField (h : ι → ℝ) (mask : ι → Bool) : Coordinates mask → ℝ :=
  fun i => 2 * h i.val

omit [DecidableEq ι] in
/-- The cancellation of the mixed energy and of the field from the difference. -/
theorem pair_weight_midpoint_difference (N : Matrix ι ι ℝ) (h : ι → ℝ)
    (x : SpinConfig ι × SpinConfig ι) :
    spinWeight N h x.1 * spinWeight N h x.2 =
      Real.exp (2 * (h ⬝ᵥ pairMidpoint x) - quadratic N (pairMidpoint x)) *
        Real.exp (-quadratic N (pairDifference x)) := by
  unfold spinWeight
  rw [← Real.exp_add, ← Real.exp_add, pair_first_eq_sum x, pair_second_eq_sub x]
  congr 1
  rw [dotProduct_add, dotProduct_sub]
  have hq := quadratic_parallelogram N (pairMidpoint x) (pairDifference x)
  linarith

omit [DecidableEq ι] in
/-- The actual pair weight factors into a zero-field law on the disagreement
coordinates and an independent field-biased law on their complement. -/
theorem pair_weight_factor (N : Matrix ι ι ℝ) (h : ι → ℝ)
    (mask : ι → Bool) (σ : SpinConfig ι) :
    spinWeight N h σ * spinWeight N h (flipOn mask σ) =
      spinWeight (doubledPrincipal N mask) 0 (restrictSpin mask σ) *
        spinWeight (doubledPrincipal N (complementMask mask))
          (doubledField h (complementMask mask)) (restrictSpin (complementMask mask) σ) := by
  change spinWeight N h (pairOfMask mask σ).1 * spinWeight N h (pairOfMask mask σ).2 = _
  rw [pair_weight_midpoint_difference N h (pairOfMask mask σ)]
  rw [midpoint_pairOfMask mask σ, difference_pairOfMask mask σ]
  rw [quadratic_extend, quadratic_extend, dot_extend]
  unfold spinWeight doubledPrincipal doubledField
  simp only [quadratic_smul, zero_dotProduct, zero_sub]
  have hd : (fun i : Coordinates (complementMask mask) => 2 * h i.val) ⬝ᵥ
      spinVector (restrictSpin (complementMask mask) σ) =
      2 * ((fun i : Coordinates (complementMask mask) => h i.val) ⬝ᵥ
        spinVector (restrictSpin (complementMask mask) σ)) := by
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  rw [hd]
  have hcancel (r : ℝ) : 2 * r / 2 = r := by ring
  simp only [hcancel]
  ring

/-- The complementary coordinates contribute this exact partition function. -/
def complementPartition (N : Matrix ι ι ℝ) (h : ι → ℝ) (mask : ι → Bool) : ℝ :=
  spinPartition (doubledPrincipal N (complementMask mask))
    (doubledField h (complementMask mask))

/-- Unnormalized probability weight of a disagreement mask. -/
def maskWeight (N : Matrix ι ι ℝ) (h : ι → ℝ) (mask : ι → Bool) : ℝ :=
  spinPartition (doubledPrincipal N mask) 0 * complementPartition N h mask

theorem weighted_pair_disintegration (N : Matrix ι ι ℝ) (h : ι → ℝ)
    (f : (ι → Bool) → (ι → ℝ) → ℝ) :
    (∑ x : SpinConfig ι × SpinConfig ι,
      (spinWeight N h x.1 * spinWeight N h x.2) * f (disagreement x) (pairDifference x)) =
      ∑ mask : SpinConfig ι,
        (∑ w : SpinConfig (Coordinates mask),
          spinWeight (doubledPrincipal N mask) 0 w * f mask (extend mask (spinVector w))) *
            complementPartition N h mask := by
  rw [sum_pairs_by_mask]
  apply Finset.sum_congr rfl
  intro mask _
  simp_rw [disagreement_pairOfMask, difference_pairOfMask]
  change (∑ σ : SpinConfig ι,
    (spinWeight N h σ * spinWeight N h (flipOn mask σ)) *
      f mask (extend mask (spinVector (restrictSpin mask σ)))) = _
  simp_rw [pair_weight_factor]
  calc
    _ = ∑ σ : SpinConfig ι,
        (spinWeight (doubledPrincipal N mask) 0 (restrictSpin mask σ) *
          f mask (extend mask (spinVector (restrictSpin mask σ)))) *
        spinWeight (doubledPrincipal N (complementMask mask))
          (doubledField h (complementMask mask)) (restrictSpin (complementMask mask) σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = _ := sum_split_spin mask
      (fun w => spinWeight (doubledPrincipal N mask) 0 w * f mask (extend mask (spinVector w)))
      (spinWeight (doubledPrincipal N (complementMask mask))
        (doubledField h (complementMask mask)))

theorem sum_pair_weights (N : Matrix ι ι ℝ) (h : ι → ℝ) :
    (∑ x : SpinConfig ι × SpinConfig ι, spinWeight N h x.1 * spinWeight N h x.2) =
      spinPartition N h ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, spinPartition, pow_two]

theorem sum_maskWeight (N : Matrix ι ι ℝ) (h : ι → ℝ) :
    (∑ mask : SpinConfig ι, maskWeight N h mask) = spinPartition N h ^ 2 := by
  have hh := weighted_pair_disintegration N h (fun _ _ => 1)
  simp only [mul_one, sum_pair_weights] at hh
  exact hh.symm

theorem maskWeight_pos (N : Matrix ι ι ℝ) (h : ι → ℝ) (mask : ι → Bool) :
    0 < maskWeight N h mask :=
  mul_pos (spinPartition_pos _ _) (spinPartition_pos _ _)

/-- The exact distribution of the disagreement mask, derived below from the pair law. -/
def maskLaw (N : Matrix ι ι ℝ) (h : ι → ℝ) : FiniteProbability (SpinConfig ι) where
  mass mask := maskWeight N h mask / spinPartition N h ^ 2
  nonneg mask := (div_pos (maskWeight_pos N h mask)
    (sq_pos_of_pos (spinPartition_pos N h))).le
  total := by
    rw [← Finset.sum_div, sum_maskWeight]
    exact div_self (ne_of_gt (sq_pos_of_pos (spinPartition_pos N h)))

theorem maskLaw_mass_pos (N : Matrix ι ι ℝ) (h : ι → ℝ) (mask : ι → Bool) :
    0 < (maskLaw N h).mass mask :=
  div_pos (maskWeight_pos N h mask) (sq_pos_of_pos (spinPartition_pos N h))

theorem spinLaw_expectation (N : Matrix ι ι ℝ) (h : ι → ℝ)
    (f : SpinConfig ι → ℝ) :
    (spinLaw N h).expectation f =
      (∑ σ : SpinConfig ι, spinWeight N h σ * f σ) / spinPartition N h := by
  unfold FiniteProbability.expectation spinLaw
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem pairLaw_expectation (N : Matrix ι ι ℝ) (h : ι → ℝ)
    (f : SpinConfig ι × SpinConfig ι → ℝ) :
    (independent (spinLaw N h) (spinLaw N h)).expectation f =
      (∑ x : SpinConfig ι × SpinConfig ι,
        (spinWeight N h x.1 * spinWeight N h x.2) * f x) / spinPartition N h ^ 2 := by
  unfold FiniteProbability.expectation independent spinLaw
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Exact joint disintegration of the mask and the half-difference, for every
real test function. This proves the zero-field conditional law without any
conditional-probability assumptions. -/
theorem pair_expectation_disintegrate (N : Matrix ι ι ℝ) (h : ι → ℝ)
    (f : (ι → Bool) → (ι → ℝ) → ℝ) :
    (independent (spinLaw N h) (spinLaw N h)).expectation
        (fun x => f (disagreement x) (pairDifference x)) =
      (maskLaw N h).expectation (fun mask =>
        (spinLaw (doubledPrincipal N mask) 0).expectation
          (fun w => f mask (extend mask (spinVector w)))) := by
  rw [pairLaw_expectation, weighted_pair_disintegration, Finset.sum_div]
  unfold FiniteProbability.expectation
  apply Finset.sum_congr rfl
  intro mask _
  change _ = (maskWeight N h mask / spinPartition N h ^ 2) *
    (spinLaw (doubledPrincipal N mask) 0).expectation
      (fun w => f mask (extend mask (spinVector w)))
  rw [spinLaw_expectation]
  unfold maskWeight
  field_simp [ne_of_gt (spinPartition_pos (doubledPrincipal N mask) 0)]

/-- Restricting the joint expectation to one fixed mask gives its exact positive
mask mass times the zero-field conditional expectation. -/
theorem restricted_pair_expectation (N : Matrix ι ι ℝ) (h : ι → ℝ)
    (mask : ι → Bool) (f : (ι → ℝ) → ℝ) :
    (independent (spinLaw N h) (spinLaw N h)).expectation
        (fun x => if disagreement x = mask then f (pairDifference x) else 0) =
      (maskLaw N h).mass mask *
        (spinLaw (doubledPrincipal N mask) 0).expectation
          (fun w => f (extend mask (spinVector w))) := by
  rw [pair_expectation_disintegrate N h (fun mask' v => if mask' = mask then f v else 0)]
  unfold FiniteProbability.expectation
  have hh (mask' : SpinConfig ι) :
      (∑ w : SpinConfig (Coordinates mask'),
        (spinLaw (doubledPrincipal N mask') 0).mass w *
          (if mask' = mask then f (extend mask' (spinVector w)) else 0)) =
      if mask' = mask then
        (spinLaw (doubledPrincipal N mask') 0).expectation
          (fun w => f (extend mask' (spinVector w))) else 0 := by
    by_cases hm : mask' = mask <;> simp [hm, FiniteProbability.expectation]
  simp_rw [hh]
  simp [FiniteProbability.expectation]

theorem disagreement_mask_probability (N : Matrix ι ι ℝ) (h : ι → ℝ)
    (mask : ι → Bool) :
    (independent (spinLaw N h) (spinLaw N h)).expectation
      (fun x => if disagreement x = mask then 1 else 0) = (maskLaw N h).mass mask := by
  simpa only [expectation_const, mul_one] using
    restricted_pair_expectation N h mask (fun _ => 1)

/-- The literal conditional-expectation ratio. Every mask has positive probability,
including the empty mask, so the displayed division is genuine. -/
theorem conditional_difference_law (N : Matrix ι ι ℝ) (h : ι → ℝ)
    (mask : ι → Bool) (f : (ι → ℝ) → ℝ) :
    (independent (spinLaw N h) (spinLaw N h)).expectation
        (fun x => if disagreement x = mask then f (pairDifference x) else 0) /
      (independent (spinLaw N h) (spinLaw N h)).expectation
        (fun x => if disagreement x = mask then 1 else 0) =
      (spinLaw (doubledPrincipal N mask) 0).expectation
        (fun w => f (extend mask (spinVector w))) := by
  rw [restricted_pair_expectation, disagreement_mask_probability]
  exact mul_div_cancel_left₀ _ (ne_of_gt (maskLaw_mass_pos N h mask))

/-- The displayed mask law is precisely the pushforward of the independent pair law. -/
theorem maskLaw_expectation (N : Matrix ι ι ℝ) (h : ι → ℝ)
    (g : (ι → Bool) → ℝ) :
    (maskLaw N h).expectation g =
      (independent (spinLaw N h) (spinLaw N h)).expectation
        (fun x => g (disagreement x)) := by
  have hh := pair_expectation_disintegrate N h (fun mask _ => g mask)
  simp only [expectation_const] at hh
  exact hh.symm

theorem maskLaw_inclusion_le_half (N : Matrix ι ι ℝ) (h : ι → ℝ) (i : ι) :
    (maskLaw N h).expectation (fun mask => if mask i then 1 else 0) ≤ (1 / 2 : ℝ) := by
  rw [maskLaw_expectation]
  exact disagreement_probability_le_half (spinLaw N h) i

end

end TheoremA2.SpinCovariance
