import TheoremA2.PrincipalInverse

/-!
# Matrix algebra for the joint precision bound

The crucial comparison increases the entire conditional-variance expression
at once. It never replaces separate occurrences of a covariance inside an
inverse or a mixed term.
-/

namespace TheoremA2.JointPrecision

open TheoremA2.PrincipalInverse
open scoped BigOperators Matrix MatrixOrder
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def spinPrecision (B : Matrix ι κ ℝ) (lam c : ℝ) : Matrix ι ι ℝ :=
  (2 * lam) • (B * B.transpose) + Matrix.diagonal (fun _ => c)

def precision (B : Matrix ι κ ℝ) (lam c H : ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks (spinPrecision B lam c) (-B) (-B.transpose)
    (Matrix.diagonal (fun _ => H))

def conditionalSchur (B : Matrix ι κ ℝ) (H : ℝ) (C : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  Matrix.diagonal (fun _ => H) - B.transpose * C * B

omit [DecidableEq ι] in
theorem normSq_nonneg (x : ι → ℝ) : 0 ≤ normSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq ι] in
theorem normSq_pos {x : ι → ℝ} (hx : x ≠ 0) : 0 < normSq x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    ext i
    simpa using not_exists_not.mp h i
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

omit [DecidableEq ι] in
theorem normSq_sub_smul (x y : ι → ℝ) (a : ℝ) :
    normSq (x - a • y) = normSq x - 2 * a * (x ⬝ᵥ y) + a ^ 2 * normSq y := by
  simp only [normSq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProduct,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem dot_transpose (B : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    x ⬝ᵥ (B *ᵥ y) = (B.transpose *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

omit [DecidableEq ι] in
theorem dot_self (x : ι → ℝ) : x ⬝ᵥ x = normSq x := by
  simp [dotProduct, normSq, pow_two]

theorem quadratic_diagonal (a : ℝ) (x : ι → ℝ) :
    quadratic (Matrix.diagonal (fun _ : ι => a)) x = a * normSq x := by
  simp only [quadratic, Matrix.mulVec_diagonal, dotProduct, normSq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadratic_spinPrecision (B : Matrix ι κ ℝ) (lam c : ℝ) (x : ι → ℝ) :
    quadratic (spinPrecision B lam c) x =
      2 * lam * normSq (B.transpose *ᵥ x) + c * normSq x := by
  rw [spinPrecision, quadratic_add_diagonal]
  unfold quadratic
  rw [Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec, dot_transpose,
    dot_self]
  rfl

omit [DecidableEq κ] in
theorem spinPrecision_posDef (B : Matrix ι κ ℝ) {lam c : ℝ}
    (hlam : 0 ≤ lam) (hc : 0 < c) : (spinPrecision B lam c).PosDef := by
  apply Matrix.PosDef.posSemidef_add _ (Matrix.PosDef.diagonal fun _ => hc)
  have hB : (B * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose B
  exact hB.smul (by positivity)

theorem quadratic_precision (B : Matrix ι κ ℝ) (lam c H : ℝ)
    (x : ι → ℝ) (y : κ → ℝ) :
    quadratic (precision B lam c H) (Sum.elim x y) =
      2 * lam * normSq (B.transpose *ᵥ x) + c * normSq x -
        2 * ((B.transpose *ᵥ x) ⬝ᵥ y) + H * normSq y := by
  unfold precision quadratic
  rw [Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim,
    Matrix.neg_mulVec, dotProduct_add, dotProduct_neg]
  rw [← quadratic, quadratic_spinPrecision, ← quadratic, quadratic_diagonal,
    dot_transpose, dotProduct_comm y]
  ring

theorem precision_completed_square (B : Matrix ι κ ℝ) (lam c : ℝ) {H : ℝ}
    (hH : H ≠ 0) (x : ι → ℝ) (y : κ → ℝ) :
    quadratic (precision B lam c H) (Sum.elim x y) =
      c * normSq x + (2 * lam - 1 / H) * normSq (B.transpose *ᵥ x) +
        H * normSq (y - (1 / H) • (B.transpose *ᵥ x)) := by
  rw [quadratic_precision, normSq_sub_smul, dotProduct_comm y]
  field_simp
  ring

theorem precision_posDef (B : Matrix ι κ ℝ) {lam c H : ℝ}
    (hlam : 0 ≤ lam) (hc : 0 < c) (hH : 0 < H) (hk : 0 ≤ 2 * lam - 1 / H) :
    (precision B lam c H).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.fromBlocks (spinPrecision_posDef B hlam hc).isHermitian
    (by simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_neg])
    (Matrix.isHermitian_diagonal_iff.2 (fun _ => rfl)), ?_⟩
  intro w hw
  let x : ι → ℝ := w ∘ Sum.inl
  let y : κ → ℝ := w ∘ Sum.inr
  have hxy : w = Sum.elim x y := by ext i; cases i <;> rfl
  simp only [star_trivial]
  change 0 < quadratic (precision B lam c H) w
  rw [hxy, precision_completed_square B lam c (ne_of_gt hH)]
  have hk0 := mul_nonneg hk (normSq_nonneg (B.transpose *ᵥ x))
  have hH0 := mul_nonneg hH.le (normSq_nonneg (y - (1 / H) • (B.transpose *ᵥ x)))
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      intro hy
      apply hw
      rw [hxy, hx, hy]
      ext i
      cases i <;> rfl
    simpa [hx, normSq] using mul_pos hH (normSq_pos hy)
  · have hx0 := mul_pos hc (normSq_pos hx)
    linarith

theorem quadratic_conditionalSchur (B : Matrix ι κ ℝ) (H : ℝ) (C : Matrix ι ι ℝ)
    (z : κ → ℝ) :
    quadratic (conditionalSchur B H C) z = H * normSq z - quadratic C (B *ᵥ z) := by
  unfold conditionalSchur quadratic
  rw [Matrix.sub_mulVec, dotProduct_sub, ← quadratic, quadratic_diagonal,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dot_transpose]
  simp only [Matrix.transpose_transpose]

/-- The whole expression in equation (71), before taking its supremum. -/
def variationalExpression (B : Matrix ι κ ℝ) (H : ℝ) (C : Matrix ι ι ℝ)
    (u : ι → ℝ) (v z : κ → ℝ) : ℝ :=
  quadratic C (u + B *ᵥ z) + 2 * (v ⬝ᵥ z) - H * normSq z

omit [DecidableEq ι] [DecidableEq κ] in
theorem variationalExpression_mono (B : Matrix ι κ ℝ) (H : ℝ)
    {C M : Matrix ι ι ℝ} (hCM : C ≤ M) (u : ι → ℝ) (v z : κ → ℝ) :
    variationalExpression B H C u v z ≤ variationalExpression B H M u v z := by
  have h := quadratic_nonneg (Matrix.le_iff.1 hCM) (u + B *ᵥ z)
  simp only [quadratic, Matrix.sub_mulVec, dotProduct_sub] at h
  unfold variationalExpression quadratic
  linarith

/-- A single variational comparison controls all appearances of `C` together. -/
theorem variationalExpression_le_inverse (B : Matrix ι κ ℝ) {lam c H : ℝ}
    (hA : (spinPrecision B lam c).PosDef) (hP : (precision B lam c H).PosDef)
    (u : ι → ℝ) (v z : κ → ℝ) :
    variationalExpression B H (spinPrecision B lam c)⁻¹ u v z ≤
      quadratic (precision B lam c H)⁻¹ (Sum.elim u v) := by
  let y := (spinPrecision B lam c)⁻¹ *ᵥ (u + B *ᵥ z)
  have hopt : 2 * ((u + B *ᵥ z) ⬝ᵥ y) - quadratic (spinPrecision B lam c) y =
      quadratic (spinPrecision B lam c)⁻¹ (u + B *ᵥ z) :=
    inverse_optimizer_value hA (u + B *ᵥ z)
  have hbound := inverse_variational_bound hP (Sum.elim u v) (Sum.elim y z)
  rw [sumElim_dotProduct_sumElim, quadratic_precision] at hbound
  rw [quadratic_spinPrecision, add_dotProduct] at hopt
  have hd : (B *ᵥ z) ⬝ᵥ y = (B.transpose *ᵥ y) ⬝ᵥ z := by
    rw [dotProduct_comm, dot_transpose]
  rw [hd] at hopt
  unfold variationalExpression
  linarith

theorem dual_quadratic_bound {a : ℝ} (ha : 0 < a) (x y : ι → ℝ) :
    2 * (x ⬝ᵥ y) - a * normSq y ≤ normSq x / a := by
  have hn := normSq_nonneg (x - a • y)
  rw [normSq_sub_smul] at hn
  apply (le_div_iff₀ ha).2
  nlinarith

/-- The rectangular-matrix bound `Bᵀ(2λBBᵀ+cI)⁻¹B ≤ (2λ)⁻¹I`. -/
theorem projected_spin_inverse_bound (B : Matrix ι κ ℝ) {lam c : ℝ}
    (hlam : 0 < lam) (hc : 0 < c) (z : κ → ℝ) :
    quadratic (spinPrecision B lam c)⁻¹ (B *ᵥ z) ≤ normSq z / (2 * lam) := by
  let y := (spinPrecision B lam c)⁻¹ *ᵥ (B *ᵥ z)
  have hopt : 2 * ((B *ᵥ z) ⬝ᵥ y) - quadratic (spinPrecision B lam c) y =
      quadratic (spinPrecision B lam c)⁻¹ (B *ᵥ z) :=
    inverse_optimizer_value (spinPrecision_posDef B hlam.le hc) _
  have hd : (B *ᵥ z) ⬝ᵥ y = z ⬝ᵥ (B.transpose *ᵥ y) := by
    rw [dotProduct_comm, dot_transpose, dotProduct_comm]
  rw [hd, quadratic_spinPrecision] at hopt
  have hdual := dual_quadratic_bound (by positivity : 0 < 2 * lam) z (B.transpose *ᵥ y)
  have hn := mul_nonneg hc.le (normSq_nonneg y)
  linarith

theorem conditionalSchur_posDef (B : Matrix ι κ ℝ) {lam c H : ℝ}
    (hlam : 0 < lam) (hc : 0 < c) (hH : 1 / (2 * lam) < H)
    {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (hCM : C ≤ (spinPrecision B lam c)⁻¹) :
    (conditionalSchur B H C).PosDef := by
  have hBC : (B.transpose * C * B).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul B hC
  have hdiag : (Matrix.diagonal (fun _ : κ => H)).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.2 (fun _ => rfl)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hdiag.sub hBC)
  intro z hz
  simp only [star_trivial]
  change 0 < quadratic (conditionalSchur B H C) z
  rw [quadratic_conditionalSchur]
  have hnonneg := quadratic_nonneg (Matrix.le_iff.1 hCM) (B *ᵥ z)
  simp only [quadratic, Matrix.sub_mulVec, dotProduct_sub] at hnonneg
  have hb := projected_spin_inverse_bound B hlam hc z
  have hpos := mul_pos (sub_pos.2 hH) (normSq_pos hz)
  unfold quadratic at hb ⊢
  rw [div_eq_mul_inv] at hb
  rw [one_div] at hpos
  nlinarith

omit [DecidableEq ι] in
theorem quadratic_add {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (x y : ι → ℝ) :
    quadratic C (x + y) = quadratic C x + 2 * (y ⬝ᵥ (C *ᵥ x)) + quadratic C y := by
  simp only [quadratic, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [symmetric_bilinear hC x y]
  ring

theorem variationalExpression_eq (B : Matrix ι κ ℝ) (H : ℝ)
    {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (u : ι → ℝ) (v z : κ → ℝ) :
    variationalExpression B H C u v z = quadratic C u +
      2 * ((v + B.transpose *ᵥ (C *ᵥ u)) ⬝ᵥ z) -
        quadratic (conditionalSchur B H C) z := by
  unfold variationalExpression
  rw [quadratic_add hC, quadratic_conditionalSchur, add_dotProduct]
  have hd : (B *ᵥ z) ⬝ᵥ (C *ᵥ u) = (B.transpose *ᵥ (C *ᵥ u)) ⬝ᵥ z := by
    rw [dotProduct_comm, dot_transpose]
  rw [hd]
  ring

/-- Exact evaluation of (71), followed by its justified monotone comparison. -/
theorem conditional_variance_expression_le (B : Matrix ι κ ℝ) {lam c H : ℝ}
    (hA : (spinPrecision B lam c).PosDef) (hP : (precision B lam c H).PosDef)
    {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (hCM : C ≤ (spinPrecision B lam c)⁻¹)
    (hD : (conditionalSchur B H C).PosDef) (u : ι → ℝ) (v : κ → ℝ) :
    quadratic C u + quadratic (conditionalSchur B H C)⁻¹
      (v + B.transpose *ᵥ (C *ᵥ u)) ≤
        quadratic (precision B lam c H)⁻¹ (Sum.elim u v) := by
  let w := v + B.transpose *ᵥ (C *ᵥ u)
  let z := (conditionalSchur B H C)⁻¹ *ᵥ w
  have he : variationalExpression B H C u v z =
      quadratic C u + quadratic (conditionalSchur B H C)⁻¹ w := by
    rw [variationalExpression_eq B H hC]
    have hv := inverse_optimizer_value hD w
    dsimp only [w, z] at hv ⊢
    linarith
  rw [← he]
  exact (variationalExpression_mono B H hCM u v z).trans
    (variationalExpression_le_inverse B hA hP u v z)

/-- The spin block of the joint inverse is bounded by `c⁻¹I`, without requiring
a square or invertible rectangular matrix `B`. -/
theorem inverse_spin_source_bound (B : Matrix ι κ ℝ) {lam c H : ℝ}
    (hlam : 0 ≤ lam) (hc : 0 < c) (hH : 0 < H) (hk : 0 ≤ 2 * lam - 1 / H)
    (u : ι → ℝ) :
    quadratic (precision B lam c H)⁻¹ (Sum.elim u (0 : κ → ℝ)) ≤ normSq u / c := by
  have hP := precision_posDef B hlam hc hH hk
  let w := (precision B lam c H)⁻¹ *ᵥ (Sum.elim u (0 : κ → ℝ))
  let x : ι → ℝ := w ∘ Sum.inl
  let y : κ → ℝ := w ∘ Sum.inr
  have hxy : w = Sum.elim x y := by ext i; cases i <;> rfl
  have hopt : 2 * (Sum.elim u (0 : κ → ℝ) ⬝ᵥ w) - quadratic (precision B lam c H) w =
      quadratic (precision B lam c H)⁻¹ (Sum.elim u (0 : κ → ℝ)) :=
    inverse_optimizer_value hP _
  rw [hxy, sumElim_dotProduct_sumElim, zero_dotProduct, add_zero,
    precision_completed_square B lam c (ne_of_gt hH)] at hopt
  have hdual := dual_quadratic_bound hc u x
  have hn1 := mul_nonneg hk (normSq_nonneg (B.transpose *ᵥ x))
  have hn2 := mul_nonneg hH.le (normSq_nonneg (y - (1 / H) • (B.transpose *ᵥ x)))
  linarith

end
end TheoremA2.JointPrecision
