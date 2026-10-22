import TheoremA2.ConvexSupport

/-!
# Averaging principal inverses: Lemma A.30 in quadratic-form notation

We prove the finite-law inequality for an arbitrary random coordinate mask and
an arbitrary random vector supported on that mask. No independence is assumed
between the coordinate-inclusion events. `normSq` is explicitly the sum of the
coordinate squares, i.e. the squared Euclidean norm, not the sup norm on a Pi
type.

After the variational estimate, the proof completes the square for actual
matrix inverses and explicitly extends principal-coordinate optimizers by zero.
The final theorem proves the claimed comparison for every vector `z`, which
is precisely the quadratic-form statement of the positive-semidefinite order.
-/

namespace TheoremA2.PrincipalInverse

open scoped BigOperators Matrix
open TheoremA2.ConvexSupport

noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

theorem expectation_nonneg (p : FiniteProbability Ω) {f : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ p.expectation f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (p.nonneg ω) (hf ω)

theorem expectation_add (p : FiniteProbability Ω) (f g : Ω → ℝ) :
    p.expectation (fun ω => f ω + g ω) = p.expectation f + p.expectation g := by
  simp [FiniteProbability.expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (p : FiniteProbability Ω) (f g : Ω → ℝ) :
    p.expectation (fun ω => f ω - g ω) = p.expectation f - p.expectation g := by
  simp [FiniteProbability.expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_const_mul (p : FiniteProbability Ω) (a : ℝ) (f : Ω → ℝ) :
    p.expectation (fun ω => a * f ω) = a * p.expectation f := by
  simp [FiniteProbability.expectation, Finset.mul_sum, mul_left_comm]

theorem expectation_mul_const (p : FiniteProbability Ω) (f : Ω → ℝ) (a : ℝ) :
    p.expectation (fun ω => f ω * a) = p.expectation f * a := by
  simp [FiniteProbability.expectation, Finset.sum_mul, mul_assoc]

theorem expectation_const (p : FiniteProbability Ω) (a : ℝ) :
    p.expectation (fun _ => a) = a := by
  rw [FiniteProbability.expectation, ← Finset.sum_mul, p.total, one_mul]

theorem expectation_sum (p : FiniteProbability Ω) (f : Ω → ι → ℝ) :
    p.expectation (fun ω => ∑ i, f ω i) =
      ∑ i, p.expectation (fun ω => f ω i) := by
  simp only [FiniteProbability.expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- The coordinatewise expectation of a random vector. -/
def mean (p : FiniteProbability Ω) (w : Ω → ι → ℝ) : ι → ℝ :=
  fun i => p.expectation (fun ω => w ω i)

/-- Euclidean squared norm in coordinates. -/
def normSq (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The actual quadratic form `xᵀ N x`. -/
def quadratic (N : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (N *ᵥ x)

theorem quadratic_eq_sum (N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadratic N x = ∑ i, ∑ j, x i * N i j * x j := by
  simp [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem quadratic_nonneg {N : Matrix ι ι ℝ} (hN : N.PosSemidef) (x : ι → ℝ) :
    0 ≤ quadratic N x := by
  simpa [quadratic] using hN.dotProduct_mulVec_nonneg x

theorem expectation_dot (p : FiniteProbability Ω) (z : ι → ℝ) (w : Ω → ι → ℝ) :
    p.expectation (fun ω => z ⬝ᵥ w ω) = z ⬝ᵥ mean p w := by
  simp only [dotProduct, expectation_sum, expectation_const_mul, mean]

/-- The exact identity underlying Jensen's inequality for a quadratic form. -/
theorem centered_quadratic_identity (p : FiniteProbability Ω)
    (N : Matrix ι ι ℝ) (w : Ω → ι → ℝ) :
    p.expectation (fun ω => quadratic N (w ω - mean p w)) =
      p.expectation (fun ω => quadratic N (w ω)) - quadratic N (mean p w) := by
  simp only [quadratic_eq_sum, expectation_sum, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hex (ω : Ω) :
      (w ω i - mean p w i) * N i j * (w ω j - mean p w j) =
        w ω i * N i j * w ω j -
        (w ω i * N i j * mean p w j) -
        (mean p w i * N i j * w ω j) +
        (mean p w i * N i j * mean p w j) := by ring
  simp_rw [hex, expectation_add, expectation_sub, expectation_mul_const,
    expectation_const_mul, expectation_const]
  change _ = _
  dsimp [mean]
  ring

theorem quadratic_mean_le (p : FiniteProbability Ω)
    {N : Matrix ι ι ℝ} (hN : N.PosSemidef) (w : Ω → ι → ℝ) :
    quadratic N (mean p w) ≤ p.expectation (fun ω => quadratic N (w ω)) := by
  have hn := expectation_nonneg p
    (fun ω => quadratic_nonneg hN (w ω - mean p w))
  rw [centered_quadratic_identity] at hn
  linarith

/-- A supported scalar random variable gains its event probability in
Cauchy--Schwarz. The event may have probability zero. -/
theorem supported_scalar_second_moment (p : FiniteProbability Ω)
    (event : Ω → Bool) (f : Ω → ℝ)
    (hsupport : ∀ ω, event ω = false → f ω = 0) :
    p.expectation f ^ 2 ≤
      p.expectation (fun ω => if event ω then 1 else 0) *
        p.expectation (fun ω => f ω ^ 2) := by
  unfold FiniteProbability.expectation
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro ω _
    exact mul_nonneg (p.nonneg ω) (by dsimp only; split_ifs <;> norm_num)
  · intro ω _
    exact mul_nonneg (p.nonneg ω) (sq_nonneg _)
  · intro ω _
    cases he : event ω
    · simp [he, hsupport ω he]
    · simp only [he, reduceIte, mul_one]
      ring

/-- The squared Euclidean norm inequality with the `1/q` gain.
The only event hypotheses are the individual marginal inclusion bounds. -/
theorem supported_norm_mean_le (p : FiniteProbability Ω)
    (mask : Ω → ι → Bool) (w : Ω → ι → ℝ) {q : ℝ} (hq : 0 < q)
    (hsupport : ∀ ω i, mask ω i = false → w ω i = 0)
    (hinclusion : ∀ i, p.expectation (fun ω => if mask ω i then 1 else 0) ≤ q) :
    normSq (mean p w) / q ≤ p.expectation (fun ω => normSq (w ω)) := by
  apply (div_le_iff₀ hq).2
  have hcoord (i : ι) :
      mean p w i ^ 2 ≤ q * p.expectation (fun ω => w ω i ^ 2) := by
    have hcs := supported_scalar_second_moment p (fun ω => mask ω i)
      (fun ω => w ω i) (fun ω => hsupport ω i)
    exact hcs.trans (mul_le_mul_of_nonneg_right (hinclusion i)
      (expectation_nonneg p (fun ω => sq_nonneg _)))
  calc
    normSq (mean p w) ≤ ∑ i, q * p.expectation (fun ω => w ω i ^ 2) :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = p.expectation (fun ω => normSq (w ω)) * q := by
      simp only [normSq, expectation_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The exact variational estimate used in the proof of Lemma A.30.

All masks, their dependence, the probability weights, and the supported vectors
are arbitrary. The positive-semidefinite hypothesis applies to the actual
matrix quadratic form. -/
theorem variational_core (p : FiniteProbability Ω)
    {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    (mask : Ω → ι → Bool) (w : Ω → ι → ℝ) (z : ι → ℝ)
    {a q : ℝ} (ha : 0 < a) (hq : 0 < q)
    (hsupport : ∀ ω i, mask ω i = false → w ω i = 0)
    (hinclusion : ∀ i, p.expectation (fun ω => if mask ω i then 1 else 0) ≤ q) :
    p.expectation (fun ω =>
      2 * (z ⬝ᵥ w ω) - quadratic N (w ω) - a * normSq (w ω)) ≤
        2 * (z ⬝ᵥ mean p w) - quadratic N (mean p w) - (a / q) * normSq (mean p w) := by
  have hquad := quadratic_mean_le p hN w
  have hnorm := supported_norm_mean_le p mask w hq hsupport hinclusion
  have hscaled := mul_le_mul_of_nonneg_left hnorm ha.le
  simp only [expectation_sub, expectation_const_mul, expectation_dot]
  have hid : a * (normSq (mean p w) / q) = (a / q) * normSq (mean p w) := by ring
  rw [hid] at hscaled
  linarith

section Inverses

variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem symmetric_bilinear {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (x y : ι → ℝ) : x ⬝ᵥ M *ᵥ y = y ⬝ᵥ M *ᵥ x := by
  have ht : Mᵀ = M := by simpa using hM.eq
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ht, dotProduct_comm]

theorem matrix_mul_inverse_vector {M : Matrix ι ι ℝ} (hM : M.PosDef)
    (z : ι → ℝ) : M *ᵥ (M⁻¹ *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)), Matrix.one_mulVec]

/-- Completing the square gives the inverse quadratic form as a variational upper bound. -/
theorem inverse_variational_bound {M : Matrix ι ι ℝ} (hM : M.PosDef)
    (z w : ι → ℝ) : 2 * (z ⬝ᵥ w) - quadratic M w ≤ quadratic M⁻¹ z := by
  let v := M⁻¹ *ᵥ z
  have hMv : M *ᵥ v = z := matrix_mul_inverse_vector hM z
  have hs : v ⬝ᵥ M *ᵥ w = z ⬝ᵥ w := by
    rw [symmetric_bilinear hM.isHermitian, hMv, dotProduct_comm]
  have hn := quadratic_nonneg hM.posSemidef (w - v)
  simp only [quadratic, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, hMv, hs] at hn
  have hwz : w ⬝ᵥ z = z ⬝ᵥ w := dotProduct_comm _ _
  have hvz : v ⬝ᵥ z = quadratic M⁻¹ z := dotProduct_comm _ _
  unfold quadratic at hvz ⊢
  nlinarith

/-- The explicit inverse vector attains that variational value. -/
theorem inverse_optimizer_value {M : Matrix ι ι ℝ} (hM : M.PosDef)
    (z : ι → ℝ) :
    2 * (z ⬝ᵥ (M⁻¹ *ᵥ z)) - quadratic M (M⁻¹ *ᵥ z) = quadratic M⁻¹ z := by
  unfold quadratic
  rw [matrix_mul_inverse_vector hM z, dotProduct_comm (M⁻¹ *ᵥ z) z]
  ring

theorem quadratic_add_diagonal (N : Matrix ι ι ℝ) (a : ℝ) (x : ι → ℝ) :
    quadratic (N + Matrix.diagonal (fun _ => a)) x = quadratic N x + a * normSq x := by
  unfold quadratic
  rw [Matrix.add_mulVec, dotProduct_add]
  congr 1
  simp only [dotProduct, Matrix.mulVec_diagonal, normSq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The subtype of coordinates present in a Boolean mask. -/
abbrev Coordinates (mask : ι → Bool) := {i : ι // mask i = true}

/-- Extend a vector on present coordinates by literal zeros on all other coordinates. -/
def extend (mask : ι → Bool) (x : Coordinates mask → ℝ) : ι → ℝ :=
  fun i => if hi : mask i = true then x ⟨i, hi⟩ else 0

omit [Fintype ι] [DecidableEq ι] in
theorem extend_present (mask : ι → Bool) (x : Coordinates mask → ℝ)
    (i : Coordinates mask) : extend mask x i.val = x i := by
  simp [extend, i.property]

omit [Fintype ι] [DecidableEq ι] in
theorem extend_absent (mask : ι → Bool) (x : Coordinates mask → ℝ)
    (i : ι) (hi : mask i = false) : extend mask x i = 0 := by
  simp [extend, hi]

omit [DecidableEq ι] in
theorem dot_extend (mask : ι → Bool) (z : ι → ℝ) (x : Coordinates mask → ℝ) :
    z ⬝ᵥ extend mask x = (fun i : Coordinates mask => z i.val) ⬝ᵥ x := by
  unfold dotProduct
  apply Finset.sum_congr_set {i | mask i = true}
  · intro i hi
    change mask i = true at hi
    simp [extend, hi]
  · intro i hi
    change ¬mask i = true at hi
    simp [extend, hi]

omit [DecidableEq ι] in
theorem normSq_extend (mask : ι → Bool) (x : Coordinates mask → ℝ) :
    normSq (extend mask x) = normSq x := by
  unfold normSq
  apply Finset.sum_congr_set {i | mask i = true}
  · intro i hi
    change mask i = true at hi
    simp [extend, hi]
  · intro i hi
    change ¬mask i = true at hi
    simp [extend, hi]

omit [DecidableEq ι] in
theorem quadratic_extend (N : Matrix ι ι ℝ) (mask : ι → Bool)
    (x : Coordinates mask → ℝ) :
    quadratic N (extend mask x) =
      quadratic (N.submatrix Subtype.val Subtype.val) x := by
  simp only [quadratic_eq_sum, Matrix.submatrix_apply]
  apply Finset.sum_congr_set {i | mask i = true}
  · intro i hi
    change mask i = true at hi
    apply Finset.sum_congr_set {j | mask j = true}
    · intro j hj
      change mask j = true at hj
      simp [extend, hi, hj]
    · intro j hj
      change ¬mask j = true at hj
      simp [extend, hj]
  · intro i hi
    change ¬mask i = true at hi
    simp [extend, hi]

/-- The actual principal submatrix on the present coordinates, shifted by `a I`. -/
def principalShift (N : Matrix ι ι ℝ) (a : ℝ) (mask : ι → Bool) :
    Matrix (Coordinates mask) (Coordinates mask) ℝ :=
  N.submatrix Subtype.val Subtype.val + Matrix.diagonal (fun _ => a)

theorem principalShift_posDef {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    {a : ℝ} (ha : 0 < a) (mask : ι → Bool) :
    (principalShift N a mask).PosDef := by
  exact Matrix.PosDef.posSemidef_add (hN.submatrix Subtype.val)
    (Matrix.PosDef.diagonal (fun _ => ha))

/-- Lemma A.30, stated as the comparison of the actual inverse quadratic forms
for every test vector. This includes the empty mask, since its coordinate type
is empty and its quadratic form is the empty sum, hence zero.

The scalar `q` is the paper's inclusion bound `p`; the argument even permits
`q > 1`. No independence of the mask coordinates is assumed. -/
theorem principal_inverse_average (p : FiniteProbability Ω)
    {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    (mask : Ω → ι → Bool) {a q : ℝ} (ha : 0 < a) (hq : 0 < q)
    (hinclusion : ∀ i, p.expectation (fun ω => if mask ω i then 1 else 0) ≤ q)
    (z : ι → ℝ) :
    p.expectation (fun ω =>
      quadratic (principalShift N a (mask ω))⁻¹
        (fun i : Coordinates (mask ω) => z i.val)) ≤
      quadratic (N + Matrix.diagonal (fun _ => a / q))⁻¹ z := by
  let w : Ω → ι → ℝ := fun ω => extend (mask ω)
    ((principalShift N a (mask ω))⁻¹ *ᵥ (fun i : Coordinates (mask ω) => z i.val))
  have hsupport : ∀ ω i, mask ω i = false → w ω i = 0 := by
    intro ω i hi
    exact extend_absent _ _ _ hi
  have hvalue (ω : Ω) :
      2 * (z ⬝ᵥ w ω) - quadratic N (w ω) - a * normSq (w ω) =
        quadratic (principalShift N a (mask ω))⁻¹
          (fun i : Coordinates (mask ω) => z i.val) := by
    dsimp only [w]
    rw [dot_extend, quadratic_extend, normSq_extend]
    have ho := inverse_optimizer_value (principalShift_posDef hN ha (mask ω))
      (fun i : Coordinates (mask ω) => z i.val)
    simpa only [principalShift, quadratic_add_diagonal, sub_add_eq_sub_sub] using ho
  have hcore := variational_core p hN mask w z ha hq hsupport hinclusion
  have hfull : (N + Matrix.diagonal (fun _ : ι => a / q)).PosDef :=
    Matrix.PosDef.posSemidef_add hN (Matrix.PosDef.diagonal (fun _ => div_pos ha hq))
  calc
    _ = p.expectation (fun ω =>
        2 * (z ⬝ᵥ w ω) - quadratic N (w ω) - a * normSq (w ω)) := by
      congr 1
      funext ω
      exact (hvalue ω).symm
    _ ≤ 2 * (z ⬝ᵥ mean p w) - quadratic N (mean p w) -
        (a / q) * normSq (mean p w) := hcore
    _ ≤ quadratic (N + Matrix.diagonal (fun _ => a / q))⁻¹ z := by
      simpa only [quadratic_add_diagonal, sub_add_eq_sub_sub] using
        inverse_variational_bound hfull z (mean p w)

/-- Put a matrix on present coordinates into the ambient matrix, filling all
other entries with zero, exactly as `embed` is defined in the paper. -/
def embedMatrix (mask : ι → Bool) (A : Matrix (Coordinates mask) (Coordinates mask) ℝ) :
    Matrix ι ι ℝ := fun i j =>
  if hi : mask i = true then
    if hj : mask j = true then A ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

omit [DecidableEq ι] in
theorem quadratic_embedMatrix (mask : ι → Bool)
    (A : Matrix (Coordinates mask) (Coordinates mask) ℝ) (z : ι → ℝ) :
    quadratic (embedMatrix mask A) z =
      quadratic A (fun i : Coordinates mask => z i.val) := by
  simp only [quadratic_eq_sum]
  apply Finset.sum_congr_set {i | mask i = true}
  · intro i hi
    change mask i = true at hi
    apply Finset.sum_congr_set {j | mask j = true}
    · intro j hj
      change mask j = true at hj
      simp [embedMatrix, hi, hj]
    · intro j hj
      change ¬mask j = true at hj
      simp [embedMatrix, hi, hj]
  · intro i hi
    change ¬mask i = true at hi
    simp [embedMatrix, hi]

omit [Fintype ι] [DecidableEq ι] in
theorem embedMatrix_isHermitian (mask : ι → Bool)
    {A : Matrix (Coordinates mask) (Coordinates mask) ℝ} (hA : A.IsHermitian) :
    (embedMatrix mask A).IsHermitian := by
  apply Matrix.ext
  intro i j
  change star (embedMatrix mask A j i) = embedMatrix mask A i j
  simp only [star_trivial]
  by_cases hi : mask i = true
  · by_cases hj : mask j = true
    · simp only [embedMatrix, dif_pos hi, dif_pos hj]
      have hs := congrArg (fun M => M ⟨i, hi⟩ ⟨j, hj⟩) hA.eq
      simpa using hs
    · simp [embedMatrix, hi, hj]
  · simp [embedMatrix, hi]

/-- Entrywise expectation of a finite random matrix. -/
def meanMatrix (p : FiniteProbability Ω) (A : Ω → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => p.expectation (fun ω => A ω i j)

omit [DecidableEq ι] in
theorem quadratic_meanMatrix (p : FiniteProbability Ω)
    (A : Ω → Matrix ι ι ℝ) (z : ι → ℝ) :
    quadratic (meanMatrix p A) z = p.expectation (fun ω => quadratic (A ω) z) := by
  simp only [quadratic_eq_sum, meanMatrix, expectation_sum,
    expectation_mul_const, expectation_const_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem meanMatrix_isHermitian (p : FiniteProbability Ω)
    (A : Ω → Matrix ι ι ℝ) (hA : ∀ ω, (A ω).IsHermitian) :
    (meanMatrix p A).IsHermitian := by
  apply Matrix.ext
  intro i j
  change star (meanMatrix p A j i) = meanMatrix p A i j
  simp only [star_trivial, meanMatrix]
  congr 1
  funext ω
  have hs := congrArg (fun M => M i j) (hA ω).eq
  simpa using hs

/-- Lemma A.30 in literal matrix notation: the difference of the full inverse
and the expected zero-embedded principal inverse is positive semidefinite. -/
theorem principal_inverse_average_psd (p : FiniteProbability Ω)
    {N : Matrix ι ι ℝ} (hN : N.PosSemidef)
    (mask : Ω → ι → Bool) {a q : ℝ} (ha : 0 < a) (hq : 0 < q)
    (hinclusion : ∀ i, p.expectation (fun ω => if mask ω i then 1 else 0) ≤ q) :
    ((N + Matrix.diagonal (fun _ => a / q))⁻¹ -
      meanMatrix p (fun ω => embedMatrix (mask ω) (principalShift N a (mask ω))⁻¹)).PosSemidef := by
  have hfull : (N + Matrix.diagonal (fun _ : ι => a / q)).PosDef :=
    Matrix.PosDef.posSemidef_add hN (Matrix.PosDef.diagonal (fun _ => div_pos ha hq))
  have hemb (ω : Ω) :
      (embedMatrix (mask ω) (principalShift N a (mask ω))⁻¹).IsHermitian :=
    embedMatrix_isHermitian _ (principalShift_posDef hN ha (mask ω)).isHermitian.inv
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hfull.isHermitian.inv.sub (meanMatrix_isHermitian p _ hemb))
  intro z
  have hbound := principal_inverse_average p hN mask ha hq hinclusion z
  have hquad : quadratic
      (meanMatrix p (fun ω => embedMatrix (mask ω) (principalShift N a (mask ω))⁻¹)) z ≤
      quadratic (N + Matrix.diagonal (fun _ => a / q))⁻¹ z := by
    simpa only [quadratic_meanMatrix, quadratic_embedMatrix] using hbound
  simpa only [quadratic, Matrix.sub_mulVec, dotProduct_sub, star_trivial] using
    sub_nonneg.mpr hquad

end Inverses

#print axioms supported_scalar_second_moment
#print axioms quadratic_mean_le
#print axioms supported_norm_mean_le
#print axioms variational_core
#print axioms principal_inverse_average
#print axioms principal_inverse_average_psd

end

end TheoremA2.PrincipalInverse
