import TheoremA2.ConvexSupportMatrix
import TheoremA2.JointPrecisionAlgebra
import TheoremA2.LatticeEnergy
import TheoremA2.PeriodicCells

set_option maxHeartbeats 800000

/-!
# From the actual joint subgaussian law to the actual lattice-cell energies

This module proves equations (74) and (75) from a measure's literal exponential
moment bound and literal translated-cell integral identity. The geometric and
energy steps, including infeasible cells and dependent column projections, are
proved here. The joint reference law and its exponential moment bound are
constructed in the joint-law modules.
-/

namespace TheoremA2.CellEnergyComparison

open MeasureTheory Set
open TheoremA2.PrincipalInverse
open scoped BigOperators Matrix MatrixOrder
noncomputable section

abbrev JointSpace (r s : ℕ) := EuclideanSpace ℝ (Fin r ⊕ Fin s)

def spinPart {r s : ℕ} (w : JointSpace r s) : Fin r → ℝ := fun i => w (Sum.inl i)
def auxiliaryPart {r s : ℕ} (w : JointSpace r s) : Fin s → ℝ := fun j => w (Sum.inr j)
def period {s : ℕ} (l : Fin s → ℤ) : Fin s → ℝ := fun j => Real.pi * l j

def cellSet {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (l : Fin s → ℤ) :
    Set (JointSpace r s) :=
  {w | ∀ j, |(B.transpose *ᵥ spinPart w) j - period l j| ≤ Real.pi / 2}

def source {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (l : Fin s → ℤ) :
    JointSpace r s :=
  WithLp.toLp 2 (Sum.elim ((2 * lam) • (B *ᵥ period l)) (-period l))

def scaledColumns {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (c : ℝ) :
    Fin s → GaussianShift.Vector r := fun j i => B i j / Real.sqrt c

def scaledSpin {r : ℕ} (c : ℝ) (z : Fin r → ℝ) : GaussianShift.Vector r :=
  fun i => Real.sqrt c * z i

def offset {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (l : Fin s → ℤ)
    (z : Fin r → ℝ) : Fin s → ℝ := B.transpose *ᵥ z - period l

/-- The coordinate and Euclidean-space conventions give the same quadratic form. -/
theorem quadratic_eq_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (w : EuclideanSpace ℝ ι) :
    ConvexSupport.quadratic D w = quadratic D (WithLp.ofLp w) := by
  rw [ConvexSupport.quadratic_eq_sum, PrincipalInverse.quadratic_eq_sum]

theorem inner_eq_dot {ι : Type*} [Fintype ι] (w y : EuclideanSpace ℝ ι) :
    inner ℝ w y = WithLp.ofLp w ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  exact dotProduct_comm _ _

theorem joint_eq_parts {r s : ℕ} (w : JointSpace r s) :
    WithLp.ofLp w = Sum.elim (spinPart w) (auxiliaryPart w) := by
  funext i
  cases i <;> rfl

theorem inner_source {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ)
    (l : Fin s → ℤ) (w : JointSpace r s) :
    inner ℝ (source B lam l) w =
      2 * lam * (period l ⬝ᵥ (B.transpose *ᵥ spinPart w)) -
        period l ⬝ᵥ auxiliaryPart w := by
  rw [inner_eq_dot, joint_eq_parts w]
  simp only [source, WithLp.ofLp_toLp, sumElim_dotProduct_sumElim, smul_dotProduct,
    neg_dotProduct, smul_eq_mul]
  have hd : (B *ᵥ period l) ⬝ᵥ spinPart w = period l ⬝ᵥ (B.transpose *ᵥ spinPart w) := by
    rw [dotProduct_comm, JointPrecision.dot_transpose, dotProduct_comm]
  rw [hd]
  ring

theorem normSq_add {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    normSq (x + y) = normSq x + 2 * (x ⬝ᵥ y) + normSq y := by
  simp only [normSq, Pi.add_apply, dotProduct, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normSq_scaledSpin {r : ℕ} {c : ℝ} (hc : 0 ≤ c) (z : Fin r → ℝ) :
    GaussianShift.normSq (scaledSpin c z) = c * normSq z := by
  simp only [GaussianShift.normSq, scaledSpin, mul_pow, Real.sq_sqrt hc,
    normSq, Finset.mul_sum]

theorem scaled_pair_feasible {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {c : ℝ} (hc : 0 < c) (l : Fin s → ℤ) (w : JointSpace r s)
    (hw : w ∈ cellSet B l) :
    (∀ j, |offset B l (spinPart w) j| ≤ Real.pi / 2) ∧
      (∀ j, GaussianShift.dot (scaledColumns B c j) (scaledSpin c (spinPart w)) =
        Real.pi * l j + offset B l (spinPart w) j) := by
  refine ⟨hw, ?_⟩
  intro j
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  simp only [GaussianShift.dot, scaledColumns, scaledSpin]
  have hsum : (∑ i, B i j / Real.sqrt c * (Real.sqrt c * spinPart w i)) =
      (B.transpose *ᵥ spinPart w) j := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [hsum]
  simp only [offset, Pi.sub_apply, period]
  ring

/-- Completing the square in the auxiliary coordinates, with every constant retained. -/
theorem cell_exponent_identity {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) {c H : ℝ} (hc : 0 ≤ c) (hH : H ≠ 0)
    (l : Fin s → ℤ) (w : JointSpace r s) :
    -lam * normSq (period l) + inner ℝ (source B lam l) w -
        ConvexSupport.quadratic (JointPrecision.precision B lam c H) w / 2 =
      -LatticeEnergy.pairEnergy (2 * lam - 1 / H)
          (scaledSpin c (spinPart w)) (offset B l (spinPart w)) -
        H / 2 * normSq (auxiliaryPart w - (1 / H) • offset B l (spinPart w)) := by
  rw [quadratic_eq_coordinate, joint_eq_parts, JointPrecision.quadratic_precision,
    inner_source, JointPrecision.normSq_sub_smul]
  rw [LatticeEnergy.pairEnergy, normSq_scaledSpin hc]
  change _ = -((c * normSq (spinPart w) +
    (2 * lam - 1 / H) * normSq (offset B l (spinPart w))) / 2) - _
  have hy : B.transpose *ᵥ spinPart w = period l + offset B l (spinPart w) := by
    ext j
    simp only [offset, Pi.sub_apply, Pi.add_apply]
    ring
  rw [hy, normSq_add, add_dotProduct, dotProduct_add,
    JointPrecision.dot_self, dotProduct_comm (auxiliaryPart w)]
  field_simp
  ring


/-- Each closed periodic cell is the inverse image of an actual coordinate box. -/
theorem cellSet_isClosed {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (l : Fin s → ℤ) : IsClosed (cellSet B l) := by
  have hc (j : Fin s) : Continuous (fun w : JointSpace r s =>
      |(B.transpose *ᵥ spinPart w) j - period l j|) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, spinPart]
    fun_prop
  simpa only [cellSet, Set.setOf_forall] using
    isClosed_iInter (fun j => isClosed_le (hc j) continuous_const)

theorem cellSet_convex {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (l : Fin s → ℤ) : Convex ℝ (cellSet B l) := by
  intro w hw y hy a b ha hb hab j
  have hparts : spinPart (a • w + b • y) = a • spinPart w + b • spinPart y := by
    funext i
    rfl
  have heq : (B.transpose *ᵥ spinPart (a • w + b • y)) j - period l j =
      a * ((B.transpose *ᵥ spinPart w) j - period l j) +
        b * ((B.transpose *ᵥ spinPart y) j - period l j) := by
    rw [hparts, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (period l j) * hab
  change |(B.transpose *ᵥ spinPart (a • w + b • y)) j - period l j| ≤ _
  rw [heq]
  calc
    _ ≤ |a * ((B.transpose *ᵥ spinPart w) j - period l j)| +
          |b * ((B.transpose *ᵥ spinPart y) j - period l j)| := abs_add_le _ _
    _ = a * |(B.transpose *ᵥ spinPart w) j - period l j| +
          b * |(B.transpose *ᵥ spinPart y) j - period l j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (Real.pi / 2) + b * (Real.pi / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (hw j) ha)
        (mul_le_mul_of_nonneg_left (hy j) hb)
    _ = Real.pi / 2 := by rw [← add_mul, hab, one_mul]

/-- The residual square in the auxiliary coordinate has its correct nonpositive sign. -/
theorem cell_exponent_le {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) {c H : ℝ} (hc : 0 ≤ c) (hH : 0 < H)
    (l : Fin s → ℤ) (w : JointSpace r s) :
    -lam * normSq (period l) + inner ℝ (source B lam l) w -
        ConvexSupport.quadratic (JointPrecision.precision B lam c H) w / 2 ≤
      -LatticeEnergy.pairEnergy (2 * lam - 1 / H)
          (scaledSpin c (spinPart w)) (offset B l (spinPart w)) := by
  rw [cell_exponent_identity B lam hc (ne_of_gt hH)]
  exact sub_le_self _ (mul_nonneg (by positivity) (JointPrecision.normSq_nonneg _))

/-- The translated-cell integral in the actual identity (73). -/
def translatedCellIntegral {Ω : Type*} [MeasurableSpace Ω] {r s : ℕ}
    (μ : Measure Ω) (X : Ω → JointSpace r s) (B : Matrix (Fin r) (Fin s) ℝ)
    (lam : ℝ) (l : Fin s → ℤ) : ℝ :=
  Real.exp (-lam * normSq (period l)) *
    ∫ ω, (cellSet B l).indicator (fun w => Real.exp (inner ℝ (source B lam l) w)) (X ω) ∂μ

/-- Equation (74) for any actual law with the stated joint exponential moments.
The right side is the literal infimum over feasible latent vectors and offsets;
empty cells are treated without assigning them a fictitious finite energy. -/
theorem translatedCellIntegral_le {Ω : Type*} [MeasurableSpace Ω] {r s : ℕ}
    (μ : Measure Ω) (B : Matrix (Fin r) (Fin s) ℝ) {lam c H : ℝ}
    (hlam : 0 ≤ lam) (hc : 0 < c) (hH : 0 < H) (hkappa : 0 ≤ 2 * lam - 1 / H)
    (X : Ω → JointSpace r s) (hX : Measurable X)
    (hint : ∀ u, Integrable (fun ω => Real.exp (inner ℝ u (X ω))) μ)
    (hmgf : ∀ u, (∫ ω, Real.exp (inner ℝ u (X ω)) ∂μ) ≤
      Real.exp (ConvexSupport.quadratic (JointPrecision.precision B lam c H)⁻¹ u / 2))
    (l : Fin s → ℤ) :
    translatedCellIntegral μ X B lam l ≤
      LatticeEnergy.cellWeight (scaledColumns B c) (2 * lam - 1 / H) 1 l := by
  classical
  by_cases hne : (cellSet B l).Nonempty
  · have hP := JointPrecision.precision_posDef B hlam hc hH hkappa
    have hinv : ((JointPrecision.precision B lam c H)⁻¹)⁻¹ =
        JointPrecision.precision B lam c H :=
      Matrix.nonsing_inv_nonsing_inv _
        ((JointPrecision.precision B lam c H).isUnit_iff_isUnit_det.mp hP.isUnit)
    obtain ⟨w, hw, _, hbound⟩ :=
      ConvexSupport.matrix_convex_support_with_maximizer μ
        (JointPrecision.precision B lam c H)⁻¹ hP.inv X hX hint hmgf
        (cellSet B l) hne (cellSet_isClosed B l) (cellSet_convex B l) (source B lam l)
    have hfeasible := scaled_pair_feasible B hc l w hw
    have he : LatticeEnergy.pairEnergy (2 * lam - 1 / H)
        (scaledSpin c (spinPart w)) (offset B l (spinPart w)) ∈
        LatticeEnergy.feasibleEnergies (scaledColumns B c) (2 * lam - 1 / H) l :=
      ⟨scaledSpin c (spinPart w), offset B l (spinPart w),
        hfeasible.1, hfeasible.2, rfl⟩
    have hE : (LatticeEnergy.feasibleEnergies (scaledColumns B c)
        (2 * lam - 1 / H) l).Nonempty := ⟨_, he⟩
    have hinf := csInf_le (LatticeEnergy.feasibleEnergies_bddBelow hkappa l) he
    have hobj : -lam * normSq (period l) +
        ConvexSupport.matrixObjective (JointPrecision.precision B lam c H)⁻¹
          (source B lam l) w ≤
        -sInf (LatticeEnergy.feasibleEnergies (scaledColumns B c)
          (2 * lam - 1 / H) l) := by
      unfold ConvexSupport.matrixObjective
      rw [hinv]
      have h := cell_exponent_le B lam hc.le hH l w
      linarith
    calc
      translatedCellIntegral μ X B lam l ≤
          Real.exp (-lam * normSq (period l)) *
            Real.exp (ConvexSupport.matrixObjective (JointPrecision.precision B lam c H)⁻¹
              (source B lam l) w) :=
        mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
      _ = Real.exp (-lam * normSq (period l) +
          ConvexSupport.matrixObjective (JointPrecision.precision B lam c H)⁻¹
            (source B lam l) w) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-sInf (LatticeEnergy.feasibleEnergies (scaledColumns B c)
          (2 * lam - 1 / H) l)) := Real.exp_le_exp.2 hobj
      _ = LatticeEnergy.cellWeight (scaledColumns B c) (2 * lam - 1 / H) 1 l := by
        simp only [LatticeEnergy.cellWeight, hE, ite_true, neg_mul, one_mul]
  · have hzero : cellSet B l = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    simpa only [translatedCellIntegral, hzero, Set.indicator_empty, integral_zero, mul_zero]
      using LatticeEnergy.cellWeight_nonneg (scaledColumns B c) (2 * lam - 1 / H) 1 l


theorem scaledColumns_normSq {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (j : Fin s) :
    GaussianShift.normSq (scaledColumns B c j) = (∑ i, B i j ^ 2) / c := by
  simp only [GaussianShift.normSq, scaledColumns, div_pow, Real.sq_sqrt hc,
    Finset.sum_div]

/-- The actual matrix column bound survives the precise `sqrt c` rescaling. -/
theorem scaledColumns_normSq_le {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ)
    {c rho : ℝ} (hc : 0 < c) (hcol : ∀ j, (∑ i, B i j ^ 2) ≤ rho) (j : Fin s) :
    GaussianShift.normSq (scaledColumns B c j) ≤ rho / c := by
  rw [scaledColumns_normSq B hc.le]
  exact div_le_div_of_nonneg_right (hcol j) hc.le

/-- Equation (75) for any finite collection of noncentral cells, using the actual
cell identity (73) and the fully proved dependent-cell lattice bound (43). -/
theorem finite_cellMass_sum_le {Ω : Type*} [MeasurableSpace Ω] {r s : ℕ}
    (μ : Measure Ω) (B : Matrix (Fin r) (Fin s) ℝ) {lam c H rho : ℝ}
    (hlam : 0 < lam) (hc : 0 < c) (hH : 0 < H) (hkappa : 3 / 4 ≤ 2 * lam - 1 / H)
    (hrho : 0 < rho) (hcut : rho / (decoderBeta * c) ≤ 1 / 1000000)
    (hcol : ∀ j, (∑ i, B i j ^ 2) ≤ rho)
    (X : Ω → JointSpace r s) (hX : Measurable X)
    (hint : ∀ u, Integrable (fun ω => Real.exp (inner ℝ u (X ω))) μ)
    (hmgf : ∀ u, (∫ ω, Real.exp (inner ℝ u (X ω)) ∂μ) ≤
      Real.exp (ConvexSupport.quadratic (JointPrecision.precision B lam c H)⁻¹ u / 2))
    (hidentity : ∀ l, PeriodicCells.cellMass B lam l =
      referenceNormalizer B (CosineReference.reference lam) *
        translatedCellIntegral μ X B lam l)
    (J : Finset (Fin s → ℤ)) (hJ : ∀ l ∈ J, l ≠ 0) :
    (∑ l ∈ J, PeriodicCells.cellMass B lam l) ≤
      referenceNormalizer B (CosineReference.reference lam) * latticeError s (rho / c) := by
  have hZ : 0 ≤ referenceNormalizer B (CosineReference.reference lam) :=
    (Real.exp_pos _).le.trans (CosineReference.referenceNormalizer_lower_bound_explicit B hlam)
  have hk0 : 0 ≤ 2 * lam - 1 / H := by linarith
  have hq : 0 < rho / c := div_pos hrho hc
  have hqcut : (rho / c) / decoderBeta ≤ 1 / 1000000 := by
    convert hcut using 1
    ring
  have hsum := LatticeEnergy.finite_noncentral_lattice_sum hq hqcut hkappa
    (scaledColumns B c) (scaledColumns_normSq_le B hc hcol) J hJ
  calc
    (∑ l ∈ J, PeriodicCells.cellMass B lam l) ≤
        ∑ l ∈ J, referenceNormalizer B (CosineReference.reference lam) *
          LatticeEnergy.cellWeight (scaledColumns B c) (2 * lam - 1 / H) 1 l := by
      apply Finset.sum_le_sum
      intro l _
      rw [hidentity l]
      exact mul_le_mul_of_nonneg_left
        (translatedCellIntegral_le μ B hlam.le hc hH hk0 X hX hint hmgf l) hZ
    _ = referenceNormalizer B (CosineReference.reference lam) *
        ∑ l ∈ J, LatticeEnergy.cellWeight (scaledColumns B c) (2 * lam - 1 / H) 1 l :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hZ

/-- The finite set here is exactly the set of all noncentral periods occurring
in the complete spin space; no cell with spin mass is omitted. -/
theorem totalNoncentralMass_le {Ω : Type*} [MeasurableSpace Ω] {r s : ℕ}
    (μ : Measure Ω) (B : Matrix (Fin r) (Fin s) ℝ) {lam c H rho : ℝ}
    (hlam : 0 < lam) (hc : 0 < c) (hH : 0 < H) (hkappa : 3 / 4 ≤ 2 * lam - 1 / H)
    (hrho : 0 < rho) (hcut : rho / (decoderBeta * c) ≤ 1 / 1000000)
    (hcol : ∀ j, (∑ i, B i j ^ 2) ≤ rho)
    (X : Ω → JointSpace r s) (hX : Measurable X)
    (hint : ∀ u, Integrable (fun ω => Real.exp (inner ℝ u (X ω))) μ)
    (hmgf : ∀ u, (∫ ω, Real.exp (inner ℝ u (X ω)) ∂μ) ≤
      Real.exp (ConvexSupport.quadratic (JointPrecision.precision B lam c H)⁻¹ u / 2))
    (hidentity : ∀ l, PeriodicCells.cellMass B lam l =
      referenceNormalizer B (CosineReference.reference lam) *
        translatedCellIntegral μ X B lam l) :
    PeriodicCells.totalNoncentralMass B lam ≤
      referenceNormalizer B (CosineReference.reference lam) * latticeError s (rho / c) := by
  apply finite_cellMass_sum_le μ B hlam hc hH hkappa hrho hcut hcol X hX hint hmgf
    hidentity ((PeriodicCells.occurringPeriods B).erase 0)
  intro l hl
  exact (Finset.mem_erase.1 hl).1

end
end TheoremA2.CellEnergyComparison
