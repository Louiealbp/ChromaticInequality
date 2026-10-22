import TheoremA2.GaussianEnvelopeBox
import TheoremA2.ConvexSupportMatrix
import TheoremA2.LatticeEnergy

/-!
# Relative Gaussian cell comparison from the literal central-box MGF

This module carries out the convex-support and lattice steps of A.26. The MGF
input is stated on the actual normalized central law. The analytic BL wrapper
will discharge it; no relative cell estimate is taken as an input.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def euclideanBox (b : ℝ) : Set (EuclideanSpace ℝ ι) := {x | ∀ i, |x i| ≤ b}

theorem euclideanBox_isClosed (b : ℝ) : IsClosed (euclideanBox (ι := ι) b) := by
  change IsClosed {x : EuclideanSpace ℝ ι | ∀ i, |x.ofLp i| ≤ b}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter (fun i : ι => isClosed_le ?_ continuous_const)
  fun_prop

theorem euclideanBox_convex (b : ℝ) : Convex ℝ (euclideanBox (ι := ι) b) := by
  intro x hx y hy a c ha hc hac
  intro i
  change |a * x i + c * y i| ≤ b
  calc
    |a * x i + c * y i| ≤ |a * x i| + |c * y i| := abs_add_le _ _
    _ = a * |x i| + c * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hc]
    _ ≤ a * b + c * b := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
      (mul_le_mul_of_nonneg_left (hy i) hc)
    _ = b := by rw [← add_mul, hac, one_mul]

theorem euclidean_inner_eq_dot (x y : EuclideanSpace ℝ ι) :
    inner ℝ x y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  exact dotProduct_comm _ _

theorem euclidean_quadratic_eq (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    TheoremA2.ConvexSupport.quadratic M x = quadratic M (WithLp.ofLp x) := by
  rw [TheoremA2.ConvexSupport.quadratic_eq_sum, PrincipalInverse.quadratic_eq_sum]

def cellPrecision (T : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  T⁻¹ + Matrix.diagonal (fun _ => (3 / 4 : ℝ))

theorem cellPrecision_posDef {T : Matrix ι ι ℝ} (hT : T.PosDef) :
    (cellPrecision T).PosDef :=
  hT.inv.add_posSemidef (Matrix.PosSemidef.diagonal (by intro i; norm_num))

def cellIndexEquiv : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm

def finCoordinates (x : ι → ℝ) : Fin (Fintype.card ι) → ℝ :=
  fun i => x (cellIndexEquiv i)

def finPeriod (k : ι → ℤ) : Fin (Fintype.card ι) → ℤ :=
  fun i => k (cellIndexEquiv i)

theorem finPeriod_injective : Function.Injective (finPeriod (ι := ι)) := by
  intro k l h
  funext i
  obtain ⟨j, rfl⟩ := cellIndexEquiv.surjective i
  exact congrFun h j

theorem finCoordinates_normSq (x : ι → ℝ) :
    GaussianShift.normSq (finCoordinates x) = normSq x := by
  exact cellIndexEquiv.sum_comp (fun i => x i ^ 2)

theorem finCoordinates_dot (x y : ι → ℝ) :
    GaussianShift.dot (finCoordinates x) (finCoordinates y) = x ⬝ᵥ y := by
  exact cellIndexEquiv.sum_comp (fun i => x i * y i)

def gaussianLatticeColumns (T : Matrix ι ι ℝ) :
    Fin (Fintype.card ι) → GaussianShift.Vector (Fintype.card ι) :=
  fun i => finCoordinates (fun j => CFC.sqrt T (cellIndexEquiv i) j)

theorem sqrt_row_normSq {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (i : ι) :
    normSq (fun j => CFC.sqrt T i j) = T i i := by
  have he : (fun j => CFC.sqrt T i j) = (CFC.sqrt T)ᵀ *ᵥ Pi.single i 1 := by
    ext j
    rw [Matrix.mulVec_single_one]
    rfl
  rw [he, normSq_sqrt_transpose hT]
  simp only [quadratic, single_dotProduct, one_mul, Matrix.mulVec_single_one, Matrix.col,
    Matrix.transpose_apply]

theorem gaussianLatticeColumns_normSq {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (i : Fin (Fintype.card ι)) :
    GaussianShift.normSq (gaussianLatticeColumns T i) = T (cellIndexEquiv i) (cellIndexEquiv i) := by
  rw [gaussianLatticeColumns, finCoordinates_normSq, sqrt_row_normSq hT]

def periodShift (k : ι → ℤ) : ι → ℝ := fun i => Real.pi * k i

def cellLatent (T : Matrix ι ι ℝ) (k : ι → ℤ) (x : ι → ℝ) : ι → ℝ :=
  (CFC.sqrt T)⁻¹ *ᵥ (periodShift k + x)

theorem gaussian_cell_feasible {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (k : ι → ℤ) (x : ι → ℝ) (hx : x ∈ coordinateBox (Real.pi / 2)) :
    (∀ i, |finCoordinates x i| ≤ Real.pi / 2) ∧
      ∀ i, GaussianShift.dot (gaussianLatticeColumns T i)
          (finCoordinates (cellLatent T k x)) =
        Real.pi * finPeriod k i + finCoordinates x i := by
  refine ⟨fun i => hx _, fun i => ?_⟩
  rw [gaussianLatticeColumns, finCoordinates_dot]
  change (CFC.sqrt T *ᵥ ((CFC.sqrt T)⁻¹ *ᵥ (periodShift k + x)))
    (cellIndexEquiv i) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (covariance_sqrt_posDef hT).det_pos)), Matrix.one_mulVec]
  rfl

theorem gaussian_cell_energy {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (k : ι → ℤ) (x : ι → ℝ) :
    LatticeEnergy.pairEnergy (3 / 4)
        (finCoordinates (cellLatent T k x)) (finCoordinates x) =
      (quadratic T⁻¹ (periodShift k + x) + (3 / 4) * normSq x) / 2 := by
  rw [LatticeEnergy.pairEnergy, finCoordinates_normSq, finCoordinates_normSq]
  rw [cellLatent, normSq_sqrt_inv hT]

theorem quadratic_add_symmetric {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (x y : ι → ℝ) :
    quadratic M (x + y) = quadratic M x + 2 * (x ⬝ᵥ (M *ᵥ y)) + quadratic M y := by
  simp only [quadratic, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [symmetric_bilinear hM y x]
  ring

theorem gaussian_cell_exponent {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (k : ι → ℤ) (x : EuclideanSpace ℝ ι) :
    -quadratic T⁻¹ (periodShift k) / 2 +
        TheoremA2.ConvexSupport.matrixObjective (cellPrecision T)⁻¹
          (WithLp.toLp 2 (-(T⁻¹ *ᵥ periodShift k))) x =
      -LatticeEnergy.pairEnergy (3 / 4)
        (finCoordinates (cellLatent T k (WithLp.ofLp x)))
        (finCoordinates (WithLp.ofLp x)) := by
  have hP := cellPrecision_posDef hT
  have hi : ((cellPrecision T)⁻¹)⁻¹ = cellPrecision T :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos))
  rw [TheoremA2.ConvexSupport.matrixObjective, hi, euclidean_inner_eq_dot,
    euclidean_quadratic_eq, gaussian_cell_energy hT]
  change -quadratic T⁻¹ (periodShift k) / 2 +
    (-(T⁻¹ *ᵥ periodShift k) ⬝ᵥ WithLp.ofLp x -
      quadratic (T⁻¹ + Matrix.diagonal (fun _ => (3 / 4 : ℝ))) (WithLp.ofLp x) / 2) = _
  rw [neg_dotProduct, dotProduct_comm (T⁻¹ *ᵥ periodShift k),
    symmetric_bilinear hT.inv.isHermitian (WithLp.ofLp x) (periodShift k),
    quadratic_add_diagonal, quadratic_add_symmetric hT.inv.isHermitian]
  ring

/-- Exact A.22-to-lattice comparison for one actual translated central cell. -/
theorem translatedEnvelopeCell_le_of_mgf {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (hmgf : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw T (Real.pi / 2)) ≤
        Real.exp (quadratic (cellPrecision T)⁻¹ u / 2))
    (k : ι → ℤ) :
    translatedEnvelopeCell T (Real.pi / 2) (periodShift k) ≤
      boxEnvelopeNormalizer T (Real.pi / 2) *
        LatticeEnergy.cellWeight (gaussianLatticeColumns T) (3 / 4) 1 (finPeriod k) := by
  have hb : 0 < Real.pi / 2 := by positivity
  have hP := cellPrecision_posDef hT
  have hint (u : EuclideanSpace ℝ ι) :
      Integrable (fun x : ι → ℝ => Real.exp (inner ℝ u (WithLp.toLp 2 x)))
        (boxEnvelopeLaw T (Real.pi / 2)) := by
    simpa only [euclidean_inner_eq_dot, WithLp.ofLp_toLp] using
      integrable_boxEnvelopeLaw_exp_dot hT.posSemidef (Real.pi / 2) (WithLp.ofLp u)
  have hmgf' (u : EuclideanSpace ℝ ι) :
      (∫ x : ι → ℝ, Real.exp (inner ℝ u (WithLp.toLp 2 x))
        ∂boxEnvelopeLaw T (Real.pi / 2)) ≤
      Real.exp (TheoremA2.ConvexSupport.quadratic (cellPrecision T)⁻¹ u / 2) := by
    simpa only [euclidean_inner_eq_dot, euclidean_quadratic_eq, WithLp.ofLp_toLp] using
      hmgf (WithLp.ofLp u)
  obtain ⟨x, hx, _, hbound⟩ :=
    TheoremA2.ConvexSupport.matrix_convex_support_with_maximizer
      (boxEnvelopeLaw T (Real.pi / 2)) (cellPrecision T)⁻¹ hP.inv
      (WithLp.toLp 2) (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable hint hmgf'
      (euclideanBox (Real.pi / 2)) ⟨0, by intro i; simp; positivity⟩
      (euclideanBox_isClosed _) (euclideanBox_convex _)
      (WithLp.toLp 2 (-(T⁻¹ *ᵥ periodShift k)))
  have hind : (∫ y : ι → ℝ,
      (euclideanBox (Real.pi / 2)).indicator
        (fun z => Real.exp (inner ℝ (WithLp.toLp 2 (-(T⁻¹ *ᵥ periodShift k))) z))
        (WithLp.toLp 2 y) ∂boxEnvelopeLaw T (Real.pi / 2)) =
      ∫ y, Real.exp (-(periodShift k ⬝ᵥ (T⁻¹ *ᵥ y)))
        ∂boxEnvelopeLaw T (Real.pi / 2) := by
    apply integral_congr_ae
    filter_upwards [boxEnvelopeLaw_ae_mem T (Real.pi / 2)] with y hy
    rw [Set.indicator_of_mem (show WithLp.toLp 2 y ∈ euclideanBox (Real.pi / 2) from hy),
      euclidean_inner_eq_dot]
    change Real.exp (-(T⁻¹ *ᵥ periodShift k) ⬝ᵥ y) = _
    rw [neg_dotProduct, dotProduct_comm (T⁻¹ *ᵥ periodShift k),
      symmetric_bilinear hT.inv.isHermitian y (periodShift k)]
  rw [hind] at hbound
  have hfeas := gaussian_cell_feasible hT k (WithLp.ofLp x) hx
  have he : LatticeEnergy.pairEnergy (3 / 4)
      (finCoordinates (cellLatent T k (WithLp.ofLp x))) (finCoordinates (WithLp.ofLp x)) ∈
      LatticeEnergy.feasibleEnergies (gaussianLatticeColumns T) (3 / 4) (finPeriod k) :=
    ⟨_, _, hfeas.1, hfeas.2, rfl⟩
  have hne := Set.nonempty_of_mem he
  have hInf := csInf_le (LatticeEnergy.feasibleEnergies_bddBelow (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (finPeriod k)) he
  rw [translatedEnvelopeCell_identity hT hb]
  calc
    _ ≤ boxEnvelopeNormalizer T (Real.pi / 2) *
        (Real.exp (-quadratic T⁻¹ (periodShift k) / 2) *
          Real.exp (TheoremA2.ConvexSupport.matrixObjective (cellPrecision T)⁻¹
            (WithLp.toLp 2 (-(T⁻¹ *ᵥ periodShift k))) x)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hbound
        (mul_nonneg (boxEnvelopeNormalizer_pos hT hb).le (Real.exp_pos _).le)
    _ = boxEnvelopeNormalizer T (Real.pi / 2) *
        Real.exp (-LatticeEnergy.pairEnergy (3 / 4)
          (finCoordinates (cellLatent T k (WithLp.ofLp x))) (finCoordinates (WithLp.ofLp x))) := by
      rw [← Real.exp_add, gaussian_cell_exponent hT]
    _ ≤ boxEnvelopeNormalizer T (Real.pi / 2) *
        Real.exp (-sInf (LatticeEnergy.feasibleEnergies (gaussianLatticeColumns T)
          (3 / 4) (finPeriod k))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hInf))
        (boxEnvelopeNormalizer_pos hT hb).le
    _ = _ := by simp only [LatticeEnergy.cellWeight, hne, ite_true, neg_mul, one_mul]

theorem translatedEnvelopeCell_nonneg (T : Matrix ι ι ℝ) (b : ℝ) (z : ι → ℝ) :
    0 ≤ translatedEnvelopeCell T b z :=
  integral_nonneg (fun x => mul_nonneg (covarianceDensity_nonneg T (z + x))
    (envelopeWeight_pos x).le)

/-- The full noncentral countable cell estimate, with the central MGF as its
sole analytic input. The lattice and Gaussian-cell assertions are proved here. -/
theorem noncentral_envelope_cells_of_mgf {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {q : ℝ} (hq : 0 < q) (hdiag : ∀ i, T i i ≤ q)
    (hcut : q / decoderBeta ≤ 1 / 1000000)
    (hmgf : ∀ u : ι → ℝ,
      (∫ x, Real.exp (u ⬝ᵥ x) ∂boxEnvelopeLaw T (Real.pi / 2)) ≤
        Real.exp (quadratic (cellPrecision T)⁻¹ u / 2)) :
    Summable (fun k : {k : ι → ℤ // k ≠ 0} =>
      translatedEnvelopeCell T (Real.pi / 2) (periodShift k.val)) ∧
      (∑' k : {k : ι → ℤ // k ≠ 0},
        translatedEnvelopeCell T (Real.pi / 2) (periodShift k.val)) ≤
        latticeError (Fintype.card ι) q * boxEnvelopeNormalizer T (Real.pi / 2) := by
  classical
  have hb : 0 < Real.pi / 2 := by positivity
  have hfin (J : Finset {k : ι → ℤ // k ≠ 0}) :
      (∑ k ∈ J, translatedEnvelopeCell T (Real.pi / 2) (periodShift k.val)) ≤
        latticeError (Fintype.card ι) q * boxEnvelopeNormalizer T (Real.pi / 2) := by
    have hl := LatticeEnergy.finite_noncentral_lattice_sum hq hcut (by norm_num : (3 / 4 : ℝ) ≤ 3 / 4)
      (gaussianLatticeColumns T) (fun i => by rw [gaussianLatticeColumns_normSq hT.posSemidef]; exact hdiag _)
      (J.image (fun k => finPeriod k.val)) (by
        intro k hk
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
        intro hz
        have hzero : finPeriod (0 : ι → ℤ) = 0 := by funext i; rfl
        exact l.property (finPeriod_injective (hz.trans hzero.symm)))
    rw [Finset.sum_image (fun a _ b _ hab => Subtype.ext (finPeriod_injective hab))] at hl
    calc
      _ ≤ ∑ k ∈ J, boxEnvelopeNormalizer T (Real.pi / 2) *
          LatticeEnergy.cellWeight (gaussianLatticeColumns T) (3 / 4) 1 (finPeriod k.val) :=
        Finset.sum_le_sum fun k _ => translatedEnvelopeCell_le_of_mgf hT hmgf k.val
      _ = boxEnvelopeNormalizer T (Real.pi / 2) *
          ∑ k ∈ J, LatticeEnergy.cellWeight (gaussianLatticeColumns T) (3 / 4) 1 (finPeriod k.val) := by
        rw [Finset.mul_sum]
      _ ≤ boxEnvelopeNormalizer T (Real.pi / 2) * latticeError (Fintype.card ι) q :=
        mul_le_mul_of_nonneg_left hl (boxEnvelopeNormalizer_pos hT hb).le
      _ = _ := mul_comm _ _
  have hs := summable_of_sum_le (fun k : {k : ι → ℤ // k ≠ 0} =>
    translatedEnvelopeCell_nonneg T (Real.pi / 2) (periodShift k.val)) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

end

end TheoremA2.GaussianCovariance
