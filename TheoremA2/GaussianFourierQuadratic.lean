import TheoremA2.GaussianFourierProduct

/-!
# Directional Gaussian second Fourier moments

The coordinate-pair formulas are assembled into the complete quadratic identity,
then transported through the actual covariance square root. Singular covariance
matrices remain permitted.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dot_sq_fourier_eq_sum (v b x : ι → ℝ) :
    ((v ⬝ᵥ x : ℝ) : ℂ) ^ 2 * fourier b x =
      ∑ i, ∑ j, ((v i * v j : ℝ) : ℂ) * ((x i : ℂ) * (x j : ℂ) * fourier b x) := by
  simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integrable_dot_sq_fourier (v b : ι → ℝ) :
    Integrable (fun x : ι → ℝ => ((v ⬝ᵥ x : ℝ) : ℂ) ^ 2 * fourier b x)
      (standardGaussian (ι := ι)) := by
  simp_rw [dot_sq_fourier_eq_sum]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_coordinate_pair_fourier b i j).const_mul ((v i * v j : ℝ) : ℂ)

theorem coordinate_pair_contraction (v b : ι → ℝ) :
    (∑ i, ∑ j, ((v i * v j : ℝ) : ℂ) *
      ((if i = j then (1 : ℂ) else 0) - (b i : ℂ) * b j)) =
      ((normSq v - (v ⬝ᵥ b) ^ 2 : ℝ) : ℂ) := by
  have hdiag : (∑ i, ∑ j, ((v i * v j : ℝ) : ℂ) *
      (if i = j then (1 : ℂ) else 0)) = (normSq v : ℂ) := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, normSq, Complex.ofReal_sum, pow_two]
  have hcross : (∑ i, ∑ j, ((v i * v j : ℝ) : ℂ) * ((b i : ℂ) * b j)) =
      ((v ⬝ᵥ b : ℝ) : ℂ) ^ 2 := by
    simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hdiag, hcross, Complex.ofReal_sub, Complex.ofReal_pow]

/-- The complete directional second Fourier moment of the standard product Gaussian. -/
theorem standard_dot_sq_fourier (v b : ι → ℝ) :
    (∫ x : ι → ℝ, ((v ⬝ᵥ x : ℝ) : ℂ) ^ 2 * fourier b x ∂standardGaussian) =
      ((normSq v - (v ⬝ᵥ b) ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(normSq b : ℝ) / 2) := by
  have hterm (i j : ι) : Integrable
      (fun x : ι → ℝ => ((v i * v j : ℝ) : ℂ) *
        ((x i : ℂ) * (x j : ℂ) * fourier b x)) (standardGaussian (ι := ι)) :=
    (integrable_coordinate_pair_fourier b i j).const_mul _
  calc
    _ = ∫ x : ι → ℝ, ∑ i, ∑ j, ((v i * v j : ℝ) : ℂ) *
        ((x i : ℂ) * (x j : ℂ) * fourier b x) ∂standardGaussian := by
      exact integral_congr_ae (Filter.Eventually.of_forall (dot_sq_fourier_eq_sum v b))
    _ = ∑ i, ∑ j, ∫ x : ι → ℝ, ((v i * v j : ℝ) : ℂ) *
        ((x i : ℂ) * (x j : ℂ) * fourier b x) ∂standardGaussian := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hterm i j)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hterm i j)
    _ = ∑ i, ∑ j, ((v i * v j : ℝ) : ℂ) *
        (((if i = j then (1 : ℂ) else 0) - (b i : ℂ) * b j) *
          Complex.exp (-(normSq b : ℝ) / 2)) := by
      simp_rw [integral_const_mul, standard_coordinate_pair_fourier]
    _ = (∑ i, ∑ j, ((v i * v j : ℝ) : ℂ) *
        ((if i = j then (1 : ℂ) else 0) - (b i : ℂ) * b j)) *
          Complex.exp (-(normSq b : ℝ) / 2) := by
      simp only [← mul_assoc, Finset.sum_mul]
    _ = _ := by rw [coordinate_pair_contraction]

theorem dot_sqrt {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (v b : ι → ℝ) :
    ((CFC.sqrt T)ᵀ *ᵥ v) ⬝ᵥ ((CFC.sqrt T)ᵀ *ᵥ b) = v ⬝ᵥ (T *ᵥ b) := by
  have hC : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  have hCt : (CFC.sqrt T)ᵀ = CFC.sqrt T := by simpa using hC.isHermitian.eq
  rw [hCt, dotProduct_comm (CFC.sqrt T *ᵥ v), symmetric_bilinear hC.isHermitian,
    Matrix.mulVec_mulVec, CFC.sqrt_mul_sqrt_self T hT.nonneg]

/-- The actual matrix Gaussian Fourier moment, for every direction and every frequency. -/
theorem covariance_dot_sq_fourier {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (v b : ι → ℝ) :
    (∫ x : ι → ℝ, ((v ⬝ᵥ x : ℝ) : ℂ) ^ 2 * fourier b x ∂covarianceGaussian T) =
      ((quadratic T v - (v ⬝ᵥ (T *ᵥ b)) ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(quadratic T b : ℝ) / 2) := by
  have hd (a x : ι → ℝ) : a ⬝ᵥ (CFC.sqrt T *ᵥ x) = ((CFC.sqrt T)ᵀ *ᵥ a) ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  unfold covarianceGaussian
  rw [integral_map (measurable_mulVec (CFC.sqrt T)).aemeasurable (by
    unfold fourier dotProduct
    fun_prop)]
  simp only [fourier, hd]
  change (∫ x : ι → ℝ, (((CFC.sqrt T)ᵀ *ᵥ v) ⬝ᵥ x : ℝ) ^ 2 *
    fourier ((CFC.sqrt T)ᵀ *ᵥ b) x ∂standardGaussian) = _
  rw [standard_dot_sq_fourier, normSq_sqrt_transpose hT, normSq_sqrt_transpose hT,
    dot_sqrt hT]

end

end TheoremA2.GaussianCovariance
