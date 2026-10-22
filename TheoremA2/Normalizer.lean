import TheoremA2.Imports
import TheoremA2.SecondMoment

/-!
# The normalizer lower bound in equation (77)

The Gaussian-weighted finite-spin normalizer is bounded below without any
assumptions on the real matrix or the scalar parameter. The final corollary
is explicitly conditional on a pointwise lower bound for a reference function;
it does not construct that reference function or prove Theorem A.2.
-/

namespace TheoremA2

open scoped BigOperators

/-- Finite Jensen inequality for the exponential, proved from its tangent-line bound. -/
theorem exp_average_le_average_exp {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : Real.exp (average f) ≤ average (fun a => Real.exp (f a)) := by
  let m := average f
  have hpoint (a : α) : Real.exp m * (1 + f a - m) ≤ Real.exp (f a) := by
    calc
      Real.exp m * (1 + f a - m) = Real.exp m * ((f a - m) + 1) := by ring
      _ ≤ Real.exp m * Real.exp (f a - m) :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
      _ = Real.exp (f a) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have h := average_mono hpoint
  have hm : average (fun a => Real.exp m * (1 + f a - m)) = Real.exp m := by
    rw [average_const_mul, average_sub, average_add, average_const, average_const]
    dsimp [m]
    ring
  rw [hm] at h
  exact h

/-- The squared Frobenius norm, written explicitly as a finite sum. -/
def frobeniusSq {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) : ℝ :=
  ∑ i, ∑ j, B i j ^ 2

/-- The squared Euclidean norm of `Bᵀσ`. -/
def projectedEnergy {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) (σ : Spin r) : ℝ :=
  ∑ j, (∑ i, B i j * sign (σ i)) ^ 2

/-- Exact orthogonality calculation for a rectangular real matrix. -/
theorem average_projectedEnergy {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℝ) :
    average (projectedEnergy B) = frobeniusSq B := by
  unfold projectedEnergy frobeniusSq
  rw [average_sum]
  simp_rw [average_linear_sq]
  exact Finset.sum_comm

/-- The finite-spin partition function with a negative quadratic weight. -/
noncomputable def gaussianSpinNormalizer {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) : ℝ :=
  average (fun σ : Spin r => Real.exp (-lam * projectedEnergy B σ))

/-- The unconditional Jensen step of equation (77), valid also for rectangular matrices. -/
theorem gaussianSpinNormalizer_lower_bound {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) :
    Real.exp (-lam * frobeniusSq B) ≤ gaussianSpinNormalizer B lam := by
  have h := exp_average_le_average_exp (fun σ : Spin r => -lam * projectedEnergy B σ)
  rw [average_const_mul, average_projectedEnergy] at h
  exact h

/-- The finite-spin normalizer of a scalar reference function. -/
noncomputable def referenceNormalizer {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) (F : ℝ → ℝ) : ℝ :=
  average (fun σ : Spin r => ∏ j, F (∑ i, B i j * sign (σ i)))

/--
The rest of equation (77). This corollary explicitly assumes the scalar
majorant property (62); it does not assert the existence of a suitable `F`.
-/
theorem referenceNormalizer_lower_bound {r s : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) (lam : ℝ) (F : ℝ → ℝ)
    (hF : ∀ x : ℝ, Real.exp (-lam * x ^ 2) ≤ F x) :
    Real.exp (-lam * frobeniusSq B) ≤ referenceNormalizer B F := by
  apply le_trans (gaussianSpinNormalizer_lower_bound B lam)
  apply average_mono
  intro σ
  calc
    Real.exp (-lam * projectedEnergy B σ) =
        ∏ j : Fin s, Real.exp (-lam * (∑ i, B i j * sign (σ i)) ^ 2) := by
      unfold projectedEnergy
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ ∏ j, F (∑ i, B i j * sign (σ i)) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact (Real.exp_pos _).le
      · intro j _
        exact hF _

end TheoremA2
