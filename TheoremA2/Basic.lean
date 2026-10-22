import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Exact finite definitions for the analytic theorem

A spin is a Boolean vector, interpreted coordinatewise as a sign in `{-1, 1}`.
All averages below are literal normalized sums over the entire finite type.
In particular, the two successive averages defining `characteristic` are over
independent uniform spin vectors. No analytic estimates are assumed here.
-/

namespace TheoremA2

open scoped BigOperators

/-- The finite sample space of all `k` independent signs. -/
abbrev Spin (k : ℕ) := Fin k → Bool

/-- Convert a Boolean to its corresponding real sign. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

/-- An entrywise sign matrix, without additional symmetry or rank assumptions. -/
def IsSignMatrix {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ i j, S i j = 1 ∨ S i j = -1

/-- A normalized counting average. -/
noncomputable def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ a, f a

/-- A normalized counting average of complex values. -/
noncomputable def complexAverage {α : Type*} [Fintype α] (f : α → ℂ) : ℂ :=
  (Fintype.card α : ℂ)⁻¹ * ∑ a, f a

/-- The real scalar `σᵀ S τ`, with both vectors explicitly represented as signs. -/
def bilinear {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (σ τ : Spin k) : ℝ :=
  ∑ i, ∑ j, sign (σ i) * S i j * sign (τ j)

/-- The characteristic function in the paper: a literal complex exponential average. -/
noncomputable def characteristic {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) : ℂ :=
  complexAverage fun σ : Spin k =>
    complexAverage fun τ : Spin k =>
      Complex.exp (((t * bilinear S σ τ : ℝ) : ℂ) * Complex.I)

/-- The real cosine form; its equality with `characteristic` must be proved. -/
noncomputable def realCharacteristic {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) : ℝ :=
  average fun σ : Spin k =>
    average fun τ : Spin k => Real.cos (t * bilinear S σ τ)

@[simp] theorem sign_false : sign false = -1 := rfl
@[simp] theorem sign_true : sign true = 1 := rfl
@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  simpa [pow_two] using sign_sq b

@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by
  cases b <;> norm_num [sign]

@[simp] theorem card_spin (k : ℕ) : Fintype.card (Spin k) = 2 ^ k := by
  simp [Spin]

theorem average_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) : 0 ≤ average f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun a _ => hf a)

theorem average_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (hfg : ∀ a, f a ≤ g a) : average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hfg a)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

@[simp] theorem average_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp [average, nsmul_eq_mul, Fintype.card_ne_zero]

theorem average_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun a => f a + g a) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun a => f a - g a) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    average (fun a => f a * c) = average f * c := by
  simp [average, Finset.sum_mul, mul_assoc]

theorem average_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun a => c * f a) = c * average f := by
  simp [average, Finset.mul_sum, mul_left_comm]

theorem average_sum {α ι : Type*} [Fintype α] [Fintype ι] (f : α → ι → ℝ) :
    average (fun a => ∑ i, f a i) = ∑ i, average (fun a => f a i) := by
  simp only [average, Finset.mul_sum]
  exact Finset.sum_comm

theorem average_congr {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a = g a) : average f = average g := by
  congr 1
  exact funext h

end TheoremA2
