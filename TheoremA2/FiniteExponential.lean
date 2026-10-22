import TheoremA2.ConvexSupport

/-!
# Differentiation of finite exponential families

Weights, normalization, means, and their derivatives are constructed from
literal finite sums. The covariance identity is proved from these sums.
-/

namespace TheoremA2.FiniteExponential

open TheoremA2.ConvexSupport
open scoped BigOperators
noncomputable section

variable {Ω E : Type*} [Fintype Ω] [Nonempty Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def weight (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) (ω : Ω) : ℝ :=
  Real.exp (a ω + L ω t)

def partition (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) : ℝ :=
  ∑ ω, weight a L t ω

theorem partition_pos (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) :
    0 < partition a L t := by
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

def law (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) : FiniteProbability Ω where
  mass ω := weight a L t ω / partition a L t
  nonneg ω := (div_pos (Real.exp_pos _) (partition_pos a L t)).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (partition_pos a L t))

def logPartition (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) : ℝ :=
  Real.log (partition a L t)

def logGradient (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) : E →L[ℝ] ℝ :=
  ∑ ω, (law a L t).mass ω • L ω

def expectationGradient (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ)
    (f : Ω → ℝ) (t : E) : E →L[ℝ] ℝ :=
  ∑ ω, ((law a L t).mass ω * f ω) • (L ω - logGradient a L t)

theorem hasFDerivAt_weight (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) (ω : Ω) :
    HasFDerivAt (fun t => weight a L t ω) (weight a L t ω • L ω) t :=
  ((L ω).hasFDerivAt.const_add (a ω)).exp

theorem hasFDerivAt_partition (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) :
    HasFDerivAt (partition a L) (∑ ω, weight a L t ω • L ω) t :=
  HasFDerivAt.fun_sum fun ω _ => hasFDerivAt_weight a L t ω

theorem hasFDerivAt_logPartition (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) :
    HasFDerivAt (logPartition a L) (logGradient a L t) t := by
  have hg : logGradient a L t = (partition a L t)⁻¹ •
      ∑ ω, weight a L t ω • L ω := by
    unfold logGradient law
    simp only [Finset.smul_sum, smul_smul, div_eq_mul_inv,
      mul_comm (partition a L t)⁻¹]
  rw [hg]
  exact (hasFDerivAt_partition a L t).log (ne_of_gt (partition_pos a L t))

theorem mass_eq_exp (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) (ω : Ω) :
    (law a L t).mass ω = Real.exp (a ω + L ω t - logPartition a L t) := by
  rw [Real.exp_sub, logPartition, Real.exp_log (partition_pos a L t)]
  rfl

theorem hasFDerivAt_mass (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t : E) (ω : Ω) :
    HasFDerivAt (fun t => (law a L t).mass ω)
      ((law a L t).mass ω • (L ω - logGradient a L t)) t := by
  simp_rw [mass_eq_exp]
  exact (((L ω).hasFDerivAt.const_add (a ω)).sub
    (hasFDerivAt_logPartition a L t)).exp

theorem hasFDerivAt_expectation (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ)
    (f : Ω → ℝ) (t : E) :
    HasFDerivAt (fun t => (law a L t).expectation f) (expectationGradient a L f t) t := by
  unfold FiniteProbability.expectation expectationGradient
  convert HasFDerivAt.fun_sum
    (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) => (hasFDerivAt_mass a L t ω).mul_const (f ω)) using 1
  simp only [smul_smul, mul_comm (f _)]

theorem logGradient_apply (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t v : E) :
    logGradient a L t v = (law a L t).expectation (fun ω => L ω v) := by
  simp [logGradient, FiniteProbability.expectation]

theorem expectationGradient_apply (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ)
    (f : Ω → ℝ) (t v : E) :
    expectationGradient a L f t v =
      (law a L t).expectation (fun ω => f ω * L ω v) -
        (law a L t).expectation f * (law a L t).expectation (fun ω => L ω v) := by
  simp only [expectationGradient, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul, logGradient_apply, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  simp only [FiniteProbability.expectation, mul_assoc]

theorem fderiv_logPartition_apply (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (t v : E) :
    fderiv ℝ (logPartition a L) t v = (law a L t).expectation (fun ω => L ω v) := by
  rw [(hasFDerivAt_logPartition a L t).fderiv, logGradient_apply]

/-- The exact Hessian of the log partition in two arbitrary directions. -/
theorem second_direction_logPartition (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ)
    (t v w : E) :
    fderiv ℝ (fun x => fderiv ℝ (logPartition a L) x v) t w =
      (law a L t).expectation (fun ω => L ω v * L ω w) -
        (law a L t).expectation (fun ω => L ω v) *
          (law a L t).expectation (fun ω => L ω w) := by
  simp_rw [fderiv_logPartition_apply]
  rw [(hasFDerivAt_expectation a L (fun ω => L ω v) t).fderiv,
    expectationGradient_apply]

theorem contDiff_weight (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (ω : Ω) :
    ContDiff ℝ ⊤ (fun t => weight a L t ω) := by
  unfold weight
  fun_prop

theorem contDiff_partition (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) :
    ContDiff ℝ ⊤ (partition a L) := by
  unfold partition
  exact ContDiff.sum fun ω _ => contDiff_weight a L ω

theorem contDiff_logPartition (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) :
    ContDiff ℝ ⊤ (logPartition a L) :=
  (contDiff_partition a L).log fun t => ne_of_gt (partition_pos a L t)

theorem contDiff_expectation (a : Ω → ℝ) (L : Ω → E →L[ℝ] ℝ) (f : Ω → ℝ) :
    ContDiff ℝ ⊤ (fun t => (law a L t).expectation f) := by
  unfold FiniteProbability.expectation
  apply ContDiff.sum
  intro ω _
  simp_rw [mass_eq_exp]
  exact (((contDiff_const.add (L ω).contDiff).sub (contDiff_logPartition a L)).exp).mul contDiff_const

end
end TheoremA2.FiniteExponential
