module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCompactData

@[expose] public section

/-! Exact local elliptic cutoff algebra, with no derivative of the unknown. -/
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1400000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ginibreLocalRegularityDirectional (v : E) (f : E → ℂ) (x : E) : ℂ := fderiv ℝ f x v

def ginibreLocalRegularityLaplacian {ι : Type*} [Fintype ι] (v : ι → E) (f : E → ℂ) (x : E) : ℂ :=
  ∑ i, ginibreLocalRegularityDirectional (v i) (ginibreLocalRegularityDirectional (v i) f) x

theorem ginibreLocalRegularityDirectional_product
    (f g : E → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v x : E) :
    ginibreLocalRegularityDirectional v (f*g) x =
      f x*ginibreLocalRegularityDirectional v g x+g x*ginibreLocalRegularityDirectional v f x := by
  unfold ginibreLocalRegularityDirectional
  rw [fderiv_mul (hf.differentiable (by simp)).differentiableAt (hg.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]

theorem ginibreLocalRegularityDirectional_second_product
    (f g : E → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v x : E) :
    ginibreLocalRegularityDirectional v (ginibreLocalRegularityDirectional v (f*g)) x =
      f x*ginibreLocalRegularityDirectional v (ginibreLocalRegularityDirectional v g) x+
      g x*ginibreLocalRegularityDirectional v (ginibreLocalRegularityDirectional v f) x+
      2*ginibreLocalRegularityDirectional v f x*ginibreLocalRegularityDirectional v g x := by
  have hDf : ContDiff ℝ ∞ (ginibreLocalRegularityDirectional v f) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hDg : ContDiff ℝ ∞ (ginibreLocalRegularityDirectional v g) :=
    (hg.fderiv_right (by simp)).clm_apply contDiff_const
  have he : ginibreLocalRegularityDirectional v (f*g) =
      f*ginibreLocalRegularityDirectional v g+g*ginibreLocalRegularityDirectional v f :=
    funext (fun x => ginibreLocalRegularityDirectional_product f g hf hg v x)
  rw [he]
  unfold ginibreLocalRegularityDirectional
  change fderiv ℝ ((fun y => f y*ginibreLocalRegularityDirectional v g y)+
    (fun y => g y*ginibreLocalRegularityDirectional v f y)) x v = _
  rw [fderiv_add ((hf.mul hDg).differentiable (by simp)).differentiableAt ((hg.mul hDf).differentiable (by simp)).differentiableAt]
  simp only [add_apply]
  change ginibreLocalRegularityDirectional v (f*ginibreLocalRegularityDirectional v g) x+
    ginibreLocalRegularityDirectional v (g*ginibreLocalRegularityDirectional v f) x = _
  rw [ginibreLocalRegularityDirectional_product f _ hf hDg,
    ginibreLocalRegularityDirectional_product g _ hg hDf]
  unfold ginibreLocalRegularityDirectional
  ring

theorem ginibreLocalRegularityLaplacian_product
    {ι : Type*} [Fintype ι] (v : ι → E) (f g : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    ginibreLocalRegularityLaplacian v (f*g) x =
      f x*ginibreLocalRegularityLaplacian v g x+g x*ginibreLocalRegularityLaplacian v f x+
        2*∑ i, ginibreLocalRegularityDirectional (v i) f x*ginibreLocalRegularityDirectional (v i) g x := by
  unfold ginibreLocalRegularityLaplacian
  simp_rw [ginibreLocalRegularityDirectional_second_product f g hf hg,
    Finset.sum_add_distrib,← Finset.mul_sum, mul_assoc]
  rw [← Finset.mul_sum]

theorem ginibreLocalRegularityDirectional_smooth (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (ginibreLocalRegularityDirectional v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem ginibreLocalRegularityLaplacian_smooth {ι : Type*} [Fintype ι]
    (v : ι → E) (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ginibreLocalRegularityLaplacian v f) := by
  apply ContDiff.sum
  intro i hi
  exact ginibreLocalRegularityDirectional_smooth _ (ginibreLocalRegularityDirectional_smooth f hf (v i)) (v i)

theorem ginibreLocalRegularityDirectional_compact (f : E → ℂ) (hf : HasCompactSupport f) (v : E) :
    HasCompactSupport (ginibreLocalRegularityDirectional v f) := hf.fderiv_apply ℝ v

theorem ginibreLocalRegularityLaplacian_compact {ι : Type*} [Fintype ι]
    (v : ι → E) (f : E → ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (ginibreLocalRegularityLaplacian v f) := by
  classical
  have hsum (s : Finset ι) : HasCompactSupport (fun x => ∑ i ∈ s,
      ginibreLocalRegularityDirectional (v i) (ginibreLocalRegularityDirectional (v i) f) x) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | @insert i s hi ih =>
      have hdi : HasCompactSupport (ginibreLocalRegularityDirectional (v i) (ginibreLocalRegularityDirectional (v i) f)) :=
        ginibreLocalRegularityDirectional_compact _ (ginibreLocalRegularityDirectional_compact f hf (v i)) (v i)
      have he : (fun x => ∑ j ∈ insert i s, ginibreLocalRegularityDirectional (v j) (ginibreLocalRegularityDirectional (v j) f) x) =
          ginibreLocalRegularityDirectional (v i) (ginibreLocalRegularityDirectional (v i) f)+
          (fun x => ∑ j ∈ s, ginibreLocalRegularityDirectional (v j) (ginibreLocalRegularityDirectional (v j) f) x) := by
        funext x
        simp only [Finset.sum_insert hi, Pi.add_apply]
      rw [he]
      exact hdi.add ih
  exact hsum Finset.univ

#print axioms ginibreLocalRegularityLaplacian_product
end
end GinibrePoincare
