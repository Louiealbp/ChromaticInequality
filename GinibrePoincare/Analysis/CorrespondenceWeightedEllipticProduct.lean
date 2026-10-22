module
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticC1Tests
@[expose] public section
open MeasureTheory Set
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_compact_C1_product
    (u g : Lp ℝ 2 (volume : Measure E)) (v : E)
    (hw : ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*u x))
    (q : E→ℝ) (hq : ContDiff ℝ 1 q) (hc : HasCompactSupport q) :
    ∃U G : Lp ℝ 2 (volume : Measure E),
      (U : E→ℝ)=ᵐ[volume](fun x=>q x*u x) ∧
      (G : E→ℝ)=ᵐ[volume](fun x=>q x*g x+fderiv ℝ q x v*u x) ∧
      ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*G x)= -(∫x, fderiv ℝ θ x v*U x) := by
  let d : E→ℝ := fun x=>fderiv ℝ q x v
  have hd : Continuous d := (hq.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdc : HasCompactSupport d := hc.fderiv_apply ℝ v
  have ht : MemLp q ⊤ (volume : Measure E) := hq.continuous.memLp_top_of_hasCompactSupport hc volume
  have hdt : MemLp d ⊤ (volume : Measure E) := hd.memLp_top_of_hasCompactSupport hdc volume
  have hU : MemLp (fun x=>q x*u x) 2 volume := ht.fun_mul (r:=2) (Lp.memLp u)
  have hG : MemLp (fun x=>q x*g x+d x*u x) 2 volume :=
    (ht.fun_mul (r:=2) (Lp.memLp g)).add (hdt.fun_mul (r:=2) (Lp.memLp u))
  refine ⟨hU.toLp _, hG.toLp _, hU.coeFn_toLp, hG.coeFn_toLp,?_⟩
  intro θ hθ hθc
  have hψ := correspondenceWeightedElliptic_weak_test_C1 u g v hw (q*θ)
    (hq.mul (hθ.of_le (by norm_num))) (hc.mul_right)
  have he (x) : fderiv ℝ (q*θ) x v=d x*θ x+q x*fderiv ℝ θ x v := by
    rw [fderiv_mul (hq.differentiable (by norm_num) x) (hθ.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    dsimp [d]
    ring
  simp_rw [he] at hψ
  have hi1 : Integrable (fun x=>d x*θ x*u x) volume := by
    have hm : MemLp (fun x=>d x*θ x) 2 volume :=
      (hd.mul hθ.continuous).memLp_of_hasCompactSupport (hdc.mul_right)
    exact hm.integrable_mul (Lp.memLp u)
  have hi2 : Integrable (fun x=>q x*fderiv ℝ θ x v*u x) volume := by
    have hm : MemLp (fun x=>q x*fderiv ℝ θ x v) 2 volume :=
      (hq.continuous.mul ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport (hc.mul_right)
    exact hm.integrable_mul (Lp.memLp u)
  have hi3 : Integrable (fun x=>q x*θ x*g x) volume := by
    have hm : MemLp (fun x=>q x*θ x) 2 volume :=
      (hq.continuous.mul hθ.continuous).memLp_of_hasCompactSupport (hc.mul_right)
    exact hm.integrable_mul (Lp.memLp g)
  have hψ' : (∫x, q x*θ x*g x)= -(∫x, d x*θ x*u x)-(∫x, q x*fderiv ℝ θ x v*u x) := by
    have heq : (fun x=>(d x*θ x+q x*fderiv ℝ θ x v)*u x)=
        (fun x=>d x*θ x*u x)+(fun x=>q x*fderiv ℝ θ x v*u x) := by funext x; dsimp; ring
    rw [heq] at hψ
    change (∫x, q x*θ x*g x)= -(∫x, d x*θ x*u x+q x*fderiv ℝ θ x v*u x) at hψ
    rw [integral_add hi1 hi2] at hψ
    linarith
  have hleft : (∫x, θ x*(hG.toLp _) x)=(∫x, q x*θ x*g x)+(∫x, d x*θ x*u x) := by
    calc
      _ = ∫x, q x*θ x*g x+d x*θ x*u x := by
        apply integral_congr_ae
        filter_upwards [hG.coeFn_toLp] with x hx
        rw [hx]
        ring
      _ = _ := integral_add hi3 hi1
  have hright : (∫x, fderiv ℝ θ x v*(hU.toLp _) x)=∫x, q x*fderiv ℝ θ x v*u x := by
    apply integral_congr_ae
    filter_upwards [hU.coeFn_toLp] with x hx
    rw [hx]
    ring
  rw [hleft, hright]
  linarith
#print axioms correspondenceWeightedElliptic_compact_C1_product
end
end GinibrePoincare
