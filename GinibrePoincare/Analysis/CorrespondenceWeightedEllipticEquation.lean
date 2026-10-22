module
public import GinibrePoincare.Analysis.CorrespondenceWeightedEllipticReal
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityTestIntegrability
@[expose] public section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def correspondenceWeightedEllipticGenerator {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (ρ θ : E→ℝ) (x : E) : ℝ :=
  ∑i, (fderiv ℝ (fun y=>fderiv ℝ θ y (b i)) x (b i)+
    (ρ x)⁻¹*fderiv ℝ ρ x (b i)*fderiv ℝ θ x (b i))

/-- A literal weighted-generator annihilator satisfies the actual local
constant-principal-part elliptic divergence equation. -/
theorem correspondenceWeightedElliptic_annihilator_equation
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ρ : E→ℝ) (hρ : ContDiff ℝ 1 ρ) (hp : ∀x, 0<ρ x)
    [IsFiniteMeasure (correspondenceWeightedEllipticMeasure ρ)]
    (u : E→ℝ) (hu : MemLp u 2 (correspondenceWeightedEllipticMeasure ρ))
    (hA : ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, u x*correspondenceWeightedEllipticGenerator b ρ θ x∂correspondenceWeightedEllipticMeasure ρ)=0)
    (θ : E→ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    (∫x, (ρ x*u x)*(∑i, fderiv ℝ (fun y=>fderiv ℝ θ y (b i)) x (b i)))=
      -(∑i,∫x, (u x*fderiv ℝ ρ x (b i))*fderiv ℝ θ x (b i)) := by
  classical
  have hul := correspondenceWeightedElliptic_locallyIntegrable ρ hρ.continuous hp u hu
  let D := fun i x=>fderiv ℝ θ x (b i)
  let DD := fun i x=>fderiv ℝ (D i) x (b i)
  have hD (i) : ContDiff ℝ ∞ (D i) := (hθ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDDs (i) : ContDiff ℝ ∞ (DD i) := ((hD i).fderiv_right (by simp)).clm_apply contDiff_const
  have hDD (i) : Continuous (DD i) := (hDDs i).continuous
  have hDi (i) : Continuous (fun x=>fderiv ℝ ρ x (b i)) :=
    (hρ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi1 (i) : Integrable (fun x=>u x*(ρ x*DD i x)) volume :=
    hul.integrable_smul_right_of_hasCompactSupport (hρ.continuous.mul (hDD i))
      (((hc.fderiv_apply ℝ (b i)).fderiv_apply ℝ (b i)).mul_left)
  have hi2 (i) : Integrable (fun x=>u x*(fderiv ℝ ρ x (b i)*D i x)) volume :=
    hul.integrable_smul_right_of_hasCompactSupport ((hDi i).mul (hD i).continuous)
      ((hc.fderiv_apply ℝ (b i)).mul_left)
  have hs1 := integrable_finsetSum Finset.univ (fun i _=>hi1 i)
  have hs2 := integrable_finsetSum Finset.univ (fun i _=>hi2 i)
  have he := hA θ hθ hc
  rw [correspondenceWeightedElliptic_integral_density ρ _ hρ.continuous hp] at he
  have hpt (x) : ρ x*(u x*correspondenceWeightedEllipticGenerator b ρ θ x)=
      (∑i, u x*(ρ x*DD i x))+(∑i, u x*(fderiv ℝ ρ x (b i)*D i x)) := by
    unfold correspondenceWeightedEllipticGenerator
    rw [Finset.mul_sum, Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [DD, D]
    field_simp [(hp x).ne']
  simp_rw [hpt] at he
  rw [integral_add hs1 hs2, integral_finsetSum _ (fun i _=>hi1 i),
    integral_finsetSum _ (fun i _=>hi2 i)] at he
  have hleft : (∫x, (ρ x*u x)*(∑i, DD i x))=∑i,∫x, u x*(ρ x*DD i x) := by
    rw [← integral_finsetSum _ (fun i _=>hi1 i)]
    apply integral_congr_ae
    exact ae_of_all volume fun x=>by simp [Finset.mul_sum]; ring
  have hright : (∑i,∫x, (u x*fderiv ℝ ρ x (b i))*D i x)=
      ∑i,∫x, u x*(fderiv ℝ ρ x (b i)*D i x) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    exact ae_of_all volume fun x=>mul_assoc _ _ _
  change (∫x, (ρ x*u x)*(∑i, DD i x))= -(∑i,∫x, (u x*fderiv ℝ ρ x (b i))*D i x)
  rw [hleft, hright]
  linarith
#print axioms correspondenceWeightedElliptic_annihilator_equation
end
end GinibrePoincare
