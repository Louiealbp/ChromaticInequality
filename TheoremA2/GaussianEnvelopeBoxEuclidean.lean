import TheoremA2.GaussianEnvelopeBox
import TheoremA2.GaussianEnvelopeEuclidean
import BrascampLieb.BoxVariance

/-!
# The literal Euclidean Gibbs law on a coordinate box

Restriction commutes with the actual positive Gaussian density, and its
normalizing constant cancels through the second tilt. The result is the
normalized Lebesgue restriction used by the proved box Brascamp–Lieb theorem.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory Measure ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Matrix RealInnerProductSpace
noncomputable section

/-- Restricting an already normalized density and tilting it again gives the
same actual law as restricting the original measure and adding the potentials. -/
theorem restrict_tilted_tilted {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [NeZero μ] (f g : α → ℝ) {s : Set α}
    (hs : MeasurableSet s) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable (fun x => Real.exp (f x)) μ) :
    ((μ.tilted f).restrict s).tilted g = (μ.restrict s).tilted (f + g) := by
  have hZ : (∫ x, Real.exp (f x) ∂μ) ≠ 0 := ne_of_gt (integral_exp_pos hf)
  have hd : (∫ x, Real.exp (g x) ∂(μ.tilted f).restrict s) =
      (∫ x in s, Real.exp ((f + g) x) ∂μ) / (∫ x, Real.exp (f x) ∂μ) := by
    rw [setIntegral_tilted' f _ hs, ← integral_div]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_apply, Real.exp_add, smul_eq_mul]
      ring
  change ((μ.tilted f).restrict s).withDensity
    (fun x => ENNReal.ofReal (Real.exp (g x) /
      (∫ y, Real.exp (g y) ∂(μ.tilted f).restrict s))) = _
  have hm₁ : Measurable (fun x => ENNReal.ofReal
      (Real.exp (f x) / (∫ y, Real.exp (f y) ∂μ))) :=
    ((Real.measurable_exp.comp hfm).div_const _).ennreal_ofReal
  have hm₂ : Measurable (fun x => ENNReal.ofReal
      (Real.exp (g x) / ((∫ y in s, Real.exp ((f + g) y) ∂μ) /
        (∫ y, Real.exp (f y) ∂μ)))) :=
    ((Real.measurable_exp.comp hgm).div_const _).ennreal_ofReal
  rw [hd, Measure.tilted, restrict_withDensity hs,
    ← withDensity_mul (μ.restrict s) hm₁ hm₂]
  unfold Measure.tilted
  congr 1
  funext x
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le (integral_exp_pos hf).le),
    Real.exp_add]
  congr 1
  field_simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem boxEnvelopeLaw_eq_volume_tilted {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (b : ℝ) :
    boxEnvelopeLaw T b =
      (volume.restrict (coordinateBox b)).tilted (fun x => -fullEnvelopePotential T x) := by
  rw [boxEnvelopeLaw, covarianceGaussian_eq_volume_tilted hT,
    restrict_tilted_tilted volume _ _ (coordinateBox_measurable b)]
  · congr 1
    funext x
    simp only [Pi.add_apply, fullEnvelopePotential]
    ring
  · unfold PrincipalInverse.quadratic Matrix.mulVec dotProduct
    fun_prop
  · exact continuous_envelopePotential.neg.measurable
  · exact integrable_exp_precision hT

def euclideanCoordinateBox (b : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, |x i| ≤ b}

theorem euclideanCoordinateBox_eq (b : ℝ) :
    euclideanCoordinateBox (ι := ι) b =
      BrascampLieb.coordinateBox (EuclideanSpace.basisFun ι ℝ) b := by
  ext x
  simp only [euclideanCoordinateBox, BrascampLieb.coordinateBox, Set.mem_setOf_eq,
    EuclideanSpace.basisFun_inner]

def euclideanBoxEnvelopeLaw (T : Matrix ι ι ℝ) (b : ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (boxEnvelopeLaw T b).map (WithLp.toLp 2)

theorem euclideanBoxEnvelopeLaw_eq_volume_tilted {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (b : ℝ) :
    euclideanBoxEnvelopeLaw T b =
      (volume.restrict (euclideanCoordinateBox b)).tilted
        (fun x => -euclideanEnvelopePotential T x) := by
  unfold euclideanBoxEnvelopeLaw
  rw [boxEnvelopeLaw_eq_volume_tilted hT]
  change ((volume.restrict (coordinateBox b)).tilted (fun x => -fullEnvelopePotential T x)).map
    (MeasurableEquiv.toLp 2 (ι → ℝ)) = _
  rw [tilted_map_equiv]
  have hv : (volume : Measure (ι → ℝ)).map (MeasurableEquiv.toLp 2 (ι → ℝ)) = volume :=
    (PiLp.volume_preserving_toLp ι).map_eq
  have hr : (volume.restrict (coordinateBox (ι := ι) b)).map
      (MeasurableEquiv.toLp 2 (ι → ℝ)) = volume.restrict (euclideanCoordinateBox b) := by
    calc
      _ = ((volume : Measure (ι → ℝ)).map (MeasurableEquiv.toLp 2 (ι → ℝ))).restrict
          (euclideanCoordinateBox b) :=
        ((MeasurableEquiv.toLp 2 (ι → ℝ)).restrict_map volume (euclideanCoordinateBox b)).symm
      _ = _ := by rw [hv]
  rw [hr]
  rfl

theorem euclideanBoxEnvelopeLaw_probability {T : Matrix ι ι ℝ} (hT : T.PosDef)
    {b : ℝ} (hb : 0 < b) : IsProbabilityMeasure (euclideanBoxEnvelopeLaw T b) := by
  letI := boxEnvelopeLaw_probability hT hb
  unfold euclideanBoxEnvelopeLaw
  infer_instance

theorem integral_euclideanBoxEnvelopeLaw (T : Matrix ι ι ℝ) (b : ℝ)
    (f : EuclideanSpace ℝ ι → ℝ) :
    (∫ x, f x ∂euclideanBoxEnvelopeLaw T b) =
      ∫ x, f (WithLp.toLp 2 x) ∂boxEnvelopeLaw T b :=
  integral_map_equiv (MeasurableEquiv.toLp 2 (ι → ℝ)) f

end
end TheoremA2.GaussianCovariance
