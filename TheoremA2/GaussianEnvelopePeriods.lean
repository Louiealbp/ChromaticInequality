import TheoremA2.GaussianEnvelopeBox
import TheoremA2.GaussianEnvelopeEuclidean
import TheoremA2.PeriodicCells
import Mathlib.MeasureTheory.Function.Floor

/-!
# Genuine countable Gaussian period decomposition

Period cells are the actual fibers of the centered integer-period map. They are
measurable and pairwise disjoint. Each selected cell is bounded by its closed
translated central cell, so no boundary-zero assertion is assumed.
-/

namespace TheoremA2.GaussianCovariance

open MeasureTheory ProbabilityTheory Set
open TheoremA2.PrincipalInverse
open scoped NNReal ENNReal BigOperators Matrix MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def periodConfiguration (x : ι → ℝ) : ι → ℤ := fun i => PeriodicCells.period (x i)

def centeredCoordinates (x : ι → ℝ) : ι → ℝ := fun i => PeriodicCells.remainder (x i)

def periodicEnvelopeWeight (x : ι → ℝ) : ℝ := envelopeWeight (centeredCoordinates x)

def selectedPeriodCell (k : ι → ℤ) : Set (ι → ℝ) := {x | periodConfiguration x = k}

theorem measurable_periodConfiguration : Measurable (periodConfiguration (ι := ι)) := by
  apply measurable_pi_lambda
  intro i
  unfold periodConfiguration PeriodicCells.period
  fun_prop

theorem measurable_centeredCoordinates : Measurable (centeredCoordinates (ι := ι)) := by
  apply measurable_pi_lambda
  intro i
  unfold centeredCoordinates PeriodicCells.remainder
  have hc : Measurable (fun n : ℤ => (n : ℝ)) := measurable_of_countable _
  have hp : Measurable (fun x : ι → ℝ => PeriodicCells.period (x i)) :=
    (measurable_pi_apply i).comp measurable_periodConfiguration
  exact (measurable_pi_apply i).sub
    (measurable_const.mul (hc.comp hp))

theorem measurable_periodicEnvelopeWeight : Measurable (periodicEnvelopeWeight (ι := ι)) :=
  continuous_envelopeWeight.measurable.comp measurable_centeredCoordinates

theorem selectedPeriodCell_measurable (k : ι → ℤ) : MeasurableSet (selectedPeriodCell k) :=
  measurable_periodConfiguration (measurableSet_singleton k)

theorem periodicEnvelopeWeight_pos (x : ι → ℝ) : 0 < periodicEnvelopeWeight x :=
  envelopeWeight_pos _

theorem periodicEnvelopeWeight_le_one (x : ι → ℝ) : periodicEnvelopeWeight x ≤ 1 :=
  envelopeWeight_le_one _

theorem integrable_periodicEnvelopeWeight (T : Matrix ι ι ℝ) :
    Integrable periodicEnvelopeWeight (covarianceGaussian T) := by
  apply (integrable_const (1 : ℝ)).mono' measurable_periodicEnvelopeWeight.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (periodicEnvelopeWeight_pos x)]
    exact periodicEnvelopeWeight_le_one x)

theorem period_zero_mem_box {x : ι → ℝ} (hx : periodConfiguration x = 0) :
    x ∈ coordinateBox (Real.pi / 2) := by
  intro i
  have hi := congrFun hx i
  change PeriodicCells.period (x i) = 0 at hi
  simpa only [PeriodicCells.remainder, hi,
    Int.cast_zero, mul_zero, sub_zero] using PeriodicCells.abs_remainder_le (x i)

theorem outside_box_covered :
    (coordinateBox (ι := ι) (Real.pi / 2))ᶜ ⊆
      ⋃ k : {k : ι → ℤ // k ≠ 0}, selectedPeriodCell k.val := by
  intro x hx
  have hk : periodConfiguration x ≠ 0 := fun h => hx (period_zero_mem_box h)
  exact Set.mem_iUnion.mpr ⟨⟨periodConfiguration x, hk⟩, rfl⟩

theorem selectedPeriodCell_disjoint :
    _root_.Pairwise (fun k l : {k : ι → ℤ // k ≠ 0} =>
      Disjoint (selectedPeriodCell k.val) (selectedPeriodCell l.val)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hkl (Subtype.ext (hx.symm.trans hy))

theorem integrable_translated_envelope {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (z : ι → ℝ) : Integrable (fun x => covarianceDensity T (z + x) * envelopeWeight x) := by
  have hi := (integrable_covarianceDensity hT).comp_add_left z
  apply hi.mono'
    ((measurable_covarianceDensity T).comp (measurable_const.add measurable_id) |>.mul
      continuous_envelopeWeight.measurable |>.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  change |covarianceDensity T (z + x) * envelopeWeight x| ≤ covarianceDensity T (z + x)
  rw [abs_of_nonneg
    (mul_nonneg (covarianceDensity_nonneg T _) (envelopeWeight_pos x).le)]
  exact mul_le_of_le_one_right (covarianceDensity_nonneg T _) (envelopeWeight_le_one x)

/-- A selected half-open period is bounded by the literal closed translated cell. -/
theorem selectedPeriodCell_integral_le {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (k : ι → ℤ) :
    (∫ x in selectedPeriodCell k, periodicEnvelopeWeight x ∂covarianceGaussian T) ≤
      translatedEnvelopeCell T (Real.pi / 2) (fun i => Real.pi * k i) := by
  let z : ι → ℝ := fun i => Real.pi * k i
  have hleft := (integrable_covarianceGaussian_iff hT periodicEnvelopeWeight).mp
    (integrable_periodicEnvelopeWeight T)
  have hright := (integrable_translated_envelope hT z).indicator (coordinateBox_measurable (Real.pi / 2))
  rw [setIntegral_covarianceGaussian_eq hT,
    ← integral_indicator (selectedPeriodCell_measurable k)]
  rw [← integral_add_left_eq_self
    ((selectedPeriodCell k).indicator (fun x => covarianceDensity T x * periodicEnvelopeWeight x)) z]
  unfold translatedEnvelopeCell
  rw [← integral_indicator (coordinateBox_measurable (Real.pi / 2))]
  apply integral_mono ((hleft.indicator (selectedPeriodCell_measurable k)).comp_add_left z) hright
  intro x
  change (selectedPeriodCell k).indicator
    (fun y => covarianceDensity T y * periodicEnvelopeWeight y) (z + x) ≤
    (coordinateBox (Real.pi / 2)).indicator
      (fun y => covarianceDensity T (z + y) * envelopeWeight y) x
  by_cases hx : z + x ∈ selectedPeriodCell k
  · have hcoord : centeredCoordinates (z + x) = x := by
      funext i
      have hi := congrFun hx i
      change PeriodicCells.period ((z + x) i) = k i at hi
      change (z + x) i - Real.pi * PeriodicCells.period ((z + x) i) = x i
      rw [hi]
      dsimp [z]
      ring
    have hbox : x ∈ coordinateBox (Real.pi / 2) := by
      intro i
      rw [← congrFun hcoord i]
      exact PeriodicCells.abs_remainder_le _
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hbox]
    change covarianceDensity T (z + x) * envelopeWeight (centeredCoordinates (z + x)) ≤ _
    rw [hcoord]
  · rw [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun x _ =>
      mul_nonneg (covarianceDensity_nonneg T _) (envelopeWeight_pos x).le) x

/-- The periodic error outside the central box is controlled by every nonzero
translated cell. Integrability and the countable sum are genuine. -/
theorem periodic_tail_le_cells {T : Matrix ι ι ℝ} (hT : T.PosDef)
    (hs : Summable (fun k : {k : ι → ℤ // k ≠ 0} =>
      translatedEnvelopeCell T (Real.pi / 2) (fun i => Real.pi * k.val i))) :
    (∫ x in (coordinateBox (Real.pi / 2))ᶜ, periodicEnvelopeWeight x
      ∂covarianceGaussian T) ≤
      ∑' k : {k : ι → ℤ // k ≠ 0},
        translatedEnvelopeCell T (Real.pi / 2) (fun i => Real.pi * k.val i) := by
  have hi := integrable_periodicEnvelopeWeight T
  have hsum := hasSum_integral_iUnion
    (fun k : {k : ι → ℤ // k ≠ 0} => selectedPeriodCell_measurable k.val)
    selectedPeriodCell_disjoint hi.integrableOn
  calc
    _ ≤ ∫ x in ⋃ k : {k : ι → ℤ // k ≠ 0}, selectedPeriodCell k.val,
        periodicEnvelopeWeight x ∂covarianceGaussian T :=
      setIntegral_mono_set hi.integrableOn
        (Filter.Eventually.of_forall (fun x => (periodicEnvelopeWeight_pos x).le))
        (Filter.Eventually.of_forall (fun _ hx => outside_box_covered hx))
    _ = ∑' k : {k : ι → ℤ // k ≠ 0},
        ∫ x in selectedPeriodCell k.val, periodicEnvelopeWeight x ∂covarianceGaussian T :=
      hsum.tsum_eq.symm
    _ ≤ _ := hsum.summable.tsum_le_tsum (fun k => selectedPeriodCell_integral_le hT k.val) hs

end

end TheoremA2.GaussianCovariance
