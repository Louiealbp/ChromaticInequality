import TheoremA2.PaddedDecoderGaussian

/-!
# Products of the actual scalar decoder

This is a comparison distribution on integer vectors. It does not assert
independence of any random cell indices or of Gaussian observations.
-/

namespace TheoremA2.PaddedDecoder

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The product comparison probability for a full integer cell label. -/
def jointProbability (v : ℝ) (w : ι → ℝ) (k : ι → ℤ) : ℝ :=
  ∏ i, probability v (k i) (w i)

theorem summable_probability {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (w : ℝ) :
    Summable (fun j : ℤ => probability v j w) :=
  (denominator_global_bound hv hv1 w).1.div_const _

theorem jointProbability_pos {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (w : ι → ℝ) (k : ι → ℤ) : 0 < jointProbability v w k := by
  exact Finset.prod_pos fun i _ => probability_pos hv hv1 _ _

theorem jointProbability_le_one {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (w : ι → ℝ) (k : ι → ℤ) : jointProbability v w k ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i _
    exact (probability_pos hv hv1 _ _).le
  · intro i _
    exact probability_le_one hv hv1 _ _

/-- Any finite collection of distinct integer-vector labels has total decoder mass at most one.
The proof includes it in the product of its coordinate ranges, without any independence premise. -/
theorem sum_jointProbability_le_one {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (w : ι → ℝ) (J : Finset (ι → ℤ)) :
    ∑ k ∈ J, jointProbability v w k ≤ 1 := by
  classical
  let R : ι → Finset ℤ := fun i => J.image (fun k => k i)
  have hsub : J ⊆ Fintype.piFinset R := by
    intro k hk
    apply Fintype.mem_piFinset.2
    intro i
    exact Finset.mem_image.2 ⟨k, hk, rfl⟩
  have hpartial (i : ι) : ∑ j ∈ R i, probability v j (w i) ≤ 1 := by
    have h := (summable_probability hv hv1 (w i)).sum_le_tsum (R i)
      (fun j _ => (probability_pos hv hv1 j (w i)).le)
    rwa [tsum_probability hv hv1 (w i)] at h
  calc
    (∑ k ∈ J, jointProbability v w k) ≤
        ∑ k ∈ Fintype.piFinset R, jointProbability v w k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => (jointProbability_pos hv hv1 w k).le)
    _ = ∏ i, ∑ j ∈ R i, probability v j (w i) := by
      unfold jointProbability
      exact (Finset.prod_univ_sum R (fun i j => probability v j (w i))).symm
    _ ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro i _
        exact Finset.sum_nonneg fun j _ => (probability_pos hv hv1 j (w i)).le
      · intro i _
        exact hpartial i

/-- The entire countable integer-vector comparison mass is summable and at most one. -/
theorem tsum_jointProbability_le_one {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (w : ι → ℝ) :
    Summable (jointProbability v w) ∧ (∑' k, jointProbability v w k) ≤ 1 := by
  have h0 (k : ι → ℤ) := (jointProbability_pos hv hv1 w k).le
  have hJ := sum_jointProbability_le_one hv hv1 w
  have hs : Summable (jointProbability v w) := summable_of_sum_le h0 hJ
  exact ⟨hs, hs.tsum_le_of_sum_le hJ⟩

/-- The joint decoder remains measurable for arbitrary measurable scalar observations. -/
theorem measurable_jointProbability {Ω : Type*} [MeasurableSpace Ω] {v : ℝ}
    (hv : 0 < v) (hv1 : v ≤ 1) (w : Ω → ι → ℝ)
    (hw : ∀ i, Measurable (fun ω => w ω i)) (k : ι → ℤ) :
    Measurable (fun ω => jointProbability v (w ω) k) := by
  apply Finset.measurable_prod
  intro i _
  exact (measurable_probability hv hv1 (k i)).comp (hw i)

/-- The logarithmic loss of the product is exactly the sum of the scalar losses. -/
theorem neg_log_jointProbability {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (w : ι → ℝ) (k : ι → ℤ) :
    -Real.log (jointProbability v w k) = ∑ i, loss v (k i) (w i) := by
  unfold jointProbability loss
  rw [Real.log_prod (fun i _ => ne_of_gt (probability_pos hv hv1 (k i) (w i)))]
  rw [Finset.sum_neg_distrib]

end
end TheoremA2.PaddedDecoder
