import TheoremA2.DecoderProduct
import TheoremA2.GaussianShift
import TheoremA2.Parameters

set_option maxHeartbeats 800000

/-!
# The actual dependent-cell lattice-energy bound

The proof uses Gaussian change of measure and Jensen directly, which is the
variational form of the paper's entropy argument. The integer label vectors
are never assumed independent. Energies are infima over the literal feasible
pairs; infeasible cells have zero exponential weight.
-/

namespace TheoremA2.LatticeEnergy

open MeasureTheory ProbabilityTheory Set
open TheoremA2.GaussianShift TheoremA2.PaddedDecoder
open scoped Topology NNReal ENNReal BigOperators
noncomputable section

/-- The energy of an actual latent vector and within-period offset. -/
def pairEnergy {r d : ℕ} (kappa : ℝ) (z : Vector r) (x : Vector d) : ℝ :=
  (normSq z + kappa * normSq x) / 2

/-- The literal set of feasible energies in equation (42). -/
def feasibleEnergies {r d : ℕ} (b : Fin d → Vector r) (kappa : ℝ) (k : Fin d → ℤ) : Set ℝ :=
  {e | ∃ (z : Vector r) (x : Vector d),
    (∀ i, |x i| ≤ Real.pi / 2) ∧
    (∀ i, dot (b i) z = Real.pi * k i + x i) ∧ e = pairEnergy kappa z x}

/-- The energy infimum, with infinity for an infeasible cell. -/
def cellEnergy {r d : ℕ} (b : Fin d → Vector r) (kappa : ℝ) (k : Fin d → ℤ) : ℝ≥0∞ := by
  classical
  exact if (feasibleEnergies b kappa k).Nonempty then
    ENNReal.ofReal (sInf (feasibleEnergies b kappa k)) else ⊤

/-- The exponential of negative energy, with the paper's explicit `exp(-∞)=0` convention. -/
def cellWeight {r d : ℕ} (b : Fin d → Vector r) (kappa t : ℝ) (k : Fin d → ℤ) : ℝ := by
  classical
  exact if (feasibleEnergies b kappa k).Nonempty then
    Real.exp (-t * sInf (feasibleEnergies b kappa k)) else 0

/-- The exact error exponent in the lattice sum. -/
def entropyError (d : ℕ) (q : ℝ) : ℝ :=
  16 * (d : ℝ) * Real.exp (-((1 / 100000 : ℝ) * decoderBeta) / q)

/-- The product decoder likelihood as a function of the one common latent observation. -/
def likelihood {r d : ℕ} (v : ℝ) (b : Fin d → Vector r) (k : Fin d → ℤ)
    (y : Vector r) : ℝ := jointProbability v (fun i => dot (b i) y) k

theorem decoderBeta_pos : 0 < decoderBeta := by norm_num [decoderBeta]

theorem dot_add {r : ℕ} (b z y : Vector r) : dot b (z + y) = dot b z + dot b y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem measurable_dot {r : ℕ} (b : Vector r) : Measurable (dot b) := by
  rw [show dot b = ⇑(projection b) by funext y; exact (projection_apply b y).symm]
  exact (projection b).measurable

/-- Applying the scalar decoder to an actual projection of the product Gaussian law. -/
theorem projected_loss {r : ℕ} {beta v x : ℝ} (hb : 0 < beta) (hv : 0 < v)
    (hvsmall : v ≤ 1 / 1000000) (b : Vector r) (hvar : normSq b / beta ≤ v)
    (k : ℤ) (hx : |x| ≤ Real.pi / 2) :
    Integrable (fun y => loss v k (Real.pi * k + x + dot b y)) (gaussian r beta) ∧
      (∫ y, loss v k (Real.pi * k + x + dot b y) ∂gaussian r beta) ≤
        (27 / 80 : ℝ) * x ^ 2 + 16 * Real.exp (-(1 / 100000 : ℝ) / v) := by
  let w : ℝ≥0 := (normSq b / beta).toNNReal
  have hw : (w : ℝ) ≤ v := by
    simpa only [w, Real.coe_toNNReal _ (div_nonneg (normSq_nonneg b) hb.le)] using hvar
  let f : ℝ → ℝ := fun n => loss v k (Real.pi * k + x + n)
  have hfi : Integrable f ((gaussian r beta).map (dot b)) := by
    rw [map_dot hb]
    exact integrable_loss_gaussian hv hvsmall w hw k hx
  have hi := hfi.comp_measurable (measurable_dot b)
  refine ⟨hi, ?_⟩
  have heq : (∫ y, f (dot b y) ∂gaussian r beta) = ∫ n, f n ∂gaussianReal 0 w := by
    rw [← integral_map (measurable_dot b).aemeasurable hfi.aestronglyMeasurable, map_dot hb]
  change (∫ y, f (dot b y) ∂gaussian r beta) ≤ _
  rw [heq]
  exact expected_loss_gaussian hv hvsmall w hw k hx

theorem likelihood_measurable {r d : ℕ} {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (b : Fin d → Vector r) (k : Fin d → ℤ) : Measurable (likelihood v b k) := by
  exact measurable_jointProbability hv hv1 (fun y i => dot (b i) y)
    (fun i => measurable_dot (b i)) k

theorem likelihood_pos {r d : ℕ} {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (b : Fin d → Vector r) (k : Fin d → ℤ) (y : Vector r) : 0 < likelihood v b k y :=
  jointProbability_pos hv hv1 _ _

theorem likelihood_le_one {r d : ℕ} {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (b : Fin d → Vector r) (k : Fin d → ℤ) (y : Vector r) : likelihood v b k y ≤ 1 :=
  jointProbability_le_one hv hv1 _ _

/-- The expected joint logarithmic loss is bounded by summing actual one-dimensional
projection losses. Correlations between projections are retained throughout. -/
theorem shifted_log_likelihood {r d : ℕ} {q : ℝ} (hq : 0 < q)
    (hcut : q / decoderBeta ≤ 1 / 1000000) (b : Fin d → Vector r)
    (hb : ∀ i, normSq (b i) ≤ q) (k : Fin d → ℤ)
    (z : Vector r) (x : Vector d) (hx : ∀ i, |x i| ≤ Real.pi / 2)
    (hcell : ∀ i, dot (b i) z = Real.pi * k i + x i) :
    Integrable (fun y => Real.log (likelihood (q / decoderBeta) b k (z + y)))
      (gaussian r decoderBeta) ∧
      -(∫ y, Real.log (likelihood (q / decoderBeta) b k (z + y)) ∂gaussian r decoderBeta) ≤
        (27 / 80 : ℝ) * normSq x + entropyError d q := by
  have hv : 0 < q / decoderBeta := div_pos hq decoderBeta_pos
  have hv1 : q / decoderBeta ≤ 1 := by linarith
  have hproject (i : Fin d) := projected_loss decoderBeta_pos hv hcut (b i)
    (div_le_div_of_nonneg_right (hb i) decoderBeta_pos.le) (k i) (hx i)
  have hsum : Integrable (fun y => ∑ i, loss (q / decoderBeta) (k i)
      (Real.pi * k i + x i + dot (b i) y)) (gaussian r decoderBeta) :=
    integrable_finsetSum _ fun i _ => (hproject i).1
  have hid : (fun y => Real.log (likelihood (q / decoderBeta) b k (z + y))) =
      (fun y => -(∑ i, loss (q / decoderBeta) (k i)
        (Real.pi * k i + x i + dot (b i) y))) := by
    funext y
    have hh := neg_log_jointProbability hv hv1 (fun i => dot (b i) (z + y)) k
    change -Real.log (likelihood (q / decoderBeta) b k (z + y)) = _ at hh
    simp only [dot_add, hcell] at hh
    linarith
  refine ⟨by rw [hid]; exact hsum.neg, ?_⟩
  rw [hid, integral_neg, neg_neg,
    integral_finsetSum _ (fun i _ => (hproject i).1)]
  calc
    (∑ i, ∫ y, loss (q / decoderBeta) (k i)
        (Real.pi * k i + x i + dot (b i) y) ∂gaussian r decoderBeta) ≤
        ∑ i : Fin d, ((27 / 80 : ℝ) * x i ^ 2 +
          16 * Real.exp (-(1 / 100000 : ℝ) / (q / decoderBeta))) :=
      Finset.sum_le_sum fun i _ => (hproject i).2
    _ = (27 / 80 : ℝ) * normSq x + entropyError d q := by
      have he : -(1 / 100000 : ℝ) / (q / decoderBeta) =
          -((1 / 100000 : ℝ) * decoderBeta) / q := by
        field_simp
      rw [he]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, normSq, entropyError]
      ring

/-- For every genuinely feasible pair, Gaussian change of measure bounds its Boltzmann
weight by the integrated actual decoder likelihood. -/
theorem feasible_pair_bound {r d : ℕ} {q kappa : ℝ} (hq : 0 < q)
    (hcut : q / decoderBeta ≤ 1 / 1000000) (hkappa : 3 / 4 ≤ kappa)
    (b : Fin d → Vector r) (hb : ∀ i, normSq (b i) ≤ q) (k : Fin d → ℤ)
    (z : Vector r) (x : Vector d) (hx : ∀ i, |x i| ≤ Real.pi / 2)
    (hcell : ∀ i, dot (b i) z = Real.pi * k i + x i) :
    Real.exp (-decoderBeta * pairEnergy kappa z x - entropyError d q) ≤
      ∫ y, likelihood (q / decoderBeta) b k y ∂gaussian r decoderBeta := by
  have hv : 0 < q / decoderBeta := div_pos hq decoderBeta_pos
  have hv1 : q / decoderBeta ≤ 1 := by linarith
  have hlog := shifted_log_likelihood hq hcut b hb k z x hx hcell
  have hh := variational_bound decoderBeta_pos z
    (likelihood_measurable hv hv1 b k) (likelihood_pos hv hv1 b k)
    (likelihood_le_one hv hv1 b k) hlog.1 hlog.2
  apply le_trans _ hh
  apply Real.exp_le_exp.2
  unfold pairEnergy decoderBeta
  have hnorm := normSq_nonneg x
  nlinarith [mul_le_mul_of_nonneg_right hkappa hnorm]

/-- Feasible energies are bounded below by zero under the actual penalty hypothesis. -/
theorem feasible_energy_nonneg {r d : ℕ} {b : Fin d → Vector r} {kappa e : ℝ}
    (hkappa : 0 ≤ kappa) {k : Fin d → ℤ} (he : e ∈ feasibleEnergies b kappa k) :
    0 ≤ e := by
  rcases he with ⟨z, x, _, _, rfl⟩
  exact div_nonneg (add_nonneg (normSq_nonneg z)
    (mul_nonneg hkappa (normSq_nonneg x))) (by norm_num)

theorem feasibleEnergies_bddBelow {r d : ℕ} {b : Fin d → Vector r} {kappa : ℝ}
    (hkappa : 0 ≤ kappa) (k : Fin d → ℤ) : BddBelow (feasibleEnergies b kappa k) :=
  ⟨0, fun _ he => feasible_energy_nonneg hkappa he⟩

theorem cellWeight_nonneg {r d : ℕ} (b : Fin d → Vector r) (kappa t : ℝ)
    (k : Fin d → ℤ) : 0 ≤ cellWeight b kappa t k := by
  classical
  unfold cellWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · rfl

/-- The displayed weight is exactly the exponential of the extended nonnegative energy,
with zero at infinity, rather than a surrogate energy or a feasible witness. -/
theorem cellWeight_eq_exp_neg_energy {r d : ℕ} (b : Fin d → Vector r)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (t : ℝ) (k : Fin d → ℤ) :
    cellWeight b kappa t k =
      if cellEnergy b kappa k = ⊤ then 0 else Real.exp (-t * (cellEnergy b kappa k).toReal) := by
  classical
  by_cases hne : (feasibleEnergies b kappa k).Nonempty
  · have hinf : 0 ≤ sInf (feasibleEnergies b kappa k) :=
      le_csInf hne (fun _ he => feasible_energy_nonneg hkappa he)
    simp only [cellWeight, cellEnergy, hne, ite_true, ENNReal.ofReal_ne_top, ite_false,
      ENNReal.toReal_ofReal hinf]
  · simp [cellWeight, cellEnergy, hne]

/-- Each likelihood is integrable under the actual Gaussian reference. -/
theorem integrable_likelihood {r d : ℕ} {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (b : Fin d → Vector r) (k : Fin d → ℤ) :
    Integrable (likelihood v b k) (gaussian r decoderBeta) := by
  apply (integrable_const (1 : ℝ)).mono' (likelihood_measurable hv hv1 b k).aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_pos (likelihood_pos hv hv1 b k y)]
  exact likelihood_le_one hv hv1 b k y

/-- Pass the proved feasible-pair bound to the literal energy infimum.
Taking logarithms gives a common energy lower bound, so no minimizer is assumed. -/
theorem cellWeight_le_integrated_likelihood {r d : ℕ} {q kappa : ℝ} (hq : 0 < q)
    (hcut : q / decoderBeta ≤ 1 / 1000000) (hkappa : 3 / 4 ≤ kappa)
    (b : Fin d → Vector r) (hb : ∀ i, normSq (b i) ≤ q) (k : Fin d → ℤ) :
    cellWeight b kappa decoderBeta k ≤ Real.exp (entropyError d q) *
      ∫ y, likelihood (q / decoderBeta) b k y ∂gaussian r decoderBeta := by
  classical
  have hv : 0 < q / decoderBeta := div_pos hq decoderBeta_pos
  have hv1 : q / decoderBeta ≤ 1 := by linarith
  by_cases hne : (feasibleEnergies b kappa k).Nonempty
  · obtain ⟨e0, z0, x0, hx0, hcell0, rfl⟩ := hne
    have hpos : 0 < ∫ y, likelihood (q / decoderBeta) b k y ∂gaussian r decoderBeta :=
      lt_of_lt_of_le (Real.exp_pos _)
        (feasible_pair_bound hq hcut hkappa b hb k z0 x0 hx0 hcell0)
    have hne' : (feasibleEnergies b kappa k).Nonempty :=
      ⟨pairEnergy kappa z0 x0, z0, x0, hx0, hcell0, rfl⟩
    have hinf :
        -(Real.log (∫ y, likelihood (q / decoderBeta) b k y ∂gaussian r decoderBeta) +
          entropyError d q) / decoderBeta ≤ sInf (feasibleEnergies b kappa k) := by
      apply le_csInf hne'
      intro e he
      rcases he with ⟨z, x, hx, hcell, rfl⟩
      have hlog := (Real.le_log_iff_exp_le hpos).2
        (feasible_pair_bound hq hcut hkappa b hb k z x hx hcell)
      apply (div_le_iff₀ decoderBeta_pos).2
      linarith
    have hexp : Real.exp (-decoderBeta * sInf (feasibleEnergies b kappa k) - entropyError d q) ≤
        ∫ y, likelihood (q / decoderBeta) b k y ∂gaussian r decoderBeta := by
      apply (Real.le_log_iff_exp_le hpos).1
      have hh := (div_le_iff₀ decoderBeta_pos).1 hinf
      nlinarith
    rw [cellWeight, if_pos hne']
    calc
      Real.exp (-decoderBeta * sInf (feasibleEnergies b kappa k)) =
          Real.exp (entropyError d q) *
            Real.exp (-decoderBeta * sInf (feasibleEnergies b kappa k) - entropyError d q) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
  · rw [cellWeight, if_neg hne]
    have hi : 0 ≤ ∫ y, likelihood (q / decoderBeta) b k y ∂gaussian r decoderBeta :=
      integral_nonneg fun y => (likelihood_pos hv hv1 b k y).le
    exact mul_nonneg (Real.exp_pos _).le hi

/-- Every finite collection of cells satisfies the actual lattice sum bound. -/
theorem finite_lattice_sum {r d : ℕ} {q kappa : ℝ} (hq : 0 < q)
    (hcut : q / decoderBeta ≤ 1 / 1000000) (hkappa : 3 / 4 ≤ kappa)
    (b : Fin d → Vector r) (hb : ∀ i, normSq (b i) ≤ q) (J : Finset (Fin d → ℤ)) :
    ∑ k ∈ J, cellWeight b kappa decoderBeta k ≤ Real.exp (entropyError d q) := by
  have hv : 0 < q / decoderBeta := div_pos hq decoderBeta_pos
  have hv1 : q / decoderBeta ≤ 1 := by linarith
  have hsum : Integrable (fun y => ∑ k ∈ J, likelihood (q / decoderBeta) b k y)
      (gaussian r decoderBeta) :=
    integrable_finsetSum _ fun k _ => integrable_likelihood hv hv1 b k
  have hmass : (∫ y, ∑ k ∈ J, likelihood (q / decoderBeta) b k y ∂gaussian r decoderBeta) ≤ 1 := by
    have hh := integral_mono hsum (integrable_const (1 : ℝ))
      (fun y => sum_jointProbability_le_one hv hv1 (fun i => dot (b i) y) J)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  calc
    (∑ k ∈ J, cellWeight b kappa decoderBeta k) ≤
        ∑ k ∈ J, Real.exp (entropyError d q) *
          ∫ y, likelihood (q / decoderBeta) b k y ∂gaussian r decoderBeta :=
      Finset.sum_le_sum fun k _ => cellWeight_le_integrated_likelihood hq hcut hkappa b hb k
    _ = Real.exp (entropyError d q) *
        ∫ y, ∑ k ∈ J, likelihood (q / decoderBeta) b k y ∂gaussian r decoderBeta := by
      rw [← Finset.mul_sum,
        integral_finsetSum _ (fun k _ => integrable_likelihood hv hv1 b k)]
    _ ≤ Real.exp (entropyError d q) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le

/-- Equation (42), summed over every integer cell and allowing all dependent observations. -/
theorem lattice_sum {r d : ℕ} {q kappa : ℝ} (hq : 0 < q)
    (hcut : q / decoderBeta ≤ 1 / 1000000) (hkappa : 3 / 4 ≤ kappa)
    (b : Fin d → Vector r) (hb : ∀ i, normSq (b i) ≤ q) :
    Summable (cellWeight b kappa decoderBeta) ∧
      (∑' k : Fin d → ℤ, cellWeight b kappa decoderBeta k) ≤ Real.exp (entropyError d q) := by
  have hJ := finite_lattice_sum hq hcut hkappa b hb
  have hs := summable_of_sum_le (fun k => cellWeight_nonneg b kappa decoderBeta k) hJ
  exact ⟨hs, hs.tsum_le_of_sum_le hJ⟩

/-- The central cell has exactly zero energy, with the actual zero-vector witness. -/
theorem central_energy_zero {r d : ℕ} (b : Fin d → Vector r)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) : cellEnergy b kappa 0 = 0 := by
  have hzero : (0 : ℝ) ∈ feasibleEnergies b kappa 0 := by
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · intro i
      simp only [Pi.zero_apply, abs_zero]
      positivity
    · intro i
      simp [dot]
    · simp [pairEnergy, normSq]
  have hne : (feasibleEnergies b kappa 0).Nonempty := ⟨0, hzero⟩
  have hinf : sInf (feasibleEnergies b kappa 0) = 0 := by
    apply le_antisymm (csInf_le (feasibleEnergies_bddBelow hkappa 0) hzero)
    exact le_csInf hne (fun _ he => feasible_energy_nonneg hkappa he)
  simp [cellEnergy, hne, hinf]

theorem central_weight_one {r d : ℕ} (b : Fin d → Vector r)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (t : ℝ) : cellWeight b kappa t 0 = 1 := by
  rw [cellWeight_eq_exp_neg_energy b hkappa t 0, central_energy_zero b hkappa]
  simp

/-- Every feasible noncentral cell pays the exact quadratic energy gap. -/
theorem noncentral_pair_energy_gap {r d : ℕ} {q kappa : ℝ} (hq : 0 < q)
    (hkappa : 0 ≤ kappa) (b : Fin d → Vector r) (hb : ∀ i, normSq (b i) ≤ q)
    (k : Fin d → ℤ) (hk : k ≠ 0) (z : Vector r) (x : Vector d)
    (hx : ∀ i, |x i| ≤ Real.pi / 2)
    (hcell : ∀ i, dot (b i) z = Real.pi * k i + x i) :
    Real.pi ^ 2 / (8 * q) ≤ pairEnergy kappa z x := by
  have hcoord : ∃ i, k i ≠ 0 := by
    by_contra! h
    apply hk
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  have hki : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
  have hperiod : Real.pi ≤ |Real.pi * (k i : ℝ)| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have htri := abs_sub (dot (b i) z) (x i)
  have hid : dot (b i) z - x i = Real.pi * (k i : ℝ) := by rw [hcell i]; ring
  rw [hid] at htri
  have hprojection : Real.pi / 2 ≤ |dot (b i) z| := by linarith [hx i]
  have hprojSq := pow_le_pow_left₀ (by positivity : 0 ≤ Real.pi / 2) hprojection 2
  rw [sq_abs] at hprojSq
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (b i) z
  change dot (b i) z ^ 2 ≤ normSq (b i) * normSq z at hcauchy
  have hnorm := mul_le_mul_of_nonneg_right (hb i) (normSq_nonneg z)
  have hlatent : Real.pi ^ 2 / (8 * q) ≤ normSq z / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * q)).2
    nlinarith
  exact hlatent.trans (by
    unfold pairEnergy
    linarith [mul_nonneg hkappa (normSq_nonneg x)])

/-- The same lower gap holds at the actual infimum, even without selecting a minimizer. -/
theorem noncentral_energy_inf_gap {r d : ℕ} {q kappa : ℝ} (hq : 0 < q)
    (hkappa : 0 ≤ kappa) (b : Fin d → Vector r) (hb : ∀ i, normSq (b i) ≤ q)
    (k : Fin d → ℤ) (hk : k ≠ 0) (hne : (feasibleEnergies b kappa k).Nonempty) :
    Real.pi ^ 2 / (8 * q) ≤ sInf (feasibleEnergies b kappa k) := by
  apply le_csInf hne
  intro e he
  rcases he with ⟨z, x, hx, hcell, rfl⟩
  exact noncentral_pair_energy_gap hq hkappa b hb k hk z x hx hcell

/-- Removing the central cell gains the exact factor `exp(-π²/(80q))`. -/
theorem noncentral_weight_factor {r d : ℕ} {q kappa : ℝ} (hq : 0 < q)
    (hkappa : 0 ≤ kappa) (b : Fin d → Vector r) (hb : ∀ i, normSq (b i) ≤ q)
    (k : Fin d → ℤ) (hk : k ≠ 0) :
    cellWeight b kappa 1 k ≤ Real.exp (-(Real.pi ^ 2) / (80 * q)) *
      cellWeight b kappa decoderBeta k := by
  classical
  by_cases hne : (feasibleEnergies b kappa k).Nonempty
  · have hgap := noncentral_energy_inf_gap hq hkappa b hb k hk hne
    have hsmall : Real.pi ^ 2 / (80 * q) ≤
        (1 / 10 : ℝ) * sInf (feasibleEnergies b kappa k) := by
      calc
        Real.pi ^ 2 / (80 * q) = (1 / 10 : ℝ) * (Real.pi ^ 2 / (8 * q)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by norm_num)
    have he : Real.exp (-(1 - decoderBeta) * sInf (feasibleEnergies b kappa k)) ≤
        Real.exp (-(Real.pi ^ 2) / (80 * q)) := by
      apply Real.exp_le_exp.2
      calc
        -(1 - decoderBeta) * sInf (feasibleEnergies b kappa k) =
            -((1 / 10 : ℝ) * sInf (feasibleEnergies b kappa k)) := by
          norm_num [decoderBeta]
        _ ≤ -(Real.pi ^ 2 / (80 * q)) := neg_le_neg hsmall
        _ = -(Real.pi ^ 2) / (80 * q) := by ring
    simp only [cellWeight, hne, ite_true]
    calc
      Real.exp (-1 * sInf (feasibleEnergies b kappa k)) =
          Real.exp (-(1 - decoderBeta) * sInf (feasibleEnergies b kappa k)) *
            Real.exp (-decoderBeta * sInf (feasibleEnergies b kappa k)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
  · simp [cellWeight, hne]

/-- Equation (43) for every finite collection of noncentral cells. -/
theorem finite_noncentral_lattice_sum {r d : ℕ} {q kappa : ℝ} (hq : 0 < q)
    (hcut : q / decoderBeta ≤ 1 / 1000000) (hkappa : 3 / 4 ≤ kappa)
    (b : Fin d → Vector r) (hb : ∀ i, normSq (b i) ≤ q)
    (J : Finset (Fin d → ℤ)) (hJ : ∀ k ∈ J, k ≠ 0) :
    ∑ k ∈ J, cellWeight b kappa 1 k ≤ latticeError d q := by
  have hk0 : 0 ≤ kappa := by linarith
  calc
    (∑ k ∈ J, cellWeight b kappa 1 k) ≤
        ∑ k ∈ J, Real.exp (-(Real.pi ^ 2) / (80 * q)) * cellWeight b kappa decoderBeta k :=
      Finset.sum_le_sum fun k hk => noncentral_weight_factor hq hk0 b hb k (hJ k hk)
    _ = Real.exp (-(Real.pi ^ 2) / (80 * q)) * ∑ k ∈ J, cellWeight b kappa decoderBeta k := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-(Real.pi ^ 2) / (80 * q)) * Real.exp (entropyError d q) :=
      mul_le_mul_of_nonneg_left (finite_lattice_sum hq hcut hkappa b hb J) (Real.exp_pos _).le
    _ = latticeError d q := by
      rw [← Real.exp_add]
      rfl

/-- Equation (43), genuinely summed over every nonzero integer cell. -/
theorem noncentral_lattice_sum {r d : ℕ} {q kappa : ℝ} (hq : 0 < q)
    (hcut : q / decoderBeta ≤ 1 / 1000000) (hkappa : 3 / 4 ≤ kappa)
    (b : Fin d → Vector r) (hb : ∀ i, normSq (b i) ≤ q) :
    Summable (fun k : {k : Fin d → ℤ // k ≠ 0} => cellWeight b kappa 1 k) ∧
      (∑' k : {k : Fin d → ℤ // k ≠ 0}, cellWeight b kappa 1 k) ≤ latticeError d q := by
  classical
  have h0 (k : {k : Fin d → ℤ // k ≠ 0}) := cellWeight_nonneg b kappa 1 k.val
  have hJ (J : Finset {k : Fin d → ℤ // k ≠ 0}) :
      ∑ k ∈ J, cellWeight b kappa 1 k.val ≤ latticeError d q := by
    have hh := finite_noncentral_lattice_sum hq hcut hkappa b hb (J.image Subtype.val)
      (by intro k hk; obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hk; exact j.property)
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at hh
    exact hh
  have hs := summable_of_sum_le h0 hJ
  exact ⟨hs, hs.tsum_le_of_sum_le hJ⟩

end
end TheoremA2.LatticeEnergy
