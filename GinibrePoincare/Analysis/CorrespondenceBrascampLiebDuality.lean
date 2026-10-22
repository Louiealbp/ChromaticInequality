module
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.MetricSpace.Isometry
@[expose] public section
namespace GinibrePoincare
noncomputable section

/-- Hilbert-space duality used after the concrete Gibbs compact-generator
range has been proved dense in the centered subspace. -/
theorem correspondenceBrascampLieb_duality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : H) (D : Set H) (energy : ℝ) (henergy : 0 ≤ energy) (hu : u ∈ closure D)
    (hbound : ∀ v ∈ D, (inner ℝ u v)^2 ≤ energy * ‖v‖^2) :
    ‖u‖^2 ≤ energy := by
  let K : Set H := {v | (inner ℝ u v)^2 ≤ energy * ‖v‖^2}
  have hK : IsClosed K := by
    exact isClosed_le ((continuous_const.inner continuous_id).pow 2)
      (continuous_const.mul (continuous_norm.pow 2))
  have hDK : D ⊆ K := fun v hv => hbound v hv
  have hUK : u ∈ K := (closure_minimal hDK hK) hu
  change (inner ℝ u u)^2 ≤ energy * ‖u‖^2 at hUK
  rw [real_inner_self_eq_norm_sq] at hUK
  by_cases hz : ‖u‖^2 = 0
  · simpa [hz] using henergy
  · have hp : 0 < ‖u‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    nlinarith
#print axioms correspondenceBrascampLieb_duality
end
end GinibrePoincare
